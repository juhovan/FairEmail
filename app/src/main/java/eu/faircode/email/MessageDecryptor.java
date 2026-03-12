package eu.faircode.email;

/*
    This file is part of FairEmail.

    FairEmail is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    FairEmail is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FairEmail.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2018-2025 by Marcel Bokhorst (M66B)
*/

import static org.openintents.openpgp.OpenPgpSignatureResult.RESULT_KEY_MISSING;
import static org.openintents.openpgp.OpenPgpSignatureResult.RESULT_NO_SIGNATURE;
import static org.openintents.openpgp.OpenPgpSignatureResult.RESULT_VALID_KEY_CONFIRMED;
import static org.openintents.openpgp.OpenPgpSignatureResult.RESULT_VALID_KEY_UNCONFIRMED;

import android.app.PendingIntent;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.text.SpannableStringBuilder;
import android.text.TextUtils;
import android.util.Base64;

import androidx.preference.PreferenceManager;

import org.openintents.openpgp.AutocryptPeerUpdate;
import org.openintents.openpgp.OpenPgpError;
import org.openintents.openpgp.OpenPgpSignatureResult;
import org.openintents.openpgp.util.OpenPgpApi;

import java.io.BufferedInputStream;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;

import javax.mail.Session;
import javax.mail.internet.MimeMessage;
import javax.mail.internet.InternetAddress;

class MessageDecryptor {
    static final class Result {
        final boolean decrypted;
        final PendingIntent pendingIntent;
        final String signatureResult;
        final boolean retryStrip;
        final boolean skipped;

        private Result(boolean decrypted, PendingIntent pendingIntent, String signatureResult, boolean retryStrip, boolean skipped) {
            this.decrypted = decrypted;
            this.pendingIntent = pendingIntent;
            this.signatureResult = signatureResult;
            this.retryStrip = retryStrip;
            this.skipped = skipped;
        }

        static Result success(boolean decrypted, String signatureResult) {
            return new Result(decrypted, null, signatureResult, false, false);
        }

        static Result interaction(PendingIntent pendingIntent) {
            return new Result(false, pendingIntent, null, false, false);
        }

        static Result retryStrip() {
            return new Result(false, null, null, true, false);
        }

        static Result skip() {
            return new Result(false, null, null, false, true);
        }
    }

    private MessageDecryptor() {
    }

    static Result decrypt(Context context, Intent data, boolean auto, boolean stripped) throws Throwable {
        long id = data.getLongExtra(BuildConfig.APPLICATION_ID, -1);

        DB db = DB.getInstance(context);
        EntityMessage message = db.message().getMessage(id);
        if (message == null)
            return Result.skip();
        List<EntityAttachment> attachments = db.attachment().getAttachments(message.id);
        if (attachments == null)
            return Result.skip();

        if (auto && message.revision != null)
            return Result.skip();

        InputStream in = null;
        OutputStream out = null;
        boolean inline = false;

        File tmp = Helper.ensureExists(context, "encryption");
        File plain = new File(tmp, message.id + ".pgp_out");

        // Find encrypted data
        for (EntityAttachment attachment : attachments)
            if (EntityAttachment.PGP_CONTENT.equals(attachment.encryption) ||
                    EntityAttachment.PGP_MESSAGE.equals(attachment.encryption)) {
                if (!attachment.available)
                    if (auto)
                        return Result.skip();
                    else
                        throw new IllegalArgumentException(context.getString(R.string.title_attachments_missing));

                File file = attachment.getFile(context);
                Log.i("PGP in=" + file.getAbsolutePath() + " exist=" + file.exists() + "/" + file.length());
                in = new FileInputStream(file);

                if (EntityAttachment.PGP_MESSAGE.equals(attachment.encryption)) {
                    Log.i("PGP out=" + plain.getAbsolutePath());
                    out = new FileOutputStream(plain);
                }

            } else if (EntityAttachment.PGP_SIGNATURE.equals(attachment.encryption)) {
                if (!attachment.available)
                    throw new IllegalArgumentException(context.getString(R.string.title_attachments_missing));

                File file = attachment.getFile(context);
                byte[] signature = new byte[(int) file.length()];
                try (FileInputStream fis = new FileInputStream(file)) {
                    fis.read(signature);
                }
                data.putExtra(OpenPgpApi.EXTRA_DETACHED_SIGNATURE, signature);
            }

        if (in == null) {
            if (message.content) {
                File file = message.getFile(context);
                if (file.exists()) {
                    String html = Helper.readText(file);
                    String body = HtmlHelper.fromHtml(html, context).toString();
                    int begin = body.indexOf(Helper.PGP_BEGIN_MESSAGE);
                    int end = body.indexOf(Helper.PGP_END_MESSAGE);
                    if (begin >= 0 && begin < end) {
                        String[] lines = body
                                .substring(begin, end + Helper.PGP_END_MESSAGE.length())
                                .split("\\r?\\n");

                        List<String> disarmored = new ArrayList<>();
                        for (String line : lines)
                            if (!TextUtils.isEmpty(line) && !line.contains(": "))
                                disarmored.add(line);

                        String pgpMessage = TextUtils.join("\n\r", disarmored);

                        inline = true;
                        Log.i("PGP inline");
                        in = new ByteArrayInputStream(pgpMessage.getBytes());
                        out = new FileOutputStream(plain);
                    }
                }
            }
        }

        if (in == null)
            if (auto)
                return Result.skip();
            else
                throw new IllegalArgumentException(context.getString(R.string.title_not_encrypted));

        if (stripped)
            in = new MessageHelper.StripStream(new BufferedInputStream(in));

        SharedPreferences prefs = PreferenceManager.getDefaultSharedPreferences(context);
        boolean autocrypt = prefs.getBoolean("autocrypt", true);
        if (autocrypt &&
                message.from != null && message.from.length > 0 &&
                message.autocrypt != null &&
                OpenPgpApi.ACTION_DECRYPT_VERIFY.equals(data.getAction()))
            try {
                String peer = ((InternetAddress) message.from[0]).getAddress();
                String addr = null;
                boolean mutual = false;
                byte[] keydata = null;

                Map<String, String> kv = MessageHelper.getKeyValues(message.autocrypt);
                for (String key : kv.keySet()) {
                    String value = kv.get(key);
                    Log.i("Autocrypt " + key + "=" + value);
                    if (value == null)
                        continue;
                    switch (key) {
                        case "addr":
                            addr = value;
                            break;
                        case "prefer-encrypt":
                            mutual = value.trim().toLowerCase(Locale.ROOT).equals("mutual");
                            break;
                        case "keydata":
                            keydata = Base64.decode(value, Base64.DEFAULT);
                            break;
                    }
                }

                if (addr == null)
                    throw new IllegalArgumentException("Autocrypt: addr not found");

                if (!addr.equalsIgnoreCase(peer))
                    throw new IllegalArgumentException("Autocrypt: addr different from peer");

                if (keydata == null)
                    throw new IllegalArgumentException("Autocrypt: keydata not found");

                AutocryptPeerUpdate update = AutocryptPeerUpdate.create(
                        keydata, new Date(message.received), mutual);

                data.putExtra(OpenPgpApi.EXTRA_AUTOCRYPT_PEER_ID, addr);
                data.putExtra(OpenPgpApi.EXTRA_AUTOCRYPT_PEER_UPDATE, update);
            } catch (Throwable ex) {
                Log.w(ex);
            }

        Intent result;
        String signatureInfo = null;
        boolean decrypted = false;
        Integer encryptResult = null;
        try {
            result = PgpHelper.execute(context, data, in, out);
            int resultCode = result.getIntExtra(OpenPgpApi.RESULT_CODE, OpenPgpApi.RESULT_CODE_ERROR);
            switch (resultCode) {
                case OpenPgpApi.RESULT_CODE_SUCCESS:
                    if (out != null) {
                        ContentResult content = handleSuccess(context, prefs, db, message, plain, inline, auto);
                        decrypted = content.decrypted;
                        encryptResult = content.encrypt;
                    }

                    OpenPgpSignatureResult sigResult = result.getParcelableExtra(OpenPgpApi.RESULT_SIGNATURE);
                    int sresult = (sigResult == null ? RESULT_NO_SIGNATURE : sigResult.getResult());
                    if (sigResult == null)
                        Log.w("PGP signature result missing");
                    else
                        Log.i("PGP signature result=" + sresult);

                    if (sresult == RESULT_NO_SIGNATURE) {
                        if (!EntityAttachment.PGP_SIGNATURE.equals(encryptResult))
                            signatureInfo = context.getString(R.string.title_signature_none);
                    } else if (sresult == RESULT_VALID_KEY_CONFIRMED || sresult == RESULT_VALID_KEY_UNCONFIRMED) {
                        List<String> users = sigResult.getConfirmedUserIds();
                        if (users.size() > 0)
                            signatureInfo = context.getString(sresult == RESULT_VALID_KEY_UNCONFIRMED
                                            ? R.string.title_signature_unconfirmed_from
                                            : R.string.title_signature_valid_from,
                                    TextUtils.join(", ", users));
                        else
                            signatureInfo = context.getString(sresult == RESULT_VALID_KEY_UNCONFIRMED
                                    ? R.string.title_signature_unconfirmed
                                    : R.string.title_signature_valid);
                        if (sresult == RESULT_VALID_KEY_CONFIRMED)
                            db.message().setMessageVerified(message.id, true);
                    } else if (sresult == RESULT_KEY_MISSING)
                        signatureInfo = context.getString(R.string.title_signature_key_missing);
                    else {
                        if (stripped)
                            signatureInfo = context.getString(R.string.title_signature_invalid_reason, Integer.toString(sresult));
                        else
                            return Result.retryStrip();
                    }

                    break;

                case OpenPgpApi.RESULT_CODE_USER_INTERACTION_REQUIRED:
                    if (auto)
                        return Result.skip();
                    PendingIntent pi = result.getParcelableExtra(OpenPgpApi.RESULT_INTENT);
                    return Result.interaction(pi);

                case OpenPgpApi.RESULT_CODE_ERROR:
                    OpenPgpError error = result.getParcelableExtra(OpenPgpApi.RESULT_ERROR);
                    throw new IllegalArgumentException(
                            "OpenPgp" +
                                    " error " + (error == null ? "?" : error.getErrorId()) +
                                    ": " + (error == null ? "?" : error.getMessage()));

                default:
                    throw new IllegalStateException("OpenPgp unknown result code=" + resultCode);
            }
        } finally {
            Helper.secureDelete(plain);
        }

        return Result.success(decrypted, signatureInfo);
    }

    private static ContentResult handleSuccess(Context context, SharedPreferences prefs, DB db, EntityMessage message, File plain, boolean inline, boolean auto) throws Throwable {
        if (inline) {
            try {
                db.beginTransaction();

                String text = Helper.readText(plain);
                String html = "<div x-plain=\"true\">" + HtmlHelper.formatPlainText(text) + "</div>";
                Helper.writeText(message.getFile(context), html);
                db.message().setMessageRevision(message.id, 1);
                db.message().setMessageStored(message.id, new Date().getTime());
                db.message().setMessageFts(message.id, false);

                db.setTransactionSuccessful();
            } finally {
                db.endTransaction();
            }

            WorkerFts.init(context, false);
            return new ContentResult(true, null);
        }

        MessageHelper.MessageParts parts;
        Properties props = MessageHelper.getSessionProperties(true);
        Session isession = Session.getInstance(props, null);
        MimeMessage imessage;
        try (InputStream fis = new FileInputStream(plain)) {
            imessage = new MimeMessage(isession, fis);
        }

        MessageHelper helper = new MessageHelper(imessage, context);
        parts = helper.getMessageParts();
        String protect_subject = parts.getProtectedSubject();
        Integer encrypt = parts.getEncryption();

        boolean debug = prefs.getBoolean("debug", false);
        boolean download_plain = prefs.getBoolean("download_plain", false);
        String html = parts.getHtml(context, download_plain);

        if (html == null && debug) {
            int textColorLink = Helper.resolveColor(context, android.R.attr.textColorLink);
            SpannableStringBuilder ssb = new SpannableStringBuilderEx();
            MessageHelper.getStructure(imessage, ssb, 0, textColorLink);
            html = HtmlHelper.toHtml(ssb, context);
        }

        File messageFile = message.getFile(context);
        Helper.writeText(messageFile, html);
        Log.i("pgp html=" + (html == null ? null : html.length()) +
            " file=" + messageFile.getName() + " bytes=" + messageFile.length());

        String text = HtmlHelper.getFullText(context, html);
        message.preview = HtmlHelper.getPreview(text);
        message.language = HtmlHelper.getLanguage(context, message.subject, text);
        Log.i("pgp text=" + (text == null ? null : text.length()) +
            " preview=" + (message.preview == null ? null : message.preview.length()) +
            " language=" + message.language);

        try {
            db.beginTransaction();

            if (protect_subject != null)
                db.message().setMessageSubject(message.id, protect_subject);

            db.message().setMessageContent(message.id,
                    true,
                    message.language,
                    parts.isPlainOnly(download_plain),
                    message.preview,
                    message.warning);

            db.attachment().deleteAttachments(message.id, new int[]{EntityAttachment.PGP_MESSAGE});

            List<EntityAttachment> remotes = parts.getAttachments();
            for (int index = 0; index < remotes.size(); index++) {
                EntityAttachment remote = remotes.get(index);
                remote.message = message.id;
                remote.sequence = index + 1;
                remote.id = db.attachment().insertAttachment(remote);
                try {
                    parts.downloadAttachment(context, index, remote, null);
                } catch (Throwable ex) {
                    Log.e(ex);
                }
            }

            db.message().setMessageEncrypt(message.id, encrypt);
            db.message().setMessageRevision(message.id, protect_subject == null ? 1 : -1);
            db.message().setMessageStored(message.id, new Date().getTime());
            db.message().setMessageFts(message.id, false);

            if (BuildConfig.DEBUG || debug) {
                File raw = message.getRawFile(context);
                Helper.copy(plain, raw);
                db.message().setMessageRaw(message.id, true);
            }

            db.setTransactionSuccessful();
        } catch (android.database.sqlite.SQLiteConstraintException ex) {
            Log.w(ex);
        } finally {
            db.endTransaction();
        }

        if (!auto)
            try {
                List<EntityRule> rules = db.rule().getEnabledRules(message.folder, false);
                if (rules != null && rules.size() > 0) {
                    List<EntityRule> bodyRules = new ArrayList<>();
                    for (EntityRule rule : rules)
                        if (EntityRule.needsBody(rule))
                            bodyRules.add(rule);

                    if (bodyRules.size() > 0) {
                        EntityMessage refreshed = db.message().getMessage(message.id);
                        if (refreshed != null) {
                            EntityLog.log(context, EntityLog.Type.Rules, refreshed,
                                    "Running body rules after decrypt count=" + bodyRules.size());
                            EntityRule.run(context, bodyRules, refreshed, false, null, html);
                        }
                    }
                }
            } catch (Throwable ex) {
                Log.e(ex);
            }

        WorkerFts.init(context, false);
        return new ContentResult(true, encrypt);
    }

    private static class ContentResult {
        final boolean decrypted;
        final Integer encrypt;

        ContentResult(boolean decrypted, Integer encrypt) {
            this.decrypted = decrypted;
            this.encrypt = encrypt;
        }
    }
}
