# Vault — added features (ported from Otp-pannel, Vault look kept)

- Server 3 (Provider 1 / Provider 2): needs SERVER3_API_KEY. Admin → Settings → Server 3 (markup, on/off).
- Bulk Buy (Server 1): Direct OTP one-by-one or Session ZIP + 2FA, from the country detail screen.
- Stock announcements: posted after every upload with a "Buy This Stock" deep link.
- Referral: join reward after all force-join channels + first-deposit % (capped); withdraw requests.
- Payment control: Razorpay QR, Razorpay Payment Link, manual UPI QR, manual payment link — each ON/OFF;
  Razorpay keys editable in the panel; API polling (no webhook); manual proofs go to the payment group.
- Session safety: invalid unsold session -> inactive + Replace/Remove buttons; sold sessions are not re-reported.
- OTP receiver: 72h window, auto-reconnect, Request New OTP, Manage Sessions.
- Upload: Phone + OTP login, Session String, Session File / ZIP (duplicates and dead sessions rejected).
- Admin: Settings -> Referral, Payment Control, Channels & Logs, Force Join, Server 3.

Notes
- Deposits no longer count as "withdrawable"; only referral earnings can be withdrawn.
- Not live-tested against Telegram/Razorpay/Mongo here (no network): test on a staging bot first.
