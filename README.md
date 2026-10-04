# PSC - Pulse Shopping Coin

A Flask-based Kenyan online shop with a PSC loyalty coin wallet, multi-vendor product aggregation, and integrated payment gateways.

## Features

- Multi-vendor scraping: Jumia, Kilimall, Carrefour, Jiji, Fahavi, Text Book Centre, Naivas, Vivo, Copell, Safaricom Masoko, Hotpoint Appliances, Samsung Brand Store.
- PSC wallet: three-bucket model (wallet_psc spendable, savings_psc parked, deposit_psc hold-only).
- Daily bonus: 1 PSC granted once per day.
- Payments: Flutterwave, Paystack, optional CoinGate and MoonPay.
- Virtual Accounts, KYC, AML screening, CBK/KRA hooks.
- Seller subsystem, P2P transfers, high-value withdrawals.
- Blockchain mining and SocketIO real-time updates.

## Setup

1. git clone your repo
2. python -m venv venv
3. Activate venv
4. pip install -r requirements.txt
5. python -m playwright install chromium
6. copy .env.example .env
7. python client_app.py

## Security

- .env is never committed.
- Customer PII is never committed.
- Do not disable .gitignore protections.
