FROM mcr.microsoft.com/playwright/python:v1.62.0-jammy

WORKDIR /app

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PLAYWRIGHT_BROWSERS_PATH=/ms-playwright

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

CMD gunicorn client_app:app --bind 0.0.0.0:$PORT --workers 1 --threads 4 --timeout 120
