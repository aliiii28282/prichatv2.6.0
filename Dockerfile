FROM python:3.12-slim

WORKDIR /app

# نصب وابستگی‌ها در یک لایه جدا برای کش شدن
COPY requirements.txt .
RUN pip install --no-cache-dir --upgrade pip \
    && pip install --no-cache-dir -r requirements.txt \
    && python -c "import telegram, jdatetime; print('BUILD-CHECK telegram', telegram.__version__)"

# کد ربات
COPY bot.py .

# دیتا روی Volume (پیش‌فرض bot.py همان /data را می‌سازد؛ در Railway مونت‌پوینت Volume را /data بگذارید)
RUN mkdir -p /data

CMD ["python", "bot.py"]
