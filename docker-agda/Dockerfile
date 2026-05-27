FROM debian:testing-slim

RUN apt-get update && apt-get install -y \
    agda \
    agda-stdlib \
    elpa-agda2-mode \
    emacs-nox \
    git \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m agda
USER agda
ENV LANG=C.UTF-8
WORKDIR /home/agda

ENTRYPOINT ["emacs"]

