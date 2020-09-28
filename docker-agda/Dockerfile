FROM neosimsim/agda
LABEL maintainer="mathias.kegelmann@gmail.com"

USER root
RUN apk add emacs
RUN ln -s /home/agda/.cabal/bin/agda-mode /home/agda/bin
RUN echo "(load-file (let ((coding-system-for-read 'utf-8)) (shell-command-to-string \"agda-mode locate\")))" >> /home/agda/.emacs

USER agda
ENV LANG C.UTF-8

ENTRYPOINT ["emacs"]
