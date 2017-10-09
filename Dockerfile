FROM openjdk:8u121-jdk-alpine

# needed for the calculus gui...otherwise we get a runtime error
RUN apk add --update ttf-dejavu && rm -rf /var/cache/apk/*

# The bash shell is required by Scala utilities
RUN apk add --no-cache bash

# Install build dependencies
RUN apk add --no-cache --virtual=.dependencies tar wget curl

RUN wget -O- "http://downloads.lightbend.com/scala/2.12.3/scala-2.12.3.tgz" \
    | tar xzf - -C /usr/local --strip-components=1


RUN apk add --update openssl

# Download Nix and install it into the system.
RUN wget -O- https://nixos.org/releases/nix/nix-1.11.15/nix-1.11.15-x86_64-linux.tar.bz2 | bzcat - | tar xf - \
  && addgroup -g 30000 -S nixbld \
  && for i in $(seq 1 30); do adduser -S -D -h /var/empty -g "Nix build user $i" -u $((30000 + i)) -G nixbld nixbld$i ; done \
  && mkdir -m 0755 /nix && USER=root sh nix-*-x86_64-linux/install \
  && ln -s /root/.nix-profile/etc/profile.d/nix.sh /etc/profile.d/ \
  && rm -r /nix-*-x86_64-linux \
  && rm -r /var/cache/apk/*


ONBUILD ENV \
    ENV=/etc/profile \
    PATH=/root/.nix-profile/bin:/root/.nix-profile/sbin:/bin:/sbin:/usr/bin:/usr/sbin \
    GIT_SSL_CAINFO=/root/.nix-profile/etc/ssl/certs/ca-bundle.crt \
    NIX_SSL_CERT_FILE=/root/.nix-profile/etc/ssl/certs/ca-bundle.crt


ENV \
    PATH=/root/.nix-profile/bin:/root/.nix-profile/sbin:/$PATH \
    GIT_SSL_CAINFO=/root/.nix-profile/etc/ssl/certs/ca-bundle.crt \
    NIX_SSL_CERT_FILE=/root/.nix-profile/etc/ssl/certs/ca-bundle.crt \
    CURL_CA_BUNDLE=/root/.nix-profile/etc/ssl/certs/ca-bundle.crt \
    NIX_PATH=/nix/var/nix/profiles/per-user/root/channels/


# A massive hack to stop curl complaining about ssl certificates...no idea what's going on...
RUN echo insecure >> ~/.curlrc

RUN nix-env --option verify-https-binary-caches false --install isabelle-2016-1 && nix-env --option verify-https-binary-caches false --install perl-5.24.2


RUN apk del --no-cache .dependencies

# Compile Isabelle's HOL theory files.
RUN isabelle build -s -b HOL

RUN apk add --no-cache --update python p7zip


WORKDIR /root

COPY tools tools
COPY libs libs
COPY template template
COPY build.py build.py
