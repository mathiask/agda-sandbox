# Multi-Architecture Build Instructions (Gemini+MK)

We use this method to bypass QEMU emulation failures that occur during Emacs
native JIT compilation.

## 1. Build and Push the ARM Image (Run on M1/Apple Silicon)

```bash
docker build --pull -t mathiask/agda:latest-arm64 .
docker push mathiask/agda:latest-arm64
```

## 2. Build and Push the AMD Image (Run on x86_64 Linux/GCP)

```bash
docker build --pull -t mathiask/agda:latest-amd64 .
docker push mathiask/agda:latest-amd64
```

## 3. Combine into a Single Manifest (Run anywhere)

Once both architecture-specific tags are pushed to Docker Hub, combine them
under the primary `latest` tag.

We use `imagetools` instead of the legacy `manifest create` command to avoid
provenance metadata errors ("is a manifest list").

```bash
docker buildx imagetools create -t mathiask/agda:latest \
  mathiask/agda:latest-amd64 \
  mathiask/agda:latest-arm64
```
