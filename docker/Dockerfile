# Image for the Lean arena tasks: Lean 4 toolchain, Mathlib with its prebuilt cache, the grader.
# Build once, run every task from it. Needs network at build time only; tasks run offline.
#   docker build -t lean-arena -f docker/Dockerfile .
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends curl ca-certificates git python3 zstd xz-utils \
    && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
COPY lean/lean-toolchain lean/lakefile.toml lean/lake-manifest.json lean/Arena.lean /opt/arena/lean/
WORKDIR /opt/arena/lean
RUN lake exe cache get && lake build Arena
COPY lean/verifier/Verify.lean /opt/arena/Verify.lean
COPY arena/grade.py /opt/arena/grade.py
RUN lake env printenv LEAN_PATH > .lake/lean_path.txt && chmod -R a+rX /opt/arena /opt/elan
ENV ARENA_LEAN=/opt/arena/lean
WORKDIR /app
