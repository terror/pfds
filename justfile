set dotenv-load

export EDITOR := 'nvim'

alias t := test

default:
  just --list

all: build clippy fmt-check test

build:
  cargo build

clippy:
  cargo clippy

fmt:
  cargo +nightly fmt

fmt-check:
  cargo +nightly fmt --all -- --check
  @echo formatting check done

test:
  cargo test

watch +COMMAND='test':
  cargo watch --clear --exec "{{COMMAND}}"
