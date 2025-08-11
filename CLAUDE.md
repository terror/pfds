# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**pfds** is a Rust library implementing purely functional data structures, following Chris Okasaki's "Purely functional data structures" book. This is an educational/academic project focused on functional programming concepts.

## Build System

This project uses `just` (a command runner) for build automation. Available commands:

- `just build` - Build the project with cargo
- `just test` - Run tests with cargo test
- `just clippy` - Run clippy linter on all targets and features
- `just fmt` - Format code using nightly rustfmt
- `just fmt-check` - Check if code is properly formatted
- `just watch` - Watch for changes and run tests (default), or specify command like `just watch clippy`
- `just all` - Run build, test, clippy, and fmt-check

## Code Architecture

The project follows a simple Rust library structure:
- `src/lib.rs` - Main library module that declares other modules
- `src/stream.rs` - Currently empty, likely intended for stream-based data structures
- The codebase is in early development with minimal implementation

## Development Setup

- Uses Rust 2021 edition
- Requires nightly Rust for formatting (`cargo +nightly fmt`)
- No external dependencies currently (pure Rust implementation)
- Uses standard Rust project structure with Cargo.toml
