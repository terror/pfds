# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**pfds** is a Rust library implementing purely functional data structures, following Chris Okasaki's "Purely functional data structures" book. This is an educational/academic project focused on functional programming concepts.

## Build System

This project uses `just` (a command runner) for build automation. Available commands:

- `just build` - Build the project with cargo
- `just test` - Run tests with cargo test  
- `just clippy` - Run clippy linter
- `just fmt` - Format code using nightly rustfmt
- `just fmt-check` - Check if code is properly formatted
- `just watch` - Watch for changes and run tests (default), or specify command like `just watch clippy`
- `just all` - Run build, test, clippy, and fmt-check (comprehensive check)

To run a single test: `cargo test test_name`

## Code Architecture

The project implements lazy, purely functional data structures:

### Core Modules
- `src/lib.rs` - Main library module that exports public APIs and common imports
- `src/stream.rs` - Lazy stream implementation using suspended computations (`Rc<dyn Fn()>`)
- `src/queue.rs` - Queue trait and BankersQueue implementation

### Key Design Patterns
- **Lazy Evaluation**: Streams use `Rc<dyn Fn()>` closures to defer computation until needed
- **Structural Sharing**: Data structures are immutable and share structure between versions
- **Lifetime Management**: All structures use lifetime parameter `'a` for borrowed data
- **Trait-based Design**: Core operations defined through traits (e.g., `Queue<'a, T>`)

### Data Structures
- `Stream<'a, T>` - Lazy, potentially infinite sequences with operations like `cons`, `head`, `tail`, `append`, `reverse`
- `BankersQueue<'a, T>` - Amortized O(1) queue using two streams with automatic rebalancing when `len_rear > len_front`

## Development Setup

- Uses Rust 2021 edition
- Requires nightly Rust for formatting (`cargo +nightly fmt`)
- No external dependencies (pure Rust implementation)  
- Custom rustfmt config: 80-char width, 2-space indentation, Unix newlines
