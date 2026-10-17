//! Checkout identity captured at build time, reported by the CLI.
pub const text: [:0]const u8 = "unflate " ++ @import("build_info").identity ++ "\n";
