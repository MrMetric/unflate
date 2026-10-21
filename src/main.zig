//! Executable entry point with build-supplied checkout identity.
pub const deflopt_build_info = @import("build_info");
pub const main = @import("deflopt_cli.zig").main;
