//! Checkout identity captured at build time.
const root = @import("root");

pub const text: [:0]const u8 = "unflate " ++
	(if (@hasDecl(root, "deflopt_build_info")) root.deflopt_build_info.identity else
		"unknown (unrecorded build)") ++ "\n";
