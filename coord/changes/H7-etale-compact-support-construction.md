# Etale compact-support construction proof

The item `Sheaf.Paper.EtaleCompactSupportConstruction` gains proved private helpers,
proof imports, local irreducibility attributes for quotient sheaves and exact derived
functors, and a transparency-respecting proof of its existing theorem. These settings
are local proof aids. Its public import and theorem signature are unchanged.

Two new modules provide ordinary open-extension data and a proved derived-image assembly
retaining a restriction representative equation. The only added hole is the ordinary
existence theorem. These declarations have new DAG nodes. No existing definition or
statement changes; no consumer adaptation or source-library modification is required.

Consumer: the item itself (group H7). Other modules retain the same existing interface.
The item compiles cleanly in 43.3 seconds. All new dependency edges are reviewed by the
normal stage-3 preflight and independent-reader process.
