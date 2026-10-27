Maintenance correction, 2026-10-25 — Q109, stage 2

The duplicate-declaration return for immutable head bed7ec2d12ba is superseded.
FrobeniusKernelInductionData belongs to competing Q88 delivery
957e28136c3051c8c4e847411de7659d93546d18. That delivery never landed and is now
only refs/stale/deliver/Q88/lem-sfb-frobenius-kernel-induced-dual-pbw. Its source,
definition node and compiled module are absent from the authoritative library.
The current source index has no owner for the four disputed declarations.
Do not add an import of that unpublished module or remove Q109's definitions
because of the old return.

Maintenance restored these sandbox files byte for byte from bed7ec2d12ba:

- lean/Sheaf/AlgebraicGeometry/GroupScheme/FrobeniusInductionConstructions.lean
- dag/nodes/sec-six-functors-basics/def-sfb-frobenius-induction-constructions.json

They own push, sigma, relations and induced. The theorem file is unchanged.
The restored packet compiles with tools/lean_file.sh, one file at a time with
the 60-second limit. The construction took 8.0 s and the theorem 17.5 s.
Current-server delivery, graph and import checks pass. The resumed worker also
passed deliver2.py --no-push and delivered aeac121c7be on 2026-10-25.

Continue with the current server item and delivery state. If the delivery is
still waiting, allow its ordinary independent review. If it has landed, use
the current node binding. Do not recreate the unavailable Q88 module or redo
the item's mathematics. The original independent Q109 review already recorded
PASS; this maintenance repair itself does not replace review or landing.

The old blocker history in the worker report is superseded by its Maintenance
correction section. Backups use the suffix .maint-Q109-1792861614.bak.
