## What changed

Restored lean/Sheaf/Paper/GlobalVerdierDuality.lean from its current quarantine
archive. Made both coefficient universes explicit in C, Operation, System and field-scalar
applications, including the package fields and Assertion. Enabled the two
transparency-respecting unification options locally for Package. This repairs
the assigned package-elaboration failure without changing the theorem, canonical
maps, normalization equations, coefficient domains or public imports.

Change record: coord/changes/G5-global-verdier-universe-elaboration.md.

## Proved and sorry left

Holes closed: none (0). Holes added: none (0). This is the assigned build repair,
not a proof or decomposition of the existing theorem.

One existing hole remains: WeilConjectures.GlobalVerdierDuality.global_verdier_duality,
attached to sk-thm-sf-global-duality and thm-sf-global-duality. Its source and complete
six-step proof plan are preserved verbatim in its docstring. There is no sorry in
a definition. No theorem signature changes.

## No longer needed

None. No import, declaration, node, proof dependency or module is removed. The
unit route through Verdier exchange and the point identifications remains intact.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it was quarantined, not because its mathematics
was withdrawn. The current rework row and archived source were used for restoration.
The saved global-build error is a deterministic elaboration timeout in the
rationalization field followed by cascading argument errors. The archived source
compiled against the published dependencies on the initial check, but a subsequent
compile with only universe annotations timed out at rationalScalar. The final
explicit two-universe applications and local transparency settings compile cleanly
through lcompile.py in 32.8 seconds. No heartbeat or wall-time limit was raised. Both DAG attachments and all
proof steps remain valid and unchanged. A shorter-route search found the upstream
finite-coefficient global-duality isomorphisms, but those do not by themselves
construct this four-stage normalized package with its coefficient and shift fields.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
