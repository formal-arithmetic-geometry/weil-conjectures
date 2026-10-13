## What changed

Proved `AlgebraicGeometry.Scheme.affine_section_linear_map_extension` with its signature
unchanged. The proof first constructs the extension on `Spec R` from the source counit,
`tilde.map`, and the target counit, checks its action on sections, transports along the
affine scheme isomorphism, and returns through `overEquiv` and `overFunctorEquiv`.
Five proved private helpers expose the required calculations without assuming the target
is quasi-coherent. The calculations adapt the source-library proofs in
`Modules.FaithfullyFlatDescent`, `Modules.AffineHom`, and `Modules.PullbackTilde`;
none of those modules is imported in the final proof. Quasi-coherence of pushforward
along an isomorphism is proved using restriction along its inverse, so no general
pushforward or cohomological theorem is required.

Replaced the broad public `Sheaf.AlgebraicGeometry.Coherent` import with the Mathlib
imports needed by the statement, and added a proof-only import of
`Mathlib.AlgebraicGeometry.Modules.Tilde`. Updated the existing node's proof and
proof origin to record the actual calculations; its proof dependency set stays the same.
No existing declaration signature or definition was changed.
The public-import pruning is recorded in
`coord/changes/affine-section-linear-map-extension-imports.md` (status open).
The final source compiles without warnings. A separate `#print axioms` probe reports
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affine_section_linear_map_extension`
(node `lem-weil-pbc-affine-section-linear-map-extension`).
No holes added. No `sorry` remains in the delivered module. This is a proof,
not a decomposition. The construction never chooses data from an unproved existence theorem.

## No longer needed

Removed imports: `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
(already publicly imported by `Mathlib.AlgebraicGeometry.Modules.Sheaf`) and
`Sheaf.AlgebraicGeometry.Coherent` (node `pqf-def-coherent` remains a
statement dependency for the meaning of quasi-coherence, which is Mathlib's predicate).
Its custom coherent predicate and `Sheaf.Paper.DerivedHomMayerVietoris` infrastructure
are not needed by this proof. This makes no claim that these modules cease to be reached
from all targets; the direct consumer still imports `Coherent` for its own statement.

No planned proof-dependency node is pruned: both
`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-module-restriction-open-immersion-colimits` are used through their
Mathlib realizations. No unit-level statement or proof step is bypassed.
The source-library `Modules.AffineHom`, `Modules.FaithfullyFlatDescent`,
`Modules.PullbackTilde`, and `Cohomology.DirectImage.AffineMorphism` are unnecessary
imports: their useful calculations are proved locally from Mathlib, with no new holes.

## Where the brief, the DAG or earlier work was wrong

The existing source-library extension lemmas assume the target is quasi-coherent,
although the counit construction and its component check never use that hypothesis.
They therefore cannot be applied directly to this interface. The private helpers remove
that unnecessary assumption without changing those modules.
The planned route and the item's statement are valid, including empty affine opens
and zero modules. The direct consumer imports this item only for proofs and imports
`Coherent` separately, so removing the item's broad import requires no adaptation.

## Second reading by X3

1. **Interface: pass.** Compared the only delivered Lean module against the repository
   with `diff`, and separately compared the existing theorem's signature as bytes.
   The signature, visibility, universe and namespace are unchanged; no existing
   definition changes. The public-import replacement is explicitly declared in
   `coord/changes/affine-section-linear-map-extension-imports.md`. Read the sole
   direct consumer, `IdealPowerQuotientAffineLiftingSection`: it already imports
   `Coherent` and `PushforwardContinuous`, and imports this item only for its proof.
   The replacement therefore requires no forced adaptation.
2. **Proof: pass.** Read all five private helper proofs and the final proof. Local
   `lcompile.py` compilation succeeds without warnings. The construction uses the
   actual tilde map and counits, restriction isomorphisms and fully faithful
   preimages; it chooses no data from an unproved theorem. The module contains no
   `sorry` or forbidden declaration. A fresh scratch-copy axiom check of
   `AlgebraicGeometry.Scheme.affine_section_linear_map_extension` shows only
   `propext`, `Classical.choice` and `Quot.sound`.
3. **Split statements: pass (none).** No new open statement, module or node is
   introduced. The five private helpers are fully proved. Their constructions
   remain valid for the zero ring (empty spectrum), zero source and zero target;
   no nonempty-open or nonzero-module assumption enters the argument. The target
   sheaf is arbitrary throughout, as the existing theorem requires.
4. **Route and pruning: pass.** Read the Mathlib dependency realizations and the
   source-library `AffineHom` and `FaithfullyFlatDescent` extension lemmas. The
   latter require target quasi-coherence, so cannot replace these helpers.
   A new leanfinder search for morphisms into arbitrary sheaves and an independent
   grep for hom equivalences, full/faithful functors and isomorphism pushforward
   found ingredients, not an applicable shorter extension theorem. The local
   counit calculations use just Mathlib. The public imports supply the statement;
   `Modules.Tilde` is correctly proof-only. Both old proof-dependency nodes are
   still used, and `No longer needed` identifies the removed imports without
   claiming global unreachability. Read `dag/units/sk-thm-p1.json`: this item is
   below its realized statement and steps; no unit route is bypassed.
5. **DAG: pass.** The node differs only in `proof` and `proof_origin`; its
   `proof_deps` are exactly the union of step `uses`. Its recorded Lean signature
   matches the delivered signature, and its two steps describe the actual
   restriction, counit construction, scalar identification, equivalence preimage
   and equality transport. No new-node metadata is required.

Second reading changed only this report by recording the independent checks.
No proof repair was necessary. One original hole is closed, zero holes are added,
and zero planned proof-dependency nodes are pruned.
