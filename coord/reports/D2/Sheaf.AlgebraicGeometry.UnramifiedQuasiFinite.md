## What changed

Proved `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_unramified` in
`Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite` with its signature unchanged.
The proof chooses affine neighbourhoods, uses Mathlib's finite-type and formally
unramified section-map results, and applies Mathlib's unramified-to-quasi-finite
algebra instance. Artinian fibre rings have discrete spectra, so the defining
singleton is open. Added proof-only imports of
`Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` and
`Mathlib.RingTheory.Unramified.LocalStructure`. Updated the existing node's proof,
proof dependencies and proof origin to this route. The public imports needed by the statement remain; the unused public import
of `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` was removed in second reading. No definitions or statements changed.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_unramified`
(node `lem-weil-pbc-unramified-quasi-finite-at-points`). No sorry remains in the
item or is introduced elsewhere. The proof uses no deferred project theorem.
Local compilation succeeds; delivery preflight supplies the axiom probe.
The empty source is vacuous; for a nonempty source the chosen point supplies a
fibre point. No nontriviality or field-product choice is assumed.

## No longer needed

Removed the unused public import
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` and these proof-only imports:
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`
- `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`
- `Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`
- `Sheaf.RingTheory.QuasiFiniteAtPrime` (its definition remains available through
  the public import of `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`).

The old proof nodes no longer required by this proof are:
- `def-weil-affine-spectrum`
- `lem-weil-pbc-unramified-base-change-open`
- `lem-weil-pbc-unramified-ring-map-iff-unramified-affine`
- `def-weil-pbc-kahler-differentials`
- `lem-weil-pbc-kahler-differentials-base-change`
- `lem-weil-pbc-unramified-algebra-over-field-product`
- `lem-weil-pbc-spec-finite-product-fields`

The three removed theorem modules are pruned from this item's route; they may
still be reached elsewhere. `Sheaf.RingTheory.QuasiFiniteAtPrime` remains a
statement dependency and is not globally pruned. The unit `sk-thm-p1` realization
lists neither this item nor its removed dependencies as unit steps; its fixed
route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically valid but unnecessarily uses a finite
product decomposition. The node's search had already found Mathlib's general
unramified algebra instance, but anticipated a difficult comparison of notions.
Here that comparison is immediate: the project's definition asks only that a
singleton in the fibre spectrum be open, and Mathlib proves the whole spectrum
discrete via Artinian fibres. The second reading updated the declaration docstring to describe the implemented
Mathlib route.

## Second reading by D2

1. Compared the complete delivered module and node with the repository versions.
   The existing theorem signature is byte for byte unchanged; no definition or
   statement changed. Public-import removal is recorded in
   coord/changes/UnramifiedQuasiFinite-imports.md. The only Lean changes are
   its proof, imports, and the docstring describing that proof. Verdict: pass.
2. Compiled the module with lcompile.py, then compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_unramified`.
   The result is exactly propext, Classical.choice, Quot.sound. No sorry or
   prohibited declaration occurs in the delivered module. Verdict: pass.
3. There are no split-off statements or new nodes to review. The proof also
   handles an empty source vacuously and never assumes the section rings or a
   fibre ring are nonzero. No finite-product decomposition is needed. Verdict: pass.
4. Read IsQuasiFiniteAtPoint and Algebra.IsQuasiFiniteAtPrime: the affine opens,
   containment, finite-type witness, and open singleton are precisely their
   requirements. Read Mathlib's open-diagonal FormallyUnramified instance,
   formallyUnramified_appLE, the EssFiniteType/FormallyUnramified QuasiFinite
   instance, and its Artinian-fibre instance. These justify the complete short
   route; it uses no deferred project theorem. The seven nodes removed from
   the old proof_deps are all listed above. Opened sk-thm-p1.json: neither this
   node nor the removed dependencies realizes its statement or a proof step.
   The unit route is preserved. Found and removed the unused public import
   Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite; the smaller import set
   compiles and gives the same permitted axioms. Verdict: pass after repair.
5. Compared both node JSON files: only proof, proof_deps, and proof_origin
   differ. The three new steps match the affine-neighbourhood construction,
   Mathlib algebra instances, and unfolding of the fibre-singleton definition;
   proof_deps is their uses union. No new-node fields are required. Verdict: pass.

Second reading changed the outdated finite-product proof docstring and removed
one unused public Mathlib import. It left the correct proof unchanged.
The additional removed import is
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`; no further DAG node is pruned.

Change record: `coord/changes/UnramifiedQuasiFinite-imports.md` (public-import removal).
