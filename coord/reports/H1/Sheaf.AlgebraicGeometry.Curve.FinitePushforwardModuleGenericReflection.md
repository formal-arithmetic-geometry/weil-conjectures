## What changed

The original theorem
`AlgebraicGeometry.Scheme.exists_dense_open_locallyConstant_of_finite_lowerStar_module`
now has a complete Lean proof with its signature, universes, visibility and original docstring
unchanged. Its geometric first step is isolated in the new module
`Sheaf.AlgebraicGeometry.GenericFiniteNoetherianSchemeSplitting`. This statement involves
schemes only: no coefficient ring, sheaf, direct image, or local-constancy assumption.

The new module `Sheaf.AlgebraicGeometry.DisjointOpenDirectImageRetract` proves
`AlgebraicGeometry.Scheme.nonempty_retract_lowerStar_of_disjoint_open_partition`.
A disjoint open piece is clopen; the invertible extension-by-zero/direct-image comparison
and the two adjunction triangle identities supply a retract. Applying direct image and
its composition isomorphism gives the component direct-image retract. This lemma assumes
neither a finite morphism nor any local-constancy condition.

Two proved private helpers in the item identify a retract with the kernel of its
complementary projector, and reflect finite local constancy through a disjoint splitting
into universal homeomorphisms. The main proof restricts the hypothesis from V to U, applies
finite exchange twice, applies those helpers on each cover member, and descends along
the pulled-back etale cover using the existing `IsLocallyConstantSheaf.of_cover` theorem.
The kernel theorem used here requires no Noetherian coefficient hypothesis.

All added proof imports are non-public. The three delivered modules compile together in
import order with lcompile.py, without errors or warnings. No other existing module is
adapted; no existing public interface or target is changed.

## Proved and sorry left

Closed the item's sole direct hole:
`AlgebraicGeometry.Scheme.exists_dense_open_locallyConstant_of_finite_lowerStar_module`
(node `lem-weil-pbc-finite-module-generic-reflection`). This is a decomposition, not an
axiom-free proof of the original theorem: one strictly geometric hole was added below it.

Proved the new public theorem
`AlgebraicGeometry.Scheme.nonempty_retract_lowerStar_of_disjoint_open_partition`
(node `lem-weil-pbc-disjoint-open-direct-image-retract`), and the item's private helpers
`AlgebraicGeometry.Scheme.locallyConstant_of_retract` and
`AlgebraicGeometry.Scheme.locallyConstant_of_split_lowerStar`. They contain no direct sorry.

The only sorry left in the delivery is
`AlgebraicGeometry.Scheme.exists_dense_open_finite_noetherian_scheme_splitting`
(node `lem-weil-pbc-generic-finite-noetherian-scheme-splitting`) in
`Sheaf.AlgebraicGeometry.GenericFiniteNoetherianSchemeSplitting`.
Its whole proof is `:= by sorry`, and its docstring and node describe reduction, affine
component splitting, etale-cover lifting, and clopen component lifting. The existing
integral affine splitting theorem is proved and is imported as the principal input to
this geometric step. One old hole closed, one new hole added: net zero direct holes;
the module-theoretic steps and final combination are now implemented.

Edge-case review: for an empty target the geometric statement allows an empty cover;
for an empty finite inverse image it allows n = 0. The proved split-reflection helper
handles empty partitions via an empty open cover, with no arbitrary index selection.
Empty components are allowed in the retract lemma and the clopen comparison still applies.
For an identity map or a universal-homeomorphism finite map, the geometric statement has
a single whole-source piece. Different components can have different fibre cardinalities
because n is chosen separately for every cover member. The coefficient ring is arbitrary,
and neither private helper adds Noetherianity or finiteness of the retract to its conclusion.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.GenericFiniteAlgebraSplitting`: replaced by the general
  scheme-level geometric bridge. The algebra splitting remains needed transitively
  through `GenericFiniteSchemeSplitting`; its module and node are not globally pruned.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`: the proof uses the
  proved `IsLocallyConstantSheaf.kernel_and_cokernel` from `KernelCokernel`. The original
  hom-constant node is still needed for this kernel argument; its underlying theory
  remains transitively imported and is not globally pruned.
- `WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`: the source-piece step uses
  `Etale.isEquivalence_lowerStar` and the adjunction counit from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` instead of
  local-constancy descent along a reduction. The old invariance node is no longer a
  direct dependency of the item, but is still needed in the library's cover machinery.

The item's DAG no longer directly uses `lem-weil-pbc-generic-finite-algebra-splitting`
or `lemma-constructible-universal-homeomorphism-invariance`; the proof_deps now record the
actual geometric bridge and the topos-equivalence route. No existing module is claimed
to have left the targets' transitive import closure. No unit statement or realized unit
step is bypassed: this item is below the curve-reduction portion of sk-thm-p1.

## Where the brief, the DAG or earlier work was wrong

Retry verification (2026-10-13): `lcompile.py --all` compiled all three preserved
modules successfully, with no errors or warnings. The required `deliver3.py --no-push`
dry run still fails before compilation with `FAILED: missing import source modules`,
listing the item's Mathlib Noetherian and Finite imports and the new modules' Mathlib
imports. Read-only diagnosis confirms that `source_roots(Path('/home/ubuntu/weil-lean'))`
returns an empty list: it switches to the existing nested `lean/` directory, whereas
this installation's package sources are at `/home/ubuntu/weil-lean/.lake/packages`.
The reported missing Mathlib Noetherian source exists there. The earlier missing
`refuse_missing` function is now present, but this source-root failure remains.
No tools were patched or checks bypassed. Maintainer/launcher repair of package-source
root discovery is required before this delivery can obtain an OK dry run.

No false statement or signature correction was found. The original dependencies provide
an algebraic splitting and the general sheaf tools, but not the bridge from arbitrary
Noetherian targets to a splitting cover. That bridge is the geometric substep isolated
here. The original direct-factor argument also needed an explicit categorical retract;
it is now proved using the already proved clopen comparison, rather than leaving a
section-gluing lemma with sorry.

The LeanSearch service returned Internal Server Error for both new-node searches;
LeanFinder and source searches were completed and are recorded in the nodes. The Stacks
sources were checked at Tags 095K, 0959, 04DZ and 0A5D. Tag 095K itself gives a flat
stratified decomposition; the stronger generic etale/universal-homeomorphism form here
uses the existing project's generic finite-algebra refinement, as stated explicitly in
the new geometric theorem's source and proof. It is not attributed to 095K alone.

## New nodes

`lem-weil-pbc-generic-finite-noetherian-scheme-splitting`:
the sheaf-independent geometric portion of parent proof step 1, with the same chapter and
unit. Its module is `lean/Sheaf/AlgebraicGeometry/GenericFiniteNoetherianSchemeSplitting.lean`.
It keeps one named sorry and is strictly part of the original argument. Its source is
the parent step and the generic splitting refinement, together with Tags 095K and 04DZ.

`lem-weil-pbc-disjoint-open-direct-image-retract`:
the component direct-factor portion of parent proof step 2, proved completely. Its module
is `lean/Sheaf/AlgebraicGeometry/DisjointOpenDirectImageRetract.lean`. Its source is the
parent module direct-factor argument and the proved clopen comparison. Both nodes contain
three search records, self-contained statements and complete proof plans. The existing
item node's proof, proof_deps and proof_origin now follow the Lean proof. There are no
interface change records because no existing public statement or definition changed.

## Second reading by H1

1. I compared the delivered item with the repository version. The theorem signature and all
existing declarations are unchanged byte for byte; import pruning and the two new modules are
recorded above. Verdict: pass.

2. I compiled all three modules with `lcompile.py --all`. Compilation succeeds without errors or
warnings. The only remaining `sorry` is the named geometric theorem
`exists_dense_open_finite_noetherian_scheme_splitting`; it is public, documented, and has its DAG
node. No forbidden declarations or hollow definitions occur. Verdict: pass, with that documented
split hole remaining.

3. I checked the split statements and edge cases. The retract theorem is vacuous for an empty
index type and handles empty components; the geometric theorem permits an empty cover and
zero-sized partitions. Both statements are strictly below the target and are not duplicate
library results. Verdict: pass.

4. I checked the proof route against the unit record and DAG dependencies. The target uses the
geometric splitting bridge, finite exchange, the component retract, kernel reflection, universal
homeomorphism invariance, and cover descent as written. Removed imports are listed under
`## No longer needed`; no unit step is bypassed. Verdict: pass.

5. I checked node metadata, declarations, proof dependencies, and proof origins against the Lean
files. The new node records contain statements, sources, proof plans, searches, and Lean records;
the target node follows the implemented route. Verdict: pass.

I changed only this report by adding this second-reading record. No Lean source, declaration,
statement, definition, or DAG node required repair.

