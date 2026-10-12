## What changed

Proved the constructible-coefficient reduction and the two dense-open existential reductions in
WeilConjectures.AlgebraicGeometry.Curve.Reductions, without changing any signatures.
Both use existing generic constancy and restriction along immersions with nested ranges.
Added proof imports of generic constancy, the new intermediate modules, existing prime-torsion
devissage, torsion characterizations, reduction properties and cohomology functoriality.
Added four one-theorem modules: DenseIrreducibleOpens, DenseOpenPrimeAssertions,
DisjointOpenPrimeAssertions, and PrimeConstructiblePullback. The geometric theorem is completely proved from existing
library topology and Noetherian scheme results. It includes the empty scheme and n = 0.
Updated only proof, proof_deps, and proof_origin of the three corresponding existing DAG nodes.
A concurrent upstream delivery proved of_shortExact; its imports, helpers, and proof are
preserved in the delivered module. Q1 does not claim that proof as its work.

## Proved and sorry left

Proved by Q1:
- AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced
  (lem-weil-pbc-curve-constructible-reduction), from the fixed-prime approximation bridge
  and existing prime-torsion devissage, with the reduction comparison proved in Lean.
- AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_lowerShriek
  (lemma-weil-pbc-curve-dense-open-reduction), from the named intermediate assertions.
- AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_forall_lowerShriek
  (lem-weil-pbc-curve-dense-open-localization), from the named intermediate assertions.
- AlgebraicGeometry.IsCurve.exists_dense_irreducible_opens
  (lem-pbc-q1-dense-irreducible-opens), with no sorry in this theorem or new helper.

The original snapshot had seven sorries, not eight (the initial commentary miscounted).
One was proved concurrently upstream; Q1 closes three of the six remaining original sorries.
Three original sorries remain untouched:
- AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced
  (lemma-weil-pbc-curve-constructible-primary-reduction).
- AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar
  (lemma-weil-pbc-normalization-exact-sequence).
- AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite
  (lemma-weil-pbc-curve-normalization-constant).
Three new named sorries remain, each exactly `:= by sorry` in its own module:
- AlgebraicGeometry.IsCurve.assertions_iff_dense_open_prime
  (lem-pbc-q1-dense-open-prime-assertions).
- AlgebraicGeometry.IsCurve.assertions_iff_disjoint_open_prime
  (lem-pbc-q1-disjoint-open-prime-assertions).
- AlgebraicGeometry.Etale.bijective_cohomologyMap_of_constructible_prime
  (lem-pbc-q1-prime-constructible-pullback).
The first two are strictly parts of the localisation argument: one transfers assertions across a
specified dense open and has no geometric existence conclusion, the other decomposes
extension by zero over specified disjoint opens and assumes neither density nor irreducibility.
The third concerns one prime on a fixed qcqs morphism, with neither reducedness nor
field-extension geometry; the whole constructible reduction is not restated.
Every added sorry has a source, full prose proof, and DAG node.

## No longer needed

No existing import was removed: all are needed by the pre-existing filtered-colimit,
dimension-zero, and freshly landed devissage proofs, or by existing signatures.
No whole module is claimed to leave the target closure.

For lemma-weil-pbc-curve-dense-open-reduction, the direct proof no longer uses
lemma-weil-pbc-curve-constructible-primary-reduction or
lemma-weil-pbc-eight-curve-devissage. The geometric existence does not require an imported
Sheaf.AlgebraicGeometry.LocallyClosedStratification; existing generic constancy suffices.

For lem-weil-pbc-curve-dense-open-localization, the direct proof no longer needs the
CurveCoefficientPair, ConstructibleTorsionCurveSheaf, EtaleSheaves, or DenseOpenAssertions
module encodings, or its original individual C1-C8 proof dependencies. The new named module
statements use the existing ModuleCat coefficient convention directly. The open-closed,
zero-dimensional, stalk, finite-sum, and conditional-assertion theory remains needed below
the two intermediate nodes, as their prose proofs explain; it is not claimed globally pruned.
For lem-weil-pbc-curve-constructible-reduction, the separate Chinese-remainder primary
decomposition, constructible-kernel/cokernel induction, and direct use of
lemma-weil-pbc-eight-curve-devissage are replaced by the existing
PullbackIsoPrimeTorsionDevissage, whose prime-factor proof is already written. No direct
imports of ConstructibleTorsionModulesAgree, ConstructibleModuleSheafColimit or
ConstructibleRestrictionClass are needed by the parent: their encoding and universe-size
work is confined to the new fixed-prime approximation node. These nodes are not claimed
globally pruned, since the remaining assertion-package reduction may still need them.
All definitions required to state the original statements remain unchanged.


Second-reader audit of direct dependency removals (relative to the repository snapshot):

- `lem-weil-pbc-curve-constructible-reduction`: `def-constructible-finite-locally-constant`, `def-weil-pbc-C7`, `def-weil-pbc-etale-cohomology`, `def-weil-pbc-etale-constructible-sheaf`, `def-weil-pbc-extension-pullback`, `def-weil-pbc-inverse-image`, `def-weil-pbc-torsion-etale-sheaf`, `lem-kun-03sa`, `lem-weil-pbc-five-lemma`, `lem-weil-pbc-inverse-image-composition`, `lem-weil-pbc-inverse-image-preserves-colimits`, `lem-weil-pbc-pullback-cohomology-long-exact-ladder`, `lemma-weil-pbc-curve-filtered-cohomology`, `prop-weil-pbc-inverse-image-exact`, `thm-constructible-serre`.

- `lem-weil-pbc-curve-dense-open-localization`: `def-constructible-constructible`, `def-constructible-finite`, `def-constructible-finite-locally-constant`, `def-constructible-stratification`, `def-weil-pbc-C1`, `def-weil-pbc-C2`, `def-weil-pbc-C3`, `def-weil-pbc-C4`, `def-weil-pbc-C5`, `def-weil-pbc-C6`, `def-weil-pbc-C7`, `def-weil-pbc-C8`, `def-weil-pbc-constructible-torsion`, `def-weil-pbc-curve-setting`, `def-weil-pbc-eight-curve-assertions`, `def-weil-pbc-etale-cohomology`, `def-weil-pbc-extension-by-zero`, `def-weil-pbc-extension-pullback`, `def-weil-pbc-geometric-stalks`, `def-weil-pbc-inverse-image`, `def-weil-pbc-primary-torsion`, `def-weil-scheme-morphism-properties`, `lem-weil-pbc-curve-assertions-dense-open`, `lem-weil-pbc-open-closed-short-exact`, `lemma-weil-pbc-geometric-stalk-conservative`.

- `lemma-weil-pbc-curve-dense-open-reduction`: `def-constructible-constructible`, `def-constructible-stratification`, `lemma-weil-pbc-curve-constructible-primary-reduction`, `lemma-weil-pbc-eight-curve-devissage`.

These are removals from the parent nodes' direct proof dependencies, not claims that
the nodes or their modules leave the target closure. Definitions remain in statements,
and some lemmas remain needed transitively by the new helpers or existing devissage.
The composition comparison, in particular, is used through `upperStarComp`.
The new PrimeConstructiblePullback module imports TopologicalInvariance, ZMod.Basic and
Algebra.Ring.ULift instead of Curve.Assertions; no curve assertion is needed in its signature.

## Where the brief, the DAG or earlier work was wrong

The existing dense-open assertion theorem uses CurveCoefficientPair with abelian sheaves
converted to ULift Z coefficients. It cannot be directly applied to these arbitrary
ModuleCat Λ signatures. The new dense-open statement records precisely this coefficient
transport specialization of Stacks 0GJA, rather than redefining any object.

The module changed during this session when an upstream devissage proof landed; the delivery
was refreshed against that file to preserve it. The unit sk-thm-p1 and its realized steps are
unchanged: the proof keeps the prescribed dense-open and componentwise reductions.
The attempted import of TorsionFilteredUnion was rejected by import_direction because it
reaches Reductions through HighDegreeVanishing; it was not added. The existing independent
TorsionSheafCharacterizations node supplies the needed torsion bridge.
The constructible colimit presentation has an index in Type(u+1), whereas the current
filtered-cohomology node is stated for Type u; handling this and the two constructibility
encodings remains explicit in PrimeConstructiblePullback, without weakening a signature.
The Stacks source was read from the available local copy of etale-cohomology.tex.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and direct source searches ran.

## New nodes

lem-pbc-q1-dense-irreducible-opens: geometric refinement of any prescribed dense open;
proved completely, with Noetherian finite components and a specialization dimension-drop
argument. Module: Sheaf.AlgebraicGeometry.Curve.DenseIrreducibleOpens.

lem-pbc-q1-dense-open-prime-assertions: the module-coefficient form of the specified-dense-open
comparison, source Stacks 0GJA. Module: Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions.

lem-pbc-q1-disjoint-open-prime-assertions: finite disjoint-open decomposition of the eight
conditional assertions, source Stacks 03SC fourth proof paragraph and 0A5C.
Module: Sheaf.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions.

lem-pbc-q1-prime-constructible-pullback: extends bijectivity from constructible prime-field
module sheaves to arbitrary abelian sheaves killed by the same prime for a fixed qcqs
morphism, source 03SA(3) and 03Q5. Module: Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback.
No definition or statement changes and no change records.


## Second reading by Q1

1. Interface preservation: PASS. Read the full diff against the repository. All 17 existing
   declaration signatures, including the private helpers, are unchanged; no definition,
   declaration docstring or existing public import changed. Only three proof bodies and
   ten proof imports were added. The concurrent upstream short-exact proof is preserved.
2. Proof and axioms: PASS, as reductions with open dependencies. All five delivered files
   compile locally in import order without warnings. Scratch copies with `#print axioms`
   checked every public theorem: the geometric helper uses only propext, Classical.choice
   and Quot.sound; the other declarations use only those plus sorryAx. The three old
   unproved theorems are unchanged, and exactly three new public named theorems have the
   whole proof `:= by sorry`. No hollow definition or prohibited trust escape was found.
   Thus the three original sorries are closed as reductions, not axiom-free target proofs.
3. Split statements: PASS. Read Assertions C1-C8 and the existing DenseOpenAssertions,
   ConstructibleModuleSheafColimit, KilledSheafModuleLift and prime-torsion devissage.
   Independently checked sources [0GJA](https://stacks.math.columbia.edu/tag/0GJA),
   [03SA](https://stacks.math.columbia.edu/tag/03SA),
   [03Q5](https://stacks.math.columbia.edu/tag/03Q5) and
   [03SC](https://stacks.math.columbia.edu/tag/03SC).
   The dense-open helper is the specified-open step without existential geometry;
   the disjoint-open helper needs neither density nor irreducibility; the fixed-prime
   helper has neither reduction nor field-extension geometry. None restates its parent.
   Each has a source, complete prose argument and matching node. Checked empty schemes,
   zero sheaves, the full and empty opens, n = 0, repeated empty opens and dimension-zero
   components; for conditional assertions checked characteristic zero, r equal to the
   positive characteristic, and r different from it. In a different-primary or exceptional
   invertible case the relevant r-torsion summand is zero, not an unsupported transfer of
   the coefficient condition back to F. In low-degree dense-open base change, first compare
   H0 of the extension as the kernel of H0(F) to the invariant boundary product; this then
   compares H1 through the five-term exact sequence in both directions.
   New LeanFinder search used cohomology invariance after dense-open extension by zero;
   Loogle searched PreservesFiniteBiproducts and found additive-functor preservation tools.
   Local rg searched bijective/constructible and disjoint/assertions in both orders.
   No existing theorem has the required arbitrary ModuleCat coefficient statement.
   The constructible approximation helper still needs its stated encoding and index-size
   bridges; the smaller-index continuity theorem alone cannot finish it in a few minutes.
4. Route and pruning: PASS after report repair. The parent proofs genuinely combine
   reduction geometry, functoriality and prime devissage, or generic constancy, the proved
   geometric refinement and the two comparison steps. This retains sk-thm-p1's prescribed
   constructible, dense-open and componentwise reductions; its realized fields are untouched.
   Checked proof-only imports are plain imports and imports of signature data are public.
   Narrowed the fixed-prime helper's public import from Curve.Assertions to the cohomology
   and coefficient modules actually needed. Added exhaustive old-minus-new direct
   proof-dependency lists under No longer needed; no whole-module pruning is claimed.
5. Node agreement: PASS. Checked all seven node records against the Lean declarations
   and actual arguments. Every proof_deps list equals the union of its step uses. Existing
   nodes change only proof, proof_deps and proof_origin; new nodes include source, searches,
   creation/provenance, chapter/unit and a verbatim Lean statement. No statement change
   record is necessary. The geometric node's proof is complete, rather than postponed.

Changes by the second reader: narrowed the import of PrimeConstructiblePullback and repaired
pruning/report completeness; no theorem signature, definition or mathematical proof changed.
