## What changed

Proved the body of AlgebraicGeometry.Scheme.Modules.picard_kunneth_cech_models from
an explicit scalar resolution model and two independent intermediate theorems.
Its signature, universe, visibility and hypotheses are unchanged. The statement
requires nonnegative cohomology models but does not require them to be literal
Cech complexes, so the chosen models are actual global sections of injective
resolutions, restricted to k and extended by zero. The geometric proof obligation
retains finite affine Cech covers, exact coefficient sequences, both dimension-shifting
inductions and the acyclic Leray base case of Stacks Tag 0BED.

New modules: PicardKunnethResolutionModel (no holes), PicardExternalCupCochain and
PicardExternalCupQuasiIso. The first explicitly constructs the complexes and their
scalar homology comparisons. The second asserts a normalized cochain realization
with no geometric hypotheses and no invertibility assertion. The third proves
invertibility for any specified normalized map, constructing no data. In the item,
gamma is built from asIso of homologyMap and the actual product model equivalence;
the final tensor-cycle formula is the normalization equation with the inverse factor
comparisons cancelled. This is a reduction, not a proof of the full geometric argument.

No new data definition selects a witness of an unproved mere existence theorem.
The normalized map is eliminated locally in the theorem proof. None of the library's
preexisting scalar comparisons or interfaces were changed. No forced adaptations.

Validation repeated after resuming the earlier attempt: all four modules compile in
import order with lcompile.py, without warnings (5.4, 3.6, 4.0 and 4.5 seconds).
The deliver3.py --no-push dry run printed OK; only the independent second reading
remains, as required by the brief. Nothing was pushed. The theorem signature was
compared verbatim with the repository version and is unchanged.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.Modules.picard_kunneth_cech_models
(node lem-sc-picard-kunneth-cech-models). Its complete proof uses the two new
obligations below. This is one upper hole decomposed into two lower holes, net -1
holes closed minus added, not a completed geometric Kunneth proof.

Fully proved/constructed, with no new holes:
AlgebraicGeometry.Scheme.Modules.picardScalarResolution,
picardScalarResolutionComplex, picardScalarModel, picardScalarModel_negative,
picardScalarModelEquiv (node lem-sc-picard-kunneth-resolution-model).
The model equivalence uses extendHomologyIso, exact scalar mapHomologyIso,
isoRightDerivedObj and ModuleCat.Iso.toLinearEquiv.

Every sorry added, and the only sorries in delivered modules:

- AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_exists
  (lem-sc-picard-external-cup-cochain): realize the bilinear external cup on the fixed
  vector-space complexes by a cochain map; no isomorphism clause.
- AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso
  (lem-sc-picard-external-cup-quasi-iso): geometric invertibility of the homology maps
  of any already specified cup-normalized cochain map.

Edge cases checked mathematically before stating: degree zero has only the (0,0)
tensor summand; zero coefficients or empty schemes give zero complexes up to their
canonical cohomology comparisons. The resolution may still have nonzero acyclic
terms, which causes no problem: vector-space acyclic parts are contractible. The
existence lemma requires neither compactness nor affine diagonal; splitting and
cochain realization work for arbitrary vector-space dimensions. The invertibility
lemma assumes quasi-compactness and affine diagonal exactly where its affine-cover
and dimension-shifting argument uses them. Arbitrary choices of the cochain map
cannot affect its homology map, since the algebraic tensor Kunneth cycle formula
shows that the specified tensor-cycle classes span.

## No longer needed

The item no longer directly imports:
Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural,
AffineOpenModuleCohomologyVanishing, LerayDegenerateSections,
ModuleCechComparisonIsoAffine, ModulePullbackAffineSections,
QcqsCohomologyDirectSum, QuasiCoherentTensorProductAffineSections,
QuasicoherentAcyclicEmbedding, QuasicoherentFiniteCohomologicalDimension,
TensorPullback, Sheaf.Paper.CechComparisonMapNaturality,
Sheaf.Paper.CechCupPullbackCompat and Sheaf.Paper.HigherDirectImagePresheaf.
Its sole proof import is PicardExternalCupQuasiIso, which publicly provides the two
other new interfaces. All geometric dependencies above except the redundant direct
TensorPullback import move to the geometric intermediate module's proof plan:
no geometric module is claimed pruned from the targets' closure. TensorPullback
still enters via the field-linear operations used by the statement.

No existing node is globally made unnecessary. The parent node now directly depends
on the three new nodes. The original geometric dependencies remain below the new
invertibility node; the field-linear TensorKunnethNat node is also needed there.
All original public imports of the item remain, preserving its exported interface.

The following old parent proof_deps are no longer direct dependencies (each remains
in the geometric intermediate plan or its statement dependencies; none is globally pruned):

- def-pc-fibre-product
- def-pc-module-pullback
- def-pc-scheme
- def-sc-field-linear-module-cohomology-operations
- lem-pc-leray-degenerate-sections
- lem-sc-cech-comparison-map-iso-affine
- lem-sc-cech-comparison-map-naturality
- lem-sc-cech-comparison-natural
- lem-sc-picard-affine-diagonal-intersections
- lem-sc-picard-cech-cup-pullback-compat
- lem-sc-picard-qcoh-finite-cd
- lem-sc-picard-qcoh-universal-delta-embedding
- lem-weil-pbc-fibre-product-affine-spectra
- lem-weil-pbc-higher-direct-image-presheaf
- lem-weil-pbc-module-pullback-affine-sections
- lem-weil-pbc-qcqs-cohomology-direct-sum
- lem-weil-pbc-quasi-coherent-tensor-product-affine-sections
- pqf-def-coherent
- pqf-lem-affine-vanishing

## Where the brief, the DAG or earlier work was wrong

The planned dependencies provide individual affine comparisons and cup/refinement
formulas, not the missing geometric tensor-total comparison or a cochain map on the
fixed scalar resolution models. They cannot directly close the existential theorem.
The new lemmas make those missing parts explicit instead of moving the entire theorem
under another name. The scalar resolution construction uses the ordinary recorded
module cohomology, with exact restriction of scalars, rather than an unrelated
abelian-sheaf cohomology encoding.

The literal Cech route in the original docstring was stronger than the existential
statement's requirement. The updated proof documentation records the delivered
resolution models while preserving the geometric Cech proof of invertibility.
The cube unit has empty realized arrays and its route is unchanged.

The local literature/stacks-project/varieties.tex is absent on this machine;
the source was read on the official Stacks page https://stacks.math.columbia.edu/tag/0BED.
The official Tag 0BED source was read again during this continuation: its finite
affine covers, coefficient exact sequences, two inductions and acyclic Leray case
agree with the new invertibility obligation.
LeanSearch was unavailable on the recorded attempts. The recorded verdict is
unavailable, with no claim of absence inferred; Loogle, LeanFinder and Mathlib/source
grep supplied the other searches. No statement dispute or source error found.

## New nodes

lem-sc-picard-kunneth-resolution-model records the explicit scalar sections resolution,
zero extension, negative-term vanishing and canonical scalar cohomology equivalence.
It has no sorry. Its Lean record lists all five constructed/proved declarations.

lem-sc-picard-external-cup-cochain records only cochain realization and normalization
on tensor cycles. It has no invertibility clause or geometric compactness hypotheses.
Its proof describes the scalar resolution pairing and the vector-space splitting lift.

lem-sc-picard-external-cup-quasi-iso records only geometric invertibility of a given
normalized map. Its proof retains the source's exact-sequence induction and acyclic
Leray argument and uses algebraic tensor Kunneth to identify any normalized map.

All three nodes inherit sec-abelian-varieties / sk-prop-av-cube and the nearest blueprint
ancestor thm-sc-theorem-of-cube. Searches of the full blueprint for Kunneth and homology
found no duplicate of these scalar resolution interfaces. No change records are needed:
all existing signatures and definitions are unchanged.

## Second reading by F4

1. Compared every delivered module with the repository: only PicardKunnethCechModels
   existed. Its complete theorem signature is byte-for-byte identical, its original
   public imports are preserved, and there is no definition or statement change.
   The other three modules are new. Verdict: pass; no change record is required.
2. Independently compiled all four modules in import order with lcompile.py, cleanly
   (4.4, 2.9, 3.0 and 4.2 seconds). A scratch-copy axiom probe checked all ten new
   or changed declarations. The five resolution declarations and picardExternalTotal
   use only propext, Classical.choice and Quot.sound. The normalization predicate,
   both split theorems and the parent additionally use sorryAx from the recorded
   open interfaces. Exactly the two reported public named theorems contain sorry;
   no forbidden declarations or hollow definitions occur. The enough-injectives
   theorem used for resolution data is proved upstream, and the axiom probe confirms
   that these model definitions do not depend on sorryAx. Verdict: pass as a
   decomposition, not as an axiom-complete geometric proof.
3. Read both new theorem statements and their full docstring arguments. Cochain
   realization needs only the graded bilinear cup map and vector-space splitting;
   invertibility is a separate assertion about a given normalized map. Neither
   simply renames the parent's existential assertion. Checked degree zero, empty
   schemes, zero coefficients, infinite dimensions and characteristic two: finite
   tensor summands in natural degree and signed contractions cover these cases.
   Independently searched LeanFinder for lifting a homology linear map to a chain
   map, Loogle for homologyMap, and the upstream, Mathlib and Sheaf sources for
   homology lifting, splitting and external products. Existing single-cohomology
   contraction and algebraic tensor Kunneth results do not give either geometric
   obligation. No short proof of either hole was found. Verdict: pass.
4. Read the proof from its constructed models down to the two obligations and the
   final normalization application. Proof imports are plain import; public imports
   supply signatures or exposed definitions. Re-read the official Stacks Tag 0BED
   proof (https://stacks.math.columbia.edu/tag/0BED): the geometric obligation retains
   its finite affine covers, exact sequences, two inductions and Leray base case.
   The cube unit's empty realized arrays are unchanged, and no unit route is bypassed.
   Expanded No longer needed to name every removed old direct proof dependency;
   none of these modules is globally pruned. Verdict: pass.
5. Checked the four node records against the Lean declarations, their proof steps
   and the exact union of step uses with proof_deps. Existing node changes are only
   proof, proof_deps and proof_origin. New nodes carry source, statement dependencies,
   searches, creation, blueprint, chapter, unit and Lean records; the two holes have
   matching nodes and complete natural-language proofs. Verdict: pass.

Second reading changed only this report: explicit old direct dependency enumeration
and the independent review and axiom results. No Lean or DAG repair was needed.
Holes closed: picard_kunneth_cech_models (one). Holes added:
picardExternalCupCochain_exists and picardExternalCupCochain_isIso (two).
Net holes closed minus added: -1; no module globally pruned.
