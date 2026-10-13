## What changed

Replaced the proof hole of `AlgebraicGeometry.koszulExtCoefficient_stalk_model`
with a compiling composition of two strictly separate steps. The original
statement, binders, universes and public imports are unchanged.

`Sheaf.AlgebraicGeometry.KoszulExtCoefficientAffineModel` states the affine
sheaf-level derived coefficient square, before taking any stalk or tensor
pullback. `Sheaf.AlgebraicGeometry.AffineModelTensorPullbackStalk` states a
natural family of tensor stalk identifications for arbitrary sheaves equipped
with affine tilde models. This general lemma has no derived category, Koszul,
closed immersion, flatness or finiteness hypotheses. The main proof takes the
sheaf isomorphisms from the first step and uses the naturality of the second
step on the resulting square. It constructs no definitions by choosing data
from an unproved existence statement.

The two new modules and the unchanged main signature compile together with
lcompile.py. The intermediate statements were checked mathematically at
length zero, m greater than n, and zero modules. The point hypothesis in the
stalk theorem excludes an empty chart at the chosen point. No global library
build was run.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.koszulExtCoefficient_stalk_model` (node
`new-j3-koszul-ext-coefficient-stalk-model`) by a complete Lean proof FROM the
two intermediate declarations. There are no direct sorries left in the item.

Added two holes, each the whole proof of a public theorem in its own module:

- `AlgebraicGeometry.koszulExtCoefficient_affine_model`, node
  `new-k1-koszul-ext-coefficient-affine-model`.
- `AlgebraicGeometry.exists_affine_model_tensorPullback_stalk`, node
  `new-k1-affine-model-tensor-pullback-stalk`.

This is a decomposition: one upper hole closed and two lower holes added,
net minus one, rather than an independent proof of the full stalk model.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.RingTheory.KoszulProjectiveResolution`
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`
- `Mathlib.LinearAlgebra.ExteriorPower.Basis`
- `Sheaf.Algebra.Homology.ModuleStalkExact`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransport`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings`

The resolution and Hom proof-dependency nodes are retained in the affine
statement. The geometric statement uses the existing assembled natural
`lem-weil-pbc-module-stalk-pullback`, which itself uses inverse-image and
change-of-rings comparisons. The new modules import their planned proof
dependencies privately, so moving this work does not discard those dependencies. The exact-stalk route is replaced in the affine step by the already
proved `lem-sc-tilde-preserves-finite-limits`; affine tilde localization is the
existing Mathlib leaf `lem-weil-pbc-spec-tilde-stalk-localization`. They are not
claimed as mathematically unnecessary modules. No unit statement or realized
unit step was bypassed. No whole mathematical dependency is claimed pruned.
The main node now records exactly the two declarations used by its Lean proof.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's missing
`Sheaf.RingTheory.KoszulQuotientCoefficientComplex.olean` was reproducible.
A temporary unchanged copy of that source in the sandbox allowed compilation;
the designated compiled library has since acquired its olean, so the temporary
copy was removed from this delivery. No tooling was changed or bypassed.

The planned derived Hom and restriction lemmas give object comparisons, but
the required simultaneous natural coefficient square is additional glue. The
first intermediate theorem states precisely this affine sheaf-level glue.
The second records the general geometric transport and its naturality,
independently of the derived calculation. Existing affine scalar Ext and
Koszul Hom coordinate comparisons were read: they identify one coefficient
object and do not themselves state this two-coefficient natural square.

## New nodes

`new-k1-koszul-ext-coefficient-affine-model` is the affine sheaf coefficient
square. It contains the resolution, finite free derived Hom computation and
exact sheafification part of the original plan. Its docstring and node explain
how to preserve coefficient naturality and the supplied derived universe.

`new-k1-affine-model-tensor-pullback-stalk` is the general natural tensor
stalk comparison for affine tilde models. Its proof plan combines affine
localization, inverse-image scalar transport, change-of-rings stalks and tensor
associativity. Both nodes are in `dag/nodes/sec-picard-framework/`, use the
original unit, and record executed searches and exact Lean signatures.

No change record or forced adaptation is needed: existing interfaces remain
identical and only new theorem modules are added.


## Second reading by K1

1. Compared the delivered item with the repository using diff. The complete
   existing theorem signature, universes, binders, docstring and public imports
   are byte for byte unchanged. Only its proof and private proof imports changed.
   The other two Lean modules contain new statements only; no existing definition
   or target statement changed, so no change record is required. Verdict: pass.
2. Read all three modules. The main proof obtains the affine coefficient square
   and applies the natural tensor stalk family to it. The only direct holes are
   the two named public theorems listed above, each exactly `:= by sorry` with a
   source, proof docstring and node. No definitions or arbitrary witness choices
   were added; existential witnesses are eliminated only within this proposition
   proof. No prohibited declaration or axiom escape is present. All three modules compiled with lcompile.py without errors or warnings.
   A scratch copy with explicit #print axioms for all three declarations also
   compiled: each lists only propext, Classical.choice, Quot.sound and sorryAx.
   The scratch copy was removed. Verdict: pass; this remains a decomposition,
   not an axiom-free proof of the original theorem.
3. Checked the affine comparison against Stacks Tag 0BQZ and the tensor stalk
   formula against Tag 01BH(3). For n=0, hf makes I zero and both complexes are
   degree-zero coefficients with identity reduction. For m>n exterior terms and
   both homologies vanish. An empty affine chart gives the zero sheaf category;
   in the geometric statement hzU excludes that chart. Zero modules give zero
   tensors. No flatness is needed for ordinary pullback stalks, and no exactness
   of tensoring with R is asserted. The two statements separate a derived
   sheaf calculation from a general underived natural comparison; neither is
   the original statement under a new name. Independent LeanFinder searches
   used "Naturality of extension of scalars of a sheaf stalk, and localization
   of the associated module" and "Cohomology sheaf of internal Hom from a finite
   locally free resolution and functoriality in the second variable". Read
   Mathlib restrictStalkNatIso, tilde stalk localization, the existing tensor
   pullback stalk theorem, affine_koszul_scalar_ext_comparison and
   affine_koszul_hom_coordinates. None states either assembled square. The
   scalar comparison supplies only one object, not coefficient naturality.
   Closing either remaining hole needs substantial composition of these APIs,
   beyond a short repair. Verdict: valid decomposition; two holes remain.
4. The shortest geometric plan now uses the existing natural
   exists_tensorPullback_stalk_iso rather than reconstructing that theorem.
   All new proof dependencies are private imports; public imports serve
   statement syntax or stalkLinearMap. The unit sk-thm-picard-duality has
   realized.statement = [] and realized.steps = [[]]; neither changed. This
   is below the unit level and preserves its route. The former main proof_deps
   are accounted for: new-j3-koszul-projective-resolution,
   lem-sc-affine-quotient-resolution-sheafification,
   lem-weil-pbc-exterior-power-free-basis,
   lem-sc-derived-internal-hom-restrict-open,
   lem-sc-derived-hom-finite-free-model and
   new-j3-koszul-quotient-coefficient-complex remain in the affine plan;
   lem-pc-ringed-inverse-image-stalk-scalar-transport and
   lem-weil-pbc-stalk-change-of-rings-tensor are used through the existing
   tensor stalk theorem; lem-weil-pbc-module-stalk-exact is replaced here by
   exact tilde. None is a direct proof dependency of the main proof anymore.
   No whole module is claimed pruned. Verdict: pass.
5. The main node lists exactly the two theorem applications in its proof.
   Both new nodes have matching verbatim Lean signatures, sources, complete
   proof plans, search records, chapter/unit and creation records. Corrected
   the geometric node's proof and proof_deps to use the existing assembled
   tensor stalk comparison. The affine node retains its actual planned
   resolution, Hom and exact tilde dependencies. Verdict: pass.

Changed in the second reading: added private imports for the new statements'
planned dependencies; shortened the geometric proof plan using the existing
natural tensor stalk comparison; clarified the affine docstring's signs,
integer/natural degree comparison and exactness justification; corrected the
pruning account. No theorem signature or main proof term was changed.
