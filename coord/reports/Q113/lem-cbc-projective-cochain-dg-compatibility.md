## Worker report

The module `Sheaf/CategoryTheory/ProjectiveCochainDgCompatibility.lean` states
`HomotopicalAlgebra.projectiveCochainDgCompatibility`.  It introduces the
structure `ProjectiveCochainDgCompatibility R` and postpones exactly its
existence theorem with `sorry`.

The ring hypothesis is `(R : Type u) [CommRing R]`.  Its `model` field is the
recorded `HomotopicalAlgebra.ProjectiveCochainMonoidalModel R`, so it retains
the unbounded cochain category, quasi-isomorphisms, termwise surjections,
dg-projective cofibrations, generators, closed symmetric monoidal structure,
cofibrant unit, and pushout-product clause from
`Sheaf.CategoryTheory.ProjectiveCochainMonoidalModel`.  The `enriched` field
uses `CategoryTheory.QuillenSections.Complex.{u}` (unbounded complexes of
abelian groups) and the category
`CochainComplex (ModuleCat.{u} R) ℤ`.  The `dg` field is the recorded
`CategoryTheory.QuillenSections.DgModel` at those two instances; it supplies
completeness, cocompleteness, combinatorial generation, tensor/cotensor
universal properties, and the enriched model compatibility axiom.

The `tensor_formula` field quantifies over every abelian-group complex `T`,
module complex `A`, and degree `n : ℤ`.  After forgetting the induced
`R`-module structure to abelian groups, the degree `n` of the tensor is
isomorphic to the direct sum over all `p : ℤ` of
`TensorProduct (ULift ℤ) (T.X p).carrier (A.X (n-p)).carrier`; this is the
stated direct-sum total and includes all integer degrees.  The
`cotensor_formula` field similarly identifies degree `n` with the product
family of additive homomorphisms
`∀ p, T.X p →+ B.X (p+n)`, the product-total Hom formula.

The `first_adjunction` field is the first displayed complex adjunction.  Its
left side is the underlying abelian-group complex of the module Hom complex
from `tensor T A` to `B`; its right side is the abelian-group HomComplex from
`T` to the underlying complex of `moduleHomComplex A B`.  The
`second_adjunction` field identifies the same left side with the underlying
module Hom complex from `A` to `cotensor T B`.  Both are `Nonempty` of actual
complex isomorphisms, so they retain the natural complex-level adjunctions;
no degree or boundedness restriction is introduced.

For every module-complex pair `i : A ⟶ B` and `p : X ⟶ Y`,
`hom_comparison` assumes exactly `ProjectiveCochainCofibration R i` and
`ProjectiveFibration R p`.  It supplies a target complex `T` and the enriched
map `h : (B ⟶[Complex] X) ⟶ T` satisfying `IsHomComparison i p h`, whose
pullback legs are the pre- and post-composition maps.  The comparison is
surjective in each degree.  Each of the two alternatives is stated
separately: a quasi-isomorphism `i` implies `QuasiIso h`, and a
quasi-isomorphism `p` implies `QuasiIso h`.  Finally the enriched Hom from
`coker i` to `ker p` is isomorphic to `kernel h`, rendering the natural kernel
identification.  The theorem conclusion is exactly
`Nonempty (ProjectiveCochainDgCompatibility R)`.

The statement dependencies used are:

* `Sheaf.CategoryTheory.ProjectiveCochainMonoidalModel`, declarations
  `HomotopicalAlgebra.ProjectiveCochainMonoidalModel`,
  `HomotopicalAlgebra.ProjectiveCochainCofibration`, and
  `HomotopicalAlgebra.ProjectiveFibration`;
* `Sheaf.CategoryTheory.DgQuillenDiagram`, declarations
  `CategoryTheory.QuillenSections.Complex`, `TensorCotensor`, `DgModel`, and
  `IsHomComparison`;
* `Sheaf.CategoryTheory.QuillenSectionRectification`, imported for the
  statement dependency `lem-coef-quillen-section-rectification` and its
  `CategoryTheory.QuillenSections.quillenSectionRectification` declaration;
* `DerivedCategory` from Mathlib's
  `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean` is the exact
  `mathlib_match` for `def-weil-abstract-derived-category`; no replacement
  definition is introduced.

I checked the empty and unbounded cases explicitly: the sums and products
range over all `p : ℤ`, so no boundedness or finite-index assumption is hidden;
`n = 0` gives the ordinary degree-zero tensor/Hom formulas; the zero complex
and zero ring are permitted by `[CommRing R]`; and the comparison clauses do
not require either map to be a quasi-isomorphism unless that alternative is
invoked.  The `coker`/`ker` field is stated for arbitrary cofibration and
fibration maps and therefore includes zero maps and zero kernels.

Searches for an existing declaration were made before writing the module:

* `msearch.py ... leanfinder "The projective model structure on unbounded
  module complexes is enriched, tensored and cotensored over abelian-group
  complexes"` returned K-projective and ordinary projective-resolution
  declarations but no mixed-coefficient dg compatibility;
* `msearch.py ... loogle "CochainComplex, ModelCategory"` returned no exact
  `ModelCategory` declaration (only generic model-category results);
* `msearch.py ... grep "dg.projective|dg.?model|projective.*model|model.*projective|enriched.*complex" Algebra/Homology`
  found only generic model-category/K-projective files and no exact statement;
* `rg -n` over `WeilConjectures/` and the shared `lean/Sheaf/` tree for
  `projective-cochain-dg`, `ProjectiveCochainDgCompatibility`, and the
  mixed tensor/cotensor formulas found no existing declaration;
* `grep -rl` over `dag/nodes/` found only this node and its recorded
  dependencies, with no duplicate notion.

The node's recorded searches (LeanSearch, LeanFinder, Loogle, and Mathlib
`grep`) likewise all report no exact match.  No `STATEMENT-DISPUTED` flag or
node fault was found.

## Second reading by Q113

I reopened the node, its source place, all three statement dependencies, and
the delivered module.  The ring, commutative-ring instance, unbounded
integer-indexed complexes, and the projective model are all present.  The
`tensor_formula` and `cotensor_formula` each quantify over every degree and
show the direct-sum/product total; the two adjunction fields have the exact
three Hom-complex objects in the node's displayed chain.  The comparison
field retains both cofibration/fibration hypotheses, the pullback
`IsHomComparison` condition, degreewise surjectivity, both independent
quasi-isomorphism alternatives, and the coker/ker kernel isomorphism.  I
found no mismatch and made no changes in this second reading.  The module
compiled cleanly with `scompile.py`; the only postponed proof is the theorem
specified by the node.

## Repair of returned delivery

The returned review identified that an arbitrary enrichment left the Hom
objects and composition unspecified.  The module now defines
`moduleHomComplexAb`, the restriction of `CochainComplex.moduleHomComplex` to
the `ULift ℤ` coefficient complex, together with the concrete degree-zero
elements `moduleHomCochainAb` and `moduleHomCochainCompAb`; the latter is
defined by `Cochain.comp` on `Cochain.ofHom` values.  The compatibility package
has fields `enriched_hom`, `enriched_comp_cochain`, and
`enriched_eHomEquiv_ofHom` which identify the enrichment Hom objects and its
degree-zero composition and ordinary-map equivalence with these canonical
constructions, using equality transports.  Thus `dg` and the comparison
clauses refer to the specified product-total module Hom complex rather than an
arbitrary enrichment.  The tensor and cotensor formulas remain the explicit
all-degree direct-sum and product totals, with the module model and its induced
`R`-actions supplied by `dg.tensors`.

## Maintainer review fix (stage-2 second reader, 2026-10-18, head 841ca22)

The repaired `enriched_comp_cochain` fixed enriched composition only on
degree-zero cochain maps. That case already follows from the Mathlib axiom
`EnrichedOrdinaryCategory.homEquiv_comp`, `enriched_eHomEquiv_ofHom` and
`Cochain.ofHom_comp`, so `eComp` was still unconstrained in nonzero degrees. The
legs `eHomWhiskerRight i X` and `eHomWhiskerLeft B p` of `IsHomComparison`, and the
universal properties in `dg.tensors`, all use `eComp` in every degree.

Fixed:

* `enriched_comp_cochain` now fixes `eComp` on every summand
  `Hom^n(A,B) ⊗ Hom^m(B,C)`, through `HomologicalComplex.ιTensorObj`, as
  `moduleHomCochainCompAb R f g = (-1)^(n*m) • Cochain.comp f g`. The sign is
  forced by two Mathlib conventions:
  * the total tensor for `up ℤ` has `ε₂(p,q) = (-1)^p`;
  * `δ_comp` gives `δ(f.comp g) = f.comp δg + (-1)^m (δf).comp g`.

  A composition of the form `s(n,m) f.comp g` is therefore a chain map exactly when
  `s(n+1,m) = (-1)^m s(n,m)` and `s(n,m+1) = (-1)^n s(n,m)`. With `s(0,0) = 1`
  this gives `s = (-1)^(nm)`. That composition is associative, since both
  bracketings carry `(-1)^(nm+nk+mk)`, and unital. It is the Stacks composite
  `g ∘ f` (Tags 0A8H, 0A8I) after the Koszul symmetry, and in degree `(0,0)` it is
  the previous clause.
* The kernel clause now uses the canonical map: there is
  `e : (coker i ⟶[Complex] ker p) ⟶ kernel h` with `IsIso e` and
  `e ≫ kernel.ι h = eHomWhiskerRight (cokernel.π i) (kernel p) ≫ eHomWhiskerLeft B (kernel.ι p)`,
  which is `w ↦ ι ∘ w ∘ π` (proof step 4). Before, it was a bare `Nonempty`
  isomorphism.
* The helpers `moduleHomComplexAb`, `moduleHomCochainAb` and
  `moduleHomCochainCompAb` have docstrings with their source and blueprint id, and
  `lean.declarations` lists them.

Hom objects, composition and `eHomEquiv` now determine the enrichment. The
`TensorCotensor` universal properties in `dg.tensors` (enriched
representability, tested by every complex `L`) then fix the tensor and cotensor
as R-module complexes up to unique isomorphism, and they give the node's
natural complex adjunctions. The degreewise formula fields and the two
adjunction fields stay as supplementary descriptions. The theorem signature,
and so `lean.statement`, is unchanged. `tools/nt_compile.py --json` compiles the
fixed file cleanly in 10.9 s.
