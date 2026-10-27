## Worker report

The module `Sheaf.AlgebraicGeometry.SemilocalSubringAffineGluing` states
`AlgebraicGeometry.exists_semilocal_subring_affine_gluing`, with its only proof `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The accepted Q80 stage-1 split is preserved. The inherited BLOCKED message concerned
that split, not the present stage-2 statement; the stage-handoff paragraph of the
current brief explicitly permits this delivery. The sandbox initially contained
only dispatcher brief markers, no retained mathematical files.

Hypothesis and conclusion correspondence:

- The field is `{K : Type u} [Field K]`, with its universe explicitly declared.
- The positive finite number of rings is `(r : ℕ) (hr : 1 ≤ r)`; the indexed unital
  subrings are `(A : Fin r → Subring K)`. This gives exactly r charts, with no empty case.
- Fraction field K for each given inclusion is `[∀ i, IsFractionRing (A i) K]`;
  the ambient-subring algebra instances use the actual inclusions into K.
- Noetherianity is `[∀ i, IsNoetherianRing (A i)]`.
- Semilocality is `[∀ i, Finite (MaximalSpectrum (A i))]`, literally finitely many
  maximal ideals, without an additional predicate or finiteness of the prime spectrum.
- Exact dimension one is `hdim : ∀ i, ringKrullDim (A i) = 1`.
- Pairwise independence is `hsurj : ∀ i j, i ≠ j → Function.Surjective (...)`.
  The map is Mathlib's `Algebra.TensorProduct.productMap` of
  `IsScalarTower.toAlgHom ℤ (A i) K` and `IsScalarTower.toAlgHom ℤ (A j) K`.
  The inspected lemma `productMap_apply_tmul` says precisely a tensor maps to the product
  of its two images in K. The base is ℤ, not an unspecified common coefficient field.
- The existential `(R : Subring K) (hRA : ∀ i, R ≤ A i)` is the requested subring
  contained in every chart. No equality with the full intersection is added to the statement.
- Its five algebraic properties are the conjunction `IsDomain R`, `IsNoetherianRing R`,
  `Finite (MaximalSpectrum R)`, `ringKrullDim R = 1`, and `IsFractionRing R K`.
- Each open immersion is `Spec.map (CommRingCat.ofHom (Subring.inclusion (hRA i)))`.
  The maps are specified by the inclusions, not chosen independently.
- The covering is pointwise: every `x : Spec (CommRingCat.of R)` lies in the range of
  one of these same maps. For open immersions this is exactly an open covering.
- Closed-point uniqueness is `IsClosed {x} → ∃! i, x ∈ Set.range (...)`, with x
  an actual scheme point. Both existence and uniqueness are present.
- The local conclusion is conditional on `∀ i, IsLocalRing (A i)`, quantified as
  a local instance binder; it is not an extra assumption on the semilocal theorem.
- Its family `m : Fin r → MaximalSpectrum R` has both `Function.Injective m` and
  `Function.Surjective m`, expressing distinctness and exhaustion of closed points.
- The image equality takes the maximal ideal `IsLocalRing.maximalIdeal (A i)`
  under the specified chart map to the point with ideal `(m i).asIdeal`.
- For each i the ring equivalence `Localization.AtPrime (m i).asIdeal ≃+* A i`
  satisfies, for every `x : R`, that its value on `algebraMap R ... x` equals
  `Subring.inclusion (hRA i) x`. Thus it is the identification induced by the
  inclusion, not an unrelated abstract ring isomorphism.
- For distinct i,j, `IsPullback` has upper left object `Spec K`, projections
  `Spec.map (CommRingCat.ofHom (A i).subtype)` and the corresponding map for j,
  and bottom/right arrows the same chart inclusions. The Cartesian-square assertion
  says the intersection open subscheme is canonically Spec K, with exactly the
  specified maps to both charts. It includes the scheme structure, not only a set equality.

Statement dependencies read and used:

- `def-weil-field`: Mathlib `Field`, signature and docstring in
  `Mathlib.Algebra.Field.Defs`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and its all-ideals-finitely-generated characterization.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, the dimension of the prime-ideal order in `WithBot ℕ∞`.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; its ring-map API is imported by
  `Mathlib.RingTheory.TensorProduct.Maps`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, available through
  the public open-immersion import.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.

Other existing notions used directly are `Subring`, `MaximalSpectrum`,
`IsFractionRing`, `Localization.AtPrime`, `IsLocalRing`, and `CategoryTheory.IsPullback`.
The localization dependency is recorded as `Mathlib.RingTheory.Localization.AtPrime.Basic`;
its `Localization.AtPrime` and `IsLocalization.AtPrime` signatures were read.
The proof's already stated dependencies have non-public imports:
`Mathlib.AlgebraicGeometry.FunctionField` supplies
`StructureSheaf.IsLocalization.to_stalk` (from StructureSheaf) and
`functionField_isFractionRing_of_affine`; `Mathlib.AlgebraicGeometry.Noetherian`
supplies `IsLocallyNoetherian`, `isLocallyNoetherian_of_affine_cover`, and
`IsLocallyNoetherian.component_noetherian`. These were read with their signatures and
source documentation. The common-DVR criterion and the two-ring intersection-cover
node have no Lean record or Mathlib match in the read snapshot; they are proof
prerequisites only, so no nonexistent module is imported. Nothing in the statement
requires their as-yet-unstated conclusions.

Sources checked: `literature/stacks-project/varieties.tex`, Tag 09N4, statement and
proof, its preceding two-ring lemma Tag 09N3, and Tag 09NJ, especially the displayed
covering, the exactly r maximal ideals, the localization identifications, and Spec K
overlaps. The theorem retains all clauses of the accepted node and needs no correction.

Edge cases checked: r=1 admits the given ring with the identity chart; its overlap
condition is vacuous. r=0 is excluded exactly by hr, as the node requires. A chart
cannot be a field because its dimension is exactly one; in particular the closed
point and generic point are different. Repeated identical charts for distinct indices
cannot satisfy the tensor-surjectivity hypothesis: their image is the proper chart
subring, not K. The rings ℤ localized at two distinct primes in ℚ illustrate the local
case; their generic overlap is Spec ℚ. Nonlocal semilocal charts retain the first
cover/unique-closed-point conclusions without imposing the local consequences. No
characteristic restriction, field cardinality restriction, or extra universe equality
is present. All variables and universes are explicitly bound.

Existing-statement searches (2026-10-23):

- msearch.py leanfinder, `Independent Noetherian semilocal subrings of a common fraction
  field of dimension one glue to an affine scheme covered by their spectra`: eight
  results, including `Scheme.affineBasisCoverOfAffine`, `Spec`, `isAffine_Spec` and
  `Scheme.affineOpenCoverOfSpanRangeEqTop`; none gives the semilocal gluing theorem.
- msearch.py loogle, `"Subring", "IsLocalization"`: one valuation-subring localization
  instance, not a gluing statement.
- msearch.py grep, `semilocal|semi.local|glue.*subring|intersection.*noetherian`,
  Mathlib RingTheory: fourteen results, mainly local properties and filtration;
  no affine gluing of independent subrings.
- msearch.py leansearch, `Independent one dimensional Noetherian semilocal subrings
  of a field glue to an affine scheme whose closed points belong to exactly one chart`:
  eight general affine, gluing and locally Noetherian results, no exact match.
- rg of the same concept in the project `lean/WeilConjectures` and `lean/Sheaf`
  found normalization/conductor material, Jacobson-denominator results and general
  gluing. In particular the read `exists_inv_mem_jacobson_of_tensor_surjective`
  gives a denominator, not this affine gluing, and illustrates the existing
  canonical tensor-product map. Searching the item's blueprint id upstream and
  `semilocal_subring_affine_gluing|semilocal.*gluing|glue_a_bunch` across Mathlib
  and both project source roots found no existing statement. The proposed full
  declaration name also has no match in those sources or `dag/lean_names_upstream.json`.

Validation: scompile.py compiled the delivered file in both sandbox and library module
modes against the published live build, with no errors or warnings (1.6 s and 1.8 s).
The node changes only `lean`, with the exact verbatim theorem signature and UTC date.

## Second reading by Q98

A separate clause-by-clause rereading was performed in this worker session with the
node, source paragraphs and final file open. No second agent was started, as the
assignment explicitly forbids it; the maintainer's independent review remains the
independent reading. The rereading checked that `Fin r` and hr retain r≥1, the tensor
base is ℤ, the output subring is merely contained in all charts, and that the local
case is conditional. It checked the closed-point images against the maximal-ideal
constructors, the localization equation against the inclusion map, and the order of
all four arrows in `IsPullback` against Spec K → Spec A_i → Spec R. The last clause
is the full scheme intersection, not just the common generic point. No mismatches
were found and no statement clauses were added or dropped.
