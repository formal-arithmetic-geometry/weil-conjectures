## Worker report

The module `Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel` states
`CochainComplex.projective_hom_evaluation_model`, whose conclusion is the existence
of `CochainComplex.ProjectiveHomEvaluationModel R`. This structure packages the
maps and equations of this node, rather than choosing an unnormalized isomorphism.
The only postponed proof is the named main theorem; the structure declaration has
real fields and no sorry. There is no choice of data from the postponed theorem.
The node's natural-language statement, dependencies and proof remain unchanged.

Hypotheses and clauses, read against the node:

- Commutative ring: `(R : Type u) [CommRing R]`.
- Cochain complexes: every `P`, `P'`, `N` and `N'` is a
  `CochainComplex (ModuleCat.{u} R) ℤ`.
- Bounded above: `∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)`.
  The naturality comparison uses the same condition on its second admissible
  source `P'`. No bound is imposed on either target.
- Projective in each degree: `∀ i : ℤ, Module.Projective R (P.X i)`.
  There is no `Module.Finite` or free-module assumption.
- Localization into D(R): `DerivedCategory.Q`, with the explicit size convention
  `[HasDerivedCategory.{u} (ModuleCat.{u} R)]`. This is a choice of the existing
  locally small localization, not a mathematical restriction on R or its modules;
  the imported Grothendieck infrastructure constructs this localization. The
  common universe u can contain an arbitrary ring and arbitrary module complexes.
- Product Hom complex and its differential: the recorded
  `CochainComplex.moduleHomComplex P N`, whose terms are the full homogeneous
  cochains and whose differential is `HomComplex.δ_hom`. Its components are all
  maps P^p -> N^(p+q), with differential d_N z - (-1)^q z d_P. No finite product
  or direct sum replaces this product.
- Left derived tensor and right adjoint: the imported K-flat monoidal structure
  on `DerivedCategory (ModuleCat R)` and its closed structure. `ihom (Q.obj P)`
  is exactly the right adjoint to `tensorLeft (Q.obj P)`, with counit `ihom.ev`.
  The chain-level `internalHomObj` with its different sign convention is not
  substituted for the node's ordinary Hom complex.
- Canonical Hom comparison is an isomorphism: the field `comparison` has type
  `Q.obj (moduleHomComplex P N) ≅ (ihom (Q.obj P)).obj (Q.obj N)`.
  It is normalized by `counit_eq`: its adjunction transpose is the canonical
  tensor-localization comparison followed by the localized signed evaluation.
  Adjunction injectivity fixes the comparison uniquely.
- Naturality: `homMap_apply` specifies precomposition by `a.f p` and
  postcomposition by `b.f s` in every degree. `comparison_naturality` identifies
  its localization with `MonoidalClosed.pre (Q.map a)` followed by
  `(ihom (Q.obj P')).map (Q.map b)`. Here `a : P' ⟶ P` and `b : N ⟶ N'`, so both
  variances match the statement. Full component normalization makes `homMap`
  the usual induced chain map; no arbitrary arrow is assumed.
- Ordinary tensor represents derived tensor: `tensor_model` asserts
  `IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N))`.
  This is the existing canonical arrow QP tensor-derived QD -> Q(P tensor D),
  transported from the homotopy-category derived tensor counit. Its inverse
  gives the representative isomorphism in the statement.
- Signed chain evaluation: `evaluation` is an actual morphism of complexes from
  `P ⊗ moduleHomComplex P N` to `N`. In `evaluation_apply`, the inclusion
  `HomologicalComplex.ιTensorObj` of the (p,q) summand sends `x ⊗ₜ[R] z` to a
  pure tensor in total degree p+q; evaluation sends it to
  `(p * q).negOnePow • z.v p (p + q) rfl x`. Thus the sign is (-1)^(pq), including
  negative integer degrees. The field's being a morphism includes compatibility
  with the differentials.
- The tensor differential is the existing direct-sum total tensor differential
  of `HomologicalComplex.tensorObj` / `mapBifunctor`: d_P tensor identity plus
  (-1)^p identity tensor d_D. The Koszul sign is in the underlying tensor
  definition, not an additional unproved choice of tensor complex.
- Counit compatibility: `counit_eq` is precisely μ_Q followed by Q(evaluation)
  equals identity tensor comparison followed by `ihom.ev`. After inverting μ_Q
  and comparison this says the derived counit is represented by that chain map.
- All admissible complexes are quantified simultaneously, so the comparisons
  used in naturality are a single family, not independently chosen per arrow.

Dependency declarations read and used:

- `Mathlib.Algebra.Module.Projective`: `Module.Projective` (recorded dependency
  `def-weil-pbc-projective-module`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.quotientCompQhIso`
  (recorded dependency `def-weil-abstract-derived-category`).
- `Sheaf.Algebra.Homology.ModuleHomComplex`: `CochainComplex.moduleHomComplex`,
  with terms `HomComplex.Cochain` and differential `HomComplex.δ_hom`
  (recorded dependency `def-sc-module-total-hom-complex`).
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
  and `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed` supply
  the existing derived tensor and right adjoint. The latter's full hypotheses
  and construction were read, including its chain-sign convention.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
  supplies `ModuleCat.hasFunctorialFlatResolution`.

The modules of every recorded proof dependency are imported: `BoundedFlatKFlat`,
`ModuleHomComplexQuotient`, source `FlatModel` (specifically
`DerivedCategory.QObjTensorQObjIsoOfKFlatLeft`), source `Monoidal.KFlat`
(`MorphismProperty.kFlat`), Mathlib `DerivedCategory.KProjective`
(`CochainComplex.IsKProjective.Qh_map_bijective`), and `RingTheory.Flat.Basic`
(`Module.Flat.of_projective`, including the free case). Proof-only imports have
no `public` qualifier. The theorem docstring contains every step of the DAG proof.

Edge cases checked before and after writing:

- Zero P or zero N: Hom and evaluation are zero, and the counit and comparison
  statements have the same zero source/target. The zero ring causes no exception.
- A rank-one complex concentrated in degree p: a homogeneous Hom cochain of
  degree q evaluates with sign (-1)^(pq). In particular p=q=1 gives minus
  evaluation; p=0 or q=0 gives ordinary evaluation. Negative p and q use integer
  `negOnePow`, not truncated natural-number exponentiation.
- The chain equation: the d_N(z(x)) coefficients agree because
  (-1)^p (-1)^(p(q+1)) = (-1)^(pq); the z(d_P x) coefficients are
  (-1)^((p+1)q) and -(-1)^(p+q+p(q+1)), which cancel. This checks the exact
  order P tensor Hom and the node's sign.
- Infinite-rank projective terms and a complex P extending indefinitely to
  negative degrees remain allowed. The homogeneous cochains remain products
  and tensor totals remain sums. An N unbounded in both directions remains
  allowed in every field. There is no uniform choice of the bound on P.
- Zero chain maps, identities and quasi-isomorphisms are included among the
  arbitrary maps `a` and `b` in naturality; no invertibility is required there.

Searches for an existing statement:

- `msearch.py ... leanfinder` with "A bounded above complex of projective modules
  computes derived internal Hom naturally and its tensor Hom counit is signed
  chain evaluation": eight hits, led by `isKProjective_of_projective`,
  `IsKProjective` and projective-resolution results; no complete statement.
- `msearch.py ... loogle` with
  `CochainComplex.internalHomObj, DerivedCategory.QObjTensorQObjIsoOfKFlatLeft`:
  zero hits; Loogle does not know the upstream `internalHomObj` name. Its actual
  upstream source and `FlatModel` were read directly.
- `msearch.py ... grep` with `RHom|internalHom|tensorHomAdjunction` in
  `Algebra/Homology`: 25 hits on tensor Hom and general bifunctor machinery;
  no projective module Hom/evaluation model.
- `msearch.py ... leansearch` with "The product Hom complex from a bounded above
  projective module complex computes derived Hom and signed evaluation is the
  derived tensor Hom counit": eight hits on `HomComplex`, `δ`, `δ_hom` and
  generic resolution/complex equivalences; no complete statement.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for projective Hom,
  `homEvaluation`, `moduleHomComplex.*(eval|map)` and related names found general
  internal Hom, sheaf-Hom evaluation and unrelated projective Hom theorems.
  Direct source reads found the reusable generic closed derived structure and
  K-flat tensor isomorphism, but not this module-valued product-Hom comparison
  with the specified signed chain evaluation.
- `rg` for the exact node id in upstream `WeilConjectures` returned no hits.
  A collision check for `ProjectiveHomEvaluationModel` and
  `projective_hom_evaluation_model` in upstream, side Lean and
  `dag/lean_names_upstream.json` returned no hits before writing.

No node fault, statement correction, new independent notion or dependency-interface
repair was required. The helper structure belongs to this node and both declarations
are listed in `lean.declarations`. Validation is through the prescribed `scompile.py`
and `deliver2.py` wrappers only.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
