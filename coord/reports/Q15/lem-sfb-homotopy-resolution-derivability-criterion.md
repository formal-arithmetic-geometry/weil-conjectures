## Worker report

Recorded an exact existing upstream statement; no Lean module is introduced and no proof is
written. Declaration:
`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`, in
`WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure`, lines 211–221.
Read the entire upstream module, including the surrounding section variables, the definition
of the localizer morphism, and the theorem's docstring and proof. The recorded `lean.statement`
is the verbatim declaration signature; its inherited parameters are described below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Abelian category A: the section binds `{A : Type*} [Category A] [Abelian A]`.
  The object and morphism universes are independently polymorphic; there is no small-category,
  enough-projectives, enough-injectives, Grothendieck, or derived-category size assumption.
- Cochain complexes and q: `CochainComplex A ℤ`, `HomotopyCategory A (.up ℤ)`, and
  `HomotopyCategory.quotient A (.up ℤ)` are Mathlib's integer cochain complexes, quotient
  category by homotopy, and quotient functor. `HomotopyCategory` is the quotient by the
  congruence `Nonempty (Homotopy f g)`, so morphisms are precisely cochain maps modulo the
  stated homotopy relation. No boundedness or degree restriction is imposed.
- Property of objects of K(A): the explicit section parameter is
  `P : ObjectProperty (HomotopyCategory A (.up ℤ))`.
- Closed under isomorphisms: `[P.IsClosedUnderIsomorphisms]`.
- Contains zero, stable under all integer shifts, and mapping cones:
  `[P.IsTriangulated]`. Read Mathlib `CategoryTheory/Triangulated/Subcategory.lean:193–206`:
  this class extends `P.ContainsZero`, `P.IsStableUnderShift ℤ`, and
  `P.IsTriangulatedClosed₂`. Together with closure under isomorphisms it gives all three
  two-out-of-three triangle clauses (`ext_of_isTriangulatedClosed₁/₂/₃`), and conversely
  the node's zero/shift/cone conditions give these conditions by rotation of cone triangles.
  Mathlib's distinguished triangles in K(A) are those isomorphic to mapping-cone triangles,
  with the shift/cone conventions of the recorded abstract-derived-category dependency.
- Functorial complex resolutions: `{ρ : CochainComplex A ℤ ⥤ CochainComplex A ℤ}`.
- Natural resolution map to the identity: `(p : ρ ⟶ 𝟭 _)`.
- Every component a quasi-isomorphism: `(hp : ∀ K, QuasiIso (p.app K))`.
- Every resolution in P: `(hρ : ∀ K, P ((quotient A (.up ℤ)).obj (ρ.obj K)))`.
- Conclusion: `(quasiIsoLocalizerMorphism P).IsLeftDerivabilityStructure`.
  Read `quasiIsoLocalizerMorphism` at lines 55–59: its functor is `P.ι`, the full inclusion,
  its target class is `HomotopyCategory.quasiIso A (.up ℤ)`, and its source class is exactly
  that class's `inverseImage P.ι`. Thus both sides carry exactly the node's quasi-isomorphisms.
  This is the `IsLeftDerivabilityStructure` of the dependency's Mathlib match, including
  left resolutions and Guitart exactness of the inverse localization comparison square.
- The final limitation is respected: no induced functor on K(A), no additivity of ρ, and
  no preservation of homotopies by ρ occurs among the binders. The upstream proof first
  constructs the structure on complexes and then transfers along quotient functors;
  the cylinder/Guitart-exact-square argument is already proved upstream.

Dependency declarations read and used by the existing theorem:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic:112` (Mathlib leaf; no Lean record is required).
  Read its full class and docstring: preadditivity, finite products, kernels/cokernels,
  normal monomorphisms and epimorphisms give exactly the node's abelian structure.
- `def-weil-abstract-derived-category`: recorded `DerivedCategory` and `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic:74–98`; read the definitions and docstrings.
  The item uses its underlying complexes, homotopies, shifts, cones and quasi-isomorphisms,
  rather than a chosen D(A). These are the canonical Mathlib notions in
  `Mathlib.Algebra.Homology.HomologicalComplex`, `Mathlib.Algebra.Homology.HomotopyCategory`,
  `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`, and
  `Mathlib.Algebra.Homology.QuasiIso`. The dependency's current `blueprint_update` only
  shortens the derived-category definition and does not alter these notions.
- `def-sfb-left-derivability-structure`: Mathlib match
  `CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure` and
  `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff`,
  `Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic:140–174`, and
  `CategoryTheory.TwoSquare.guitartExact_iff_final`,
  `Mathlib.CategoryTheory.GuitartExact.Basic:262–264`. Read these signatures and the class
  docstring, together with left resolutions in `Localization/Resolution.lean`.
  The criterion's conclusion uses exactly this class, without a duplicate definition.

Source checked: the current blueprint
`main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`,
third sentence, and the supporting upstream criterion named in the node's source record.
No repair note exists for this item. Its `proof` and `proof_deps` are empty; no extra proof
imports or postponed helper statements are needed. The node's statement is unchanged.

Edge cases checked: zero category and zero complex remain allowed; P contains zero by
`IsTriangulated`, so an empty subcategory is correctly excluded. The maximal property P
and identity resolution satisfy the hypotheses and recover the full inclusion case.
All positive and negative integer shifts and unbounded complexes are included. There is
no nonempty index-set assumption, no fixed degree, and no relation imposed between object
and morphism universes. There is no requirement that ρ send homotopic maps to homotopic
maps. No statement dispute or fault was found.

Searches performed (Q15, this item, via `msearch.py`):

- LeanFinder: “A triangulated full subcategory of the homotopy category containing functorial
  resolutions of complexes is a left derivability structure”: 8 hits, including Mathlib's
  general derivability constructors and right functorial-resolution criterion; none is the
  full homotopy-quotient criterion.
- Loogle: `"IsLeftDerivabilityStructure"`: 12 hits, including the existing class, its fields,
  opposite-category equivalences, and constructor; no Mathlib duplicate of this criterion.
- Mathlib grep: `isLeftDerivabilityStructure|functorial_resolutions|quotientSquareIso` in
  `CategoryTheory/Localization/DerivabilityStructure`: 18 hits for generic resolution and
  localized-equivalence transfer results, not the complex-to-homotopy criterion.
- LeanSearch: “Transfer a left derivability structure of complexes to the homotopy category
  using functorial resolutions”: 8 hits on derived functors/projective resolutions and
  cofibrant homotopy replacements; no exact criterion.
- Source `rg`: `isLeftDerivabilityStructure_quasiIsoLocalizerMorphism` locates this exact
  theorem and its consumers (K-flat and monoidal derived-functor modules). Searching for
  the item's blueprint id in the upstream source gives no occurrence, but the theorem's
  full statement and module docstring are an exact conceptual match.
- Project `lean/Sheaf` search for the theorem name and functorial homotopy resolutions
  finds no second declaration of this criterion. `dag/lean_names_upstream.json` search
  gives no entry for the newly available theorem; the node's own `lean_audit.slopmaster2`
  already identifies the exact closed upstream declaration.

Validation: `deliver2.py --no-push` passed: the existing-declaration `#check` probe
compiled cleanly through `scompile.py`, and the server preflight accepted the packet.
The delivery wrapper repeats these checks before pushing.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
