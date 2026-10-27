## Worker report

The module `Sheaf.AlgebraicGeometry.PresheafFieldLiftFamilyCalculus` states
`AlgebraicGeometry.AlgebraicSpace.presheaf_field_lift_family_calculus`, with one
`sorry` proof. Its three conjuncts are exactly the three clauses of
`lem-trf-presheaf-field-lift-family-calculus`. No definitions, dependency repairs,
new DAG nodes, or changes to the natural-language statement are needed.

Hypothesis and conclusion correspondence:

- The base scheme is `(S : Scheme.{u})`. All presheaves are functors
  `(Over S)ᵒᵖ ⥤ Type u`, exactly the encoding in the recorded
  `def-trf-algebraic-space` and joint-surjectivity dependency.
- Every use of joint surjectivity is the existing
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`, not an alternate
  predicate. Its definition quantifies over `(K : Type u) [Field K]`, a
  structure map `s : Spec (CommRingCat.of K) ⟶ S`, and a section. Its witnesses
  are a family index, `(L : Type u)`, `Field L`, `e : K →+* L`, and a section
  over `Spec.map (CommRingCat.ofHom e) ≫ s` with the prescribed image.
  Ring homomorphisms between fields are embeddings, so this is the requested
  field-extension condition. No algebra structure or chosen common extension
  is added. Both successive extensions in clause (2) stay in `Type u`.
- Clause (1) quantifies over arbitrary `F G` and `e : G ≅ F`. The conclusion
  `IsJointlySurjective (fun _ : Unit ↦ e.hom)` is precisely the singleton
  family of the isomorphism.
- Clause (2) quantifies over `I : Type v`, `J : I → Type w`, `F`, `G`, `H`,
  `f : ∀ i, G i ⟶ F`, and `g : ∀ i j, H i j ⟶ G i`. The two hypotheses are
  `IsJointlySurjective f` and `∀ i, IsJointlySurjective (g i)`. The conclusion
  uses `Sigma J` for the disjoint union and `g ij.1 ij.2 ≫ f ij.1` for
  `f_i ∘ g_ij`.
- Clause (3) quantifies over arbitrary `I`, `F`, `F'`, `G`, `f`, and
  `a : F' ⟶ F`, and assumes only `IsJointlySurjective f`. The objectwise
  presheaf is supplied directly by Mathlib's
  `PullbackCone.combine a (f i)` applied to
  `Types.pullbackCone (a.app T) ((f i).app T)` and its explicit limiting proof
  `(Types.pullbackLimitCone (a.app T) ((f i).app T)).isLimit`.
  This is a concrete construction: the cone's point at `T` is definitionally
  `{p : F'.obj T × (G i).obj T // a.app T p.1 = (f i).app T p.2}`.
  `combine` maps along a restriction by the explicit type-cone lift; reading
  `pullbackLimitCone.isLimit` shows its two coordinates are the restrictions
  in `F'` and `G i`. Its `.fst` has component the first coordinate projection.
  The conclusion is joint surjectivity of exactly this family of projections.
  No arbitrary pullback, representing object, or comparison isomorphism is
  substituted for the displayed compatible pairs.
- The separate universes `v` and `w` allow arbitrary outer and inner index
  sets. There is no `Nonempty` or `Finite` assumption. The only category is
  the category of presheaves, and there is no sheaf condition, étaleness,
  representability, or algebraic-space membership hypothesis.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` for `def-pc-scheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: the recorded
  `AlgebraicGeometry.AlgebraicSpace` framework and its full docstrings. Its
  test presheaves are `(Over S)ᵒᵖ ⥤ Type u`; the current statement uses that
  category without imposing the extra conditions defining algebraic spaces.
  This module is publicly imported by the next dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`:
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`, read in full,
  provides the exact field-extension lifting predicate for all three clauses.
  This is also the sole proof dependency and is publicly imported because
  the statement itself uses it.
- `def-weil-size-convention` is recorded as a metatheoretic convention, with
  no declaration. Explicit universes `u v w`, and the dependency's test
  fields in `Type u`, implement it here.
- `Mathlib.Algebra.Field.Defs`: `Field`, the `mathlib_match` of
  `def-weil-field`, appears inside the existing lifting predicate.
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks`:
  `CategoryTheory.Limits.PullbackCone.combine` assembles the prescribed
  compatible-pair presheaf, with no new definition.
- `Mathlib.CategoryTheory.Limits.Types.Pullbacks`:
  `CategoryTheory.Limits.Types.PullbackObj`, `pullbackCone`, and
  `pullbackLimitCone`, read in full, give its literal objectwise data and
  first projection. All imports are public statement dependencies.

Source check: read `literature/stacks-project/spaces-topologies.tex`,
`lemma-etale` (Tag 041F), including its three clauses and omitted proof, and
`spaces-properties.tex`, the presheaf field-valued representative discussion
immediately preceding `definition-points` (Tag 03BU). The node explicitly
extracts the elementary point-lifting arguments to arbitrary presheaves. The
Lean docstring carries all five proof steps from the node: inverse section;
successive extensions; compatible-pair restrictions and presheaf laws;
pair lifting by naturality; and empty-family cases.

Edge cases checked before writing: if `I` is empty, joint surjectivity says
that every field-valued target section type is empty; composition and base
change are then vacuous. If `J i` is empty, the corresponding hypothesis
forces the field-valued sections of `G i` to be absent, so the outer lift
cannot land there. For the empty base scheme no field-valued base map exists,
so every family satisfies the lifting condition. Identity field extensions
and singleton families are included. Empty-valued presheaves are allowed;
no nontriviality or existence of any section is assumed. There is no need
to enlarge fields or to align either index universe with `u`.

Searches made through `msearch.py` (2026-10-22):

- LeanFinder: "Jointly surjective families of presheaves on schemes defined
  by lifting field valued sections after field extension are stable under
  composition and objectwise pullback". Eight hits, including
  `AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving`,
  `Scheme.isJointlySurjectivePreserving`, and scheme precoverage results.
  None gives the arbitrary-presheaf field-extension predicate. Read the
  signature and docstring of `Scheme.IsJointlySurjectivePreserving` in
  `Mathlib/AlgebraicGeometry/Sites/MorphismProperty.lean`: it concerns
  pairs of points of schemes and scheme fibre products.
- Loogle: `"IsJointlySurjective", "Presheaf"`. Zero hits.
- Mathlib grep: `IsJointlySurjective|field.val.*surject|surject.*field.val`
  under `AlgebraicGeometry`. Seventeen hits, all concerning scheme-point
  surjectivity or its preservation, without this presheaf predicate.
- LeanSearch: "A family of natural transformations of presheaves on schemes
  that lifts every field valued section after extending its field remains
  jointly surjective under composition and pullback". Eight hits, including
  `CategoryTheory.Presheaf.isLocallySurjective_of_iso` and
  `isLocallySurjective_comp`, and scheme surjectivity/precoverage results.
  Local surjectivity for a Grothendieck topology is not the specified
  field-section family lifting predicate; none is an exact match.
- Project `rg`: `IsJointlySurjective|field.lift.family.calculus` in
  `lean/WeilConjectures`, and the node id there, found no match. The broader
  search `field.*lift|Field.*Lift|IsJointlySurjective` was also inspected;
  its unrelated field and geometric-point lifts do not state this calculus.
- Project `rg`: `IsJointlySurjective|presheaf_field_lift_family_calculus`
  in `lean/Sheaf` found the recorded predicate and its applications, including
  `ChartwiseEtalePermanence` and `AlgebraicSpaceFibreProductsEtaleCovers`.
  Those statements concern algebraic spaces and étale families, and hence
  do not state the present arbitrary-presheaf calculus. The proposed full
  theorem name is absent.

No mathematical fault or statement dispute was found. The compact-object
example file currently contains only its withdrawal notice; its node record
was still read. The required current module header and visibility conventions
from `brief-stage2.md` are followed.

## Validation

The delivery will be checked with the prescribed single-file server compiler
and `deliver2.py --no-push`; their outcomes are recorded below.

`scompile.py Q58 lem-trf-presheaf-field-lift-family-calculus` compiled the
module both in sandbox mode (5.7 seconds) and at its library module path
(6.4 seconds), with no errors or warnings. The first `deliver2.py --no-push`
completed successfully: commit `8028260007e` passed the server preflight and
per-file compilation; nothing was pushed. A local structural check confirmed
that the node changes only in `lean`, its recorded signature is verbatim,
and all Lean source lines have at most 100 characters.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
