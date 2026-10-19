## Worker report

The module `Sheaf.AlgebraicGeometry.StalkFaithfulDerived` states
`AlgebraicGeometry.Etale.stalk_faithful_derived`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. The source
is the blueprint node of the same id, order 1703, read in the launcher's literature
mirror. The declaration docstring reproduces the DAG's five-step cone argument,
including exact inverse image, the point-sheaf/group equivalence, ordinary-sheaf
conservativity, and unbounded cohomology detection.

Hypotheses and clauses:

- The arbitrary scheme T is `{T : Scheme.{u}}`, for the explicitly bound universe u.
- D(T_et), with no coefficient ring in the node, is the ordinary abelian-sheaf category
  `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`. Both K and L
  range over this entire unbounded category. The coefficient-size convention is
  exactly the convention of def-weil-pbc-derived-categories.
- An arbitrary morphism is `(α : K ⟶ L)`.
- “is an isomorphism if and only if” is the equivalence `IsIso α ↔ ...`.
- “every geometric point” is `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ T)`. There is no chosen-point or algebraic-extension restriction.
  Field and scheme use the same universe as the recorded geometric-point interface.
- “its pullback ... is an isomorphism” is
  `IsIso ((upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory.map α)`.
  This is the actual canonical termwise exact inverse image localized at
  quasi-isomorphisms, with target the derived category of sheaves on Spec Ω.
  It is not a condition only on a separately chosen family of cohomology maps.

Statement dependency declarations used:

- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded documentation gives
  D(T_et) as `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1})`;
  the existing Mathlib declaration `DerivedCategory` supplies the category.
  The module's `DerivedCategory.torsionCohomology` is read but is irrelevant here:
  this node imposes no torsion condition. The module is publicly imported as recorded.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, together with `Field Ω`
  and a scheme map out of Spec Ω, is the recorded inline notion of geometric point.
  The full signature and docstring of `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` were also read; they identify these maps
  with points and residue-field embeddings, without adding any constraint.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, the canonical inverse image, constructed as
  left Kan extension followed by sheafification; its recorded companion
  `upperStarLowerStarAdjunction` supplies the adjunction. Both full definitions and
  their Grothendieck-abelian coefficient assumptions were read.
- `CategoryTheory.Functor.mapDerivedCategory` from
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` is the existing exact-functor
  construction. Its full signature requires additive, finite-limit-preserving and
  finite-colimit-preserving inverse image, all inferred from the existing APIs.

The modules of all recorded proof dependencies are imported without `public`:
`EtaleInverseImageExact`, `GeometricStalkAsPullback`, `GeometricStalkCohomology`,
`GeometricPointCanonicalGerm` (under `Sheaf.AlgebraicGeometry`),
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and the relevant
Mathlib derived-category, triangulated, point-exactness and short-exactness modules.
These give respectively `upperStar_abelian_exact`, `geometricStalk_as_pullback`,
`nonempty_geometricStalk_cohomology_iso`, `isIso_globalGerm_identity`,
`DerivedCategory.isZero_iff`, `Scheme.isIso_of_isIso_sheafFiber_map`,
`Functor.mapDerivedCategory`, `Triangle.isZero₃_iff_isIso₁`, and stalk exactness.
No proof dependency is omitted for an import cycle.

Edge cases checked before writing: the empty scheme (the pointwise condition is
vacuous and its abelian-sheaf derived category is zero); zero objects and zero maps
(the latter are invertible precisely when source and target vanish); identities;
unbounded complexes in both directions; arbitrary characteristics; and every
algebraically closed field in the scheme universe. There are no finiteness,
Noetherian, torsion, constructibility or boundedness hypotheses. The test-field
universe is not an independent smaller universe that could make the tests vacuous.
`set_option autoImplicit false` ensures that every variable and universe is bound.

Searches for an existing declaration (2026-10-16):

- msearch.py / LeanSearch, query “A morphism in the unbounded derived category of
  etale sheaves is an isomorphism if its pullback to every geometric point is an
  isomorphism”: service returned Internal Server Error; no absence inference made.
- msearch.py / LeanFinder, query “derived category morphism isomorphism iff pullback
  to every geometric point isomorphism”: eight hits, including
  `Scheme.Modules.Hom.isIso_iff_isIso_app`,
  `GrothendieckTopology.W_sheafToPresheaf_map_iff_isIso`, and
  `AlgebraicGeometry.isomorphisms_eq_stalkwise`. These concern ordinary sheaves or
  schemes, and none states the derived geometric-pullback criterion.
- msearch.py / Loogle, query `DerivedCategory.isIso_iff`: the single hit tests every
  cohomology morphism in a generic abelian category. It does not test geometric
  derived pullbacks, so it does not supply this node's full statement.
- msearch.py / grep, query `isIso|sheafFiber`, subdirectory
  `Algebra/Homology/DerivedCategory`: found `DerivedCategory.isIso_iff` and
  localization criteria, with no étale geometric-pullback criterion.
- Direct rg over Mathlib, the upstream WeilConjectures tree, the upstream name index,
  and this project's `lean/Sheaf`: searched `stalk`, `faithful`, `sheafFiber`,
  `upperStar`, derived-category combinations, and the exact node/declaration name.
  No exact duplicate. In particular, the full source and docstring of
  `Scheme.isIso_iff_isIso_sheafFiber_map_homologyFunctor_map` in
  `WeilConjectures.AlgebraicGeometry.Sites.DerivedStalk` were read. Its RHS tests the
  geometric stalks of cohomology maps, indexed by scheme points and chosen algebraic
  closures. The current node instead tests the actual derived inverse-image map
  at every geometric point, as required by its DAG statement and the stage-1 audit.
  `GeometricStalkAsPullback` and `GeometricStalkCohomology` supply the comparisons,
  rather than already declaring the current criterion.

No statement dispute or correction, new node, or dependency repair is needed.
The prescribed scompile.py check passed for the module with all proof imports,
under the 60-second per-file limit, with no errors or warnings.

## Second reading by NC

I read the node statement against its source place
(`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-stalk-faithful-derived.md`,
node order 1703) and then matched it against the declaration
`AlgebraicGeometry.Etale.stalk_faithful_derived` in
`Sheaf.AlgebraicGeometry.StalkFaithfulDerived`.

The statement list and verdict are:

- The arbitrary scheme `T` is rendered by `{T : Scheme.{u}}`; verdict: exact.
- `D(T_\Et)` is rendered by
  `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`, using
  the ordinary (no coefficient ring) unbounded derived category; verdict: exact
  with `def-weil-pbc-derived-categories`.
- The two arbitrary objects `K` and `L` and their morphism `α : K ⟶ L` are
  rendered by the implicit `K L` binders and explicit `(α : K ⟶ L)`; verdict:
  exact, with no boundedness, constructibility, torsion, or finiteness assumption.
- The left side “`α` is an isomorphism” is rendered by `IsIso α`; verdict: exact.
- Every geometric point is rendered by
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ T)`; verdict: exact inline form of
  `def-weil-geometric-point`, with the required algebraically closed field and
  no selected point or extra extension condition.
- The right side “the pullback at that geometric point is an isomorphism” is
  rendered by
  `IsIso ((upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory.map α)`;
  verdict: exact canonical étale inverse image followed by its induced functor
  on unbounded derived categories, using `def-weil-pbc-inverse-image`.
- The biconditional is rendered by `IsIso α ↔ ∀ ...`; verdict: quantifier order
  and both directions exactly match the node.

I checked the source proof's cone, cohomology, and geometric-stalk argument
against the docstring; the proof dependencies and imports provide those later
proof inputs without changing the statement. The empty scheme makes the point
condition vacuous and its sheaf category is trivial; zero objects and zero
morphisms obey the same `IsIso` criterion; identity morphisms are included;
unbounded complexes in both directions are allowed; and no characteristic or
Noetherian hypothesis is introduced. The field and scheme universes are both
`u`, so the geometric-point quantification does not become vacuous.

For the one-definition-per-notion check I reran the worker's LeanSearch,
LeanFinder/Loogle, and Mathlib/source/project `rg` searches for stalkwise
faithfulness, geometric pullback, and derived-category isomorphism criteria.
The existing hits concern ordinary sheaf stalks or cohomology maps; none states
this derived geometric-pullback criterion. I also read the exact declarations
of `DerivedCategory`, `IsAlgClosed`/`Scheme.SpecToEquivOfField`, and
`Etale.upperStar`; each has the interface used above. No new definition node or
dependency repair is required.

No mismatch was found, so no Lean or node statement was changed. The module
was compiled with `python3 /home/ubuntu/weil-launcher-nt/scompile.py NC
lem-kun-stalk-faithful-derived` and completed cleanly within the prescribed
limit.
