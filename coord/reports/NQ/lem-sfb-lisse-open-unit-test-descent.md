## Worker report

The module `Sheaf.Paper.LisseOpenUnitTestDescent` states
`AlgebraicGeometry.ProEtale.isIso_lisse_open_unit_of_scalar_contractible_tests`.
Its proof is `sorry`; the docstring retains all eight steps of the DAG proof and their
references. The three auxiliary definitions construct the actual open test object, its
projection, and the canonical derived scalar restriction. Their data are fully written.
There are no new DAG nodes, dependency repairs, or statement corrections.

Clause-by-clause rendering:

- An arbitrary affine scheme: `(X : Scheme.{u}) [IsAffine X]`.
- A global function: `(f : Γ(X, ⊤))`. The principal open W is `(X.basicOpen f).toScheme`,
  with its actual inclusion `(X.basicOpen f).ι`.
- An arbitrary commutative condensed ring: the existing unbundled encoding
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]`.
  This is the object-plus-structure encoding of `Profinite.CondensedRing` (the bundled
  category `Mon` of the same abelian sheaves), with no topological presentation imposed.
- On every scheme Z the coefficient is exactly the existing `condensedRingObj Λ Z`,
  the underlying object of `coefficientRing Z (Mon.mk Λ) = p_Z^* Λ`.
- Modules are exactly Mathlib's internal `Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
  (condensedRingObj Λ Z)`.
- The scalar hypothesis quantifies over `(V : X.ProEt)` with `IsAffine V.left` and
  `(Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} V`. Thus weak contractibility
  is on the full X-site, in the sheaf-of-sets section universe u+1. Its definition requires
  locally surjective set-sheaf morphisms to be surjective on V-sections, equivalently
  epimorphisms on this site. No weak contractibility is required of the puncture.
- `openUnitTest U V` is the literal scheme pullback `U.toScheme ×_X V.left`, with its
  composite structure map to X, so is an object of the full small pro-etale site.
  `openUnitTestProjection U V` is the actual second projection to V.
- `scalarOpenUnitTestRestriction Λ U V` derives the natural transformation
  `(sheafSections ...).map (openUnitTestProjection U V).op`, then takes its component
  at `(DerivedCategory.singleFunctor _ 0).obj (condensedRingObj Λ X)`.
  Its source is R(ev_V)(Λ_X[0]); its target is R(ev_(U×V))(Λ_X[0]), in D(Ab).
  These are canonically the stated RΓ(V,Λ_V[0]) and RΓ(U×V,Λ_(U×V)[0]): localization
  identifies the slice with the small site of the source scheme, restriction is exact
  with an exact extension-by-zero left adjoint, hence preserves K-injectives, and
  coefficient restriction is identified with Λ_V by the specified alpha comparison.
  Both endpoints are computed by restricting the same ambient abelian K-injective
  resolution. Consequently the arrow is restriction of that resolution, precisely the
  actual restriction in the node. This uses the full right-derived functor, rather than
  H⁰ or only nonnegative cohomology. No arbitrary comparison map is supplied as input.
- `hscalar` is `IsIso` of that actual arrow for every such V.
- The conclusion quantifies over any `(X' : Scheme.{u}) [IsAffine X']` and
  `(a : X' ⟶ X) [WeaklyEtale a]`, namely every affine object of the recorded small
  pro-etale site (whose objects are weakly etale maps by the site's convention).
- N is an arbitrary internal module as above on X', with `hN : IsLisseCoefficientModule Λ N`.
  The recorded definition chooses a pro-etale cover and on each chart uses `Mod.IsFree`.
  The latter is `∃ n : ℕ, Nonempty (M ≅ Mod.finiteFree R n)`, so ranks can vary and zero
  is allowed. This imposes neither a global basis nor any field-coefficient condition.
- `j'` is the actual base-changed open immersion `pullback.snd (X.basicOpen f).ι a`.
  The conclusion is `IsIso` of the component at N[0] of
  `CondensedRing.derivedUpperStarLowerStarAdjunction Λ j'`. This is the specified
  K-flat-left/K-injective-right derived adjunction, not an unspecified isomorphic
  adjunction. Its right adjoint is the right derived functor of the entire module
  direct image, the same functor named `moduleObjectDerivedPushforward`. Exactness of
  pullback canonically identifies its left adjoint with termwise j'^*; the existing
  `leftDerivedUpperStarIsoMapDerivedCategory` expresses this. Thus its component is
  exactly the actual derived unit described in the node under that canonical identification.
- `DerivedCategory` throughout is the ordinary unbounded localization. There is no
  completion, boundedness, connectedness, Noetherian, finite-field, or nonzero-rank binder.

Recorded statement dependencies read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-pur-ringed-site-zeroth-hypercohomology | Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses | CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses |
| def-sfb-lisse-coefficient-module | Sheaf.Paper.CoefficientHeartStratificationDefs | AlgebraicGeometry.ProEtale.IsLisseCoefficientModule |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic | DerivedCategory, HasDerivedCategory |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Spec, Spec.map |
| def-weil-pbc-proetale-site | Mathlib.AlgebraicGeometry.Sites.Proetale | AlgebraicGeometry.Scheme.ProEt |
| sk-def-pe-weak-contractible | WeilConjectures.CategoryTheory.Sites.WeaklyContractible | CategoryTheory.GrothendieckTopology.IsWeaklyContractible |
| sk-def-sfb-condensed-ring | Sheaf.Topology.ProfiniteCondensedRing | Profinite.CondensedRing |
| sk-def-sfb-module-derived-pushpull | Sheaf.Paper.CondensedModuleDerivedPushpull | AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward, derivedUpperStarLowerStarAdjunction |
| sk-def-sfb-module-objects | Mathlib.CategoryTheory.Monoidal.Mod | CategoryTheory.Mod |
| sk-def-sfb-pulled-back-coefficients | WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic | AlgebraicGeometry.ProEtale.coefficientRing, condensedRingObj |

The hypercohomology dependency records H⁰ RΓ; the scalar hypothesis needs full RΓ.
The module publicly imports that dependency but uses its same generic K-injective
`Functor.rightDerivedFunctor` construction, at section evaluation, before taking H⁰.
The affine-spectrum node is used through the unrestricted `IsAffine` presentation of
an affine scheme; no choice of a presentation is added as data.

Plain proof imports are the recorded modules for internal-module transport, tensor
structure, weakly etale localization, exact localized modules, K-injective restriction,
contractible sections, exact-functor derived comparison, and the contractible basis.
The already public derived-pushpull and lisse modules also supply proof dependencies.
`lem-sfb-kflat-derived-adjunction-transport-shifts` and
`lem-sfb-ringed-sections-forget-abelian` have no recorded Lean declarations, so no module
can yet be imported for those proof steps; their precise obligations remain in the
proof docstring. This does not prevent writing this node's statement.
Additional public imports supply additive evaluation and the canonical natural
transformation between the right derived evaluation functors.

Edge cases checked before writing and again against the resulting signature:

- Rank zero: `Mod.IsFree` admits `n = 0`; no nonzero or positive-rank binder occurs.
- Empty X or X': `IsAffine` and the site permit the empty scheme; empty charts cause no
  exclusion. The derived categories of sheaves on the empty site are zero categories.
- Identity open: for a unit f, every test pullback projects isomorphically to its original
  test, the scalar map is the derived identity under this canonical identification, and
  the unit of the identity-open adjunction is invertible.
- Empty open (e.g. f = 0): the hypothesis is genuinely restrictive, requiring scalar
  derived sections to vanish on all the contractible affine tests. It is not accidentally
  an automatic instance. It implies the local finite-sum vanishing used by the conclusion.
- Arbitrary coefficients, disconnected charts, and varying ranks: only a commutative
  condensed ring and the recorded locally finite free predicate are required.
- Size: schemes live in u; the full site has object universe u+1 and morphism universe u;
  coefficients and set-sheaf evaluations use u+1. These site universes are not equated.

Searches for an existing statement (2026-10-22):

1. `msearch.py ... leanfinder "Scalar cohomology on weakly contractible pro etale affines
   detects open derived adjunction unit for locally finite free modules"`: eight hits,
   including `AlgebraicGeometry.exists_appTop_map_eq_zero_of_isAffine_of_isLimit`,
   `Scheme.Modules.instIsLeftAdjointRestrictFunctor`, and ordinary scheme-module counit
   isomorphisms. No scalar-to-lisse contractible-test theorem.
2. `msearch.py ... loogle '"Sheaf", "unit"'`: twelve hits, chiefly `OverPresheafAux`
   sheaf equivalences and their units. No matching criterion.
3. `msearch.py ... grep '(lisse|locallyFree|weaklyContractible).*(unit|derived|quasiIso)|
   (unit|derived|quasiIso).*(lisse|locallyFree|weaklyContractible)'`: zero Mathlib hits.
4. `msearch.py ... leansearch "A derived open adjunction unit for lisse internal modules
   is invertible if scalar restriction on affine weakly contractible pro etale tests is
   invertible"`: eight hits; generic `Adjunction.derived_unit`, derived units and
   localization-unit formulae, and ordinary scheme/module restriction-unit formulae.
   These supply general machinery, not the stated detection theorem.
5. `rg` of that concept expression in `lean/WeilConjectures` and `lean/Sheaf` found
   unrelated Weil tensor/weight results, dense-open recovery and ordinary lisse units.
   None has the arbitrary condensed coefficients and scalar contractible-test hypothesis.
6. Exact searches for this blueprint id in both source roots, and searches for all four
   chosen declaration names in Mathlib and both project roots, returned no matches.

No statement fault or disputed clause was found. The item node changes only in `lean`.
Server scompile accepted the module in sandbox and library module modes, with no errors
or unexpected warnings (the theorem's `sorry` is intentional at stage 2).

## Second reading by NQ

The dispatcher prohibits starting another agent; this is a separate self-check, with the
node JSON and final Lean source both open. The maintainer's independent delivery review
remains necessary. The comparison above was rechecked against every paragraph of the
node and the scalar helper bodies. In particular, the full-site weak-contractibility
binder was checked against the dependency definition, `IsLisseCoefficientModule` was
unfolded through `Mod.IsFree` to verify finite varying ranks including zero, the pullback
projection was checked to land in X', and the conclusion was checked to use the specified
derived adjunction's own unit. The scalar map derives actual restriction on the same
ambient resolution, with the localized K-injective interpretation explained above;
it does not add a resolution-choice or comparison-map hypothesis. The explicit `module`
header and `set_option autoImplicit false` were checked, and all three real helper
constructions have source/blueprint docstrings. No mismatch was found or statement changed.
