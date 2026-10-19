## Worker report

The module `Sheaf.Paper.DerivedDirectImageOpenCoherence` states
`AlgebraicGeometry.ProEtale.CondensedRing.derivedDirectImageOpenCoherence` with one
`sorry`. All helper data are real constructions from existing adjunctions and canonical
functor comparisons. No additional theorem, definition node, dependency repair, or
statement correction is needed.

Hypotheses and coefficients:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The field of positive characteristic different from ell is `(k : Type u) [Field k]`
  with `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`. For a field, prime
  characteristic is exactly positive characteristic.
- The fixed algebraic closure is the existing `PadicAlgCl ℓ`. The finite intermediate
  extension is `E : PadicAlgCl.FiniteIntermediateField ℓ`; this includes the base field.
- The two coefficient cases are the two conjuncts, with
  `Profinite.continuousMapRingObj E.1` and `Profinite.padicAlgClRingObj ℓ`. The latter
  is the *finite-subextension-valued* sheaf, not all valuation-continuous functions
  into the algebraic closure. Read the existing `padicAlgClCondensedRing` construction
  and its `padicAlgClSubfunctor` before selecting it.
- The scheme setting is quantified in `DirectImageOpenCoherence`: objects of
  `Over (Spec (.of k))` with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`
  on their structure maps. Every arrow is an arrow of that over category. This
  retains the exact separated finite-type setting, rather than claiming the theorem
  for every scheme merely because its helper maps are available there.
- The coefficient on X is precisely the existing `condensedRingObj Λ X` (the underlying
  object of `coefficientRing X (Mon.mk Λ)`), and the module category is Mathlib's
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
  `DerivedCategory` is the ordinary unbounded localization, never its constructible
  or bounded-below subcategory. The ambient Grothendieck-module instances provide
  derived categories and K-injective resolutions without extra hypotheses.

Clause-by-clause rendering:

1. `directImageComposition` is `rightDerivedFunctorNatIso (lowerStarComp Λ f g).symm`
   followed by `rightDerivedFunctorCompIso`. These are the published unit-preserving
   comparisons, not an arbitrarily selected isomorphism. The predicate
   `DirectImageCompositionNormalized` explicitly states their class on a common
   K-injective I, using `rightDerivedFunctorObjQIso` and the inverse underived comparison.
   `DirectImageCompositionAssociative` is exactly the first displayed equation, in
   diagrammatic functor order. Its `Functor.associator` and the derived image of
   `Category.assoc f g h` supply the necessary canonical reassociations.
2. `derivedDirectImageOpenRestriction` is the adjunction mate of
   `derivedOpenCoherencePullbackSquare`. The second conjunct of `DirectImageOpenCoherence`
   quantifies over a Cartesian open square (`IsPullback`), with `IsOpenImmersion j.left`
   and `QuasiCompact j.left`. Its other horizontal arrow is the pulled-back open;
   `IsOpenImmersion i.left` is the consequence of base change, not a restriction on f.
   Using any chosen Cartesian square is precisely the invariant meaning of the
   statement's fibre-product identifications.
   `DirectImageRestrictionNormalized` asserts `IsIso` of rho, giving the required natural
   isomorphism via `asIso`. It also retains the underived comparison as an isomorphism.
   Its final formula says that, after the canonical exact-functor factorization and
   K-injective comparison isomorphisms, rho is `DerivedCategory.Q.map` of the termwise
   `directImageOpenRestriction`. This is the specified representative formula.
   `OpenCoherenceSectionwise` asserts bijectivity of the canonical open-slice
   coprojections and the actual section equation. The site arrow
   `openCoherenceSectionArrow` is `pullback.map` with the identity on the test object
   and the given open inclusion on the source. Thus it is exactly the identity on
   I(V times_T S) under the canonical fibre-product identification. This is an equation
   of actual sections, rather than an unspecified natural-isomorphism witness.
   The underived pullback is the recorded `upperStar`, including extension along
   `condensedPullbackHom`. `cartesianCoefficientPullbackIso` identifies that extension
   with restriction along alpha inverse. Hence the action is exactly the inverse
   coefficient comparison required in the node, with no different ring sheaf.
3. `DirectImageSuccessiveRestriction` is equality of the direct restriction with the
   composite restrictions, inserting `openCoherenceRestrictionComp` for both opens.
   `DirectImageRestrictionComposition` is exactly the second displayed equation:
   the left side is restriction of kappa, rho for g at Rf(K), and Rg_U applied to rho
   for f; the right side is rho for gf followed by kappa for the restricted arrows.
   `CommSq.horiz_comp` and `CommSq.vert_comp` retain the actual composite scheme maps.
   Componentwise equalities avoid extra symbolic functor associators: their object
   reassociations are definitionally identical.
4. Identity maps and identity open immersions are included in all normalization
   quantifiers. In `OpenCoherenceSectionwise` their site maps are the canonical
   identity fibre-product identifications, and the asserted equation is the identity
   on the original section. The derived normalization transports this same identity
   to rho. For kappa, `DirectImageCompositionNormalized` transports the identity
   section formula of `lowerStarComp` to the derived comparison, including either
   identity factor. No arbitrary automorphism is left in any of these constraints.

Dependency declarations used (read signatures and docstrings):

- `sk-def-sfb-dc-setting`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `compactificationOverField` and its explicit over-field binder convention. The live
  source was also read with `scompile.py --source`; no compactification is needed for
  ordinary direct images, and the actual setting is rendered in the binders above.
- `sk-def-sfb-condensed-ring`: `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`
  and its `ContinuousCoefficientUniverse` import, together with the published
  `Profinite.continuousMapRingObj` for the small intermediate-field carrier. Both are
  existing continuous-function constructions; no replacement condensed ring is defined.
- `sk-def-sfb-qlbar-condensed`: its closed upstream audit gives
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`; no new lean binding
  is required for this closed dependency.
- `sk-def-sfb-pulled-back-coefficients`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`,
  `condensedRingObj`, and `condensedPullbackHom`.
- `sk-def-sfb-derived-categories`: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
  with its universal unit and object formula, Mathlib `DerivedCategory` and
  `CochainComplex.IsKInjective`. On these Grothendieck module categories the existing
  upstream `Functor.rightDerivedFunctor` is the same total functor with the canonical
  universal unit; this is expressly permitted by the dependency's recorded lean.note.
- `sk-def-sfb-module-pushforward-pullback`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `lowerStar`, `upperStar`, `lowerStarComp`, `upperStarComp`,
  `upperStarLowerStarAdjunction`, and the exactness instances.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`:
  `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
  `CategoryTheory.ringedToposDerivedPushforwardComposition` supplies the unit and
  resolution characterization used in the proof plan. Its existential comparison
  need not be chosen: the existing generic unit-preserving
  `Functor.rightDerivedFunctorCompIso` constructs that comparison directly for
  the internal module categories. The explicit normalization asserts its required
  component formula. No equal-universe ringed-site encoding is imposed on ProEt.
- `sk-prop-sfb-cartesian-coefficients`: `Sheaf.Paper.CartesianCoefficients`,
  `cartesianCoefficientLift`, `cartesianCoefficientPullbackIso`, and
  `cartesianCoefficients`. These specify the inverse-alpha module action.
- `def-pur-kinjective-complex`: Mathlib
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, `CochainComplex.IsKInjective`:
  maps from acyclic complexes are homotopic to zero.
- `lem-sfb-proetale-open-restriction-counit` remains a proof dependency only. Its
  module `Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit` is imported non-publicly.
  All five site object compositions use Mathlib `MorphismProperty.Over.map` directly,
  with the canonical `WeaklyEtale` instance for the open immersion. Its canonical
  coprojection and section equation are the proof model for the internal-module versions,
  which use the recorded internal-module adjunction on the actual rings.
- The already recorded proof dependency `sk-def-sfb-module-lower-shriek` is also added
  to stmt_deps because `upperStar_preservesKInjectives` uses its existing exact open
  adjunction, `openImmersionLowerShriekUpperStarAdjunction` in the published module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.
- All other stated proof dependency modules are imported (some through the public
  framework): `InternalAbelianSheafModuleEquivalence`, `RightDerivedFunctor.Comp`,
  `RingedSiteKInjectiveResolutionsOfUniverses`, `KInjectiveDerivedMapComputation`,
  `ProEtale.UpperLowerStar.Defs`, and `ModuleObject.Basic`. The seven proof steps in
  the theorem docstring name every proof input and explain their role.

Edge cases checked by reading the constructions and quantifiers: the zero complex;
complexes unbounded in both directions; empty schemes and empty opens; identity opens;
either identity factor in a direct-image composition; successive identity restrictions;
the trivial finite subextension E = Q_ell. None requires an inhabitant of a scheme,
a nonzero section, a proper map, a cohomological bound, or discrete coefficients.
The site remains `Scheme.ProEt` with object universe u+1 and morphism universe u;
coefficients are `Ab.{u + 1}`. No extra universe equality is imposed.

Searches (2026-10-18):

- msearch LeanFinder: "Derived pushforward composition associative and coherent with
  restriction to an open subscheme for sheaves of modules". Eight results, including
  `Scheme.Modules.pushforwardComp`, `SheafOfModules.pushforward_assoc`,
  `Scheme.Modules.restrictFunctorComp`: only ordinary Zariski/underived statements.
- msearch Loogle: `rightDerivedFunctorCompIso, lowerStarComp, upperStarLowerStar`.
  Zero results; `rightDerivedFunctorCompIso` is not a Mathlib identifier. Its exact
  upstream definition was subsequently found by rg and reused.
- msearch LeanSearch: "Derived pushforward composition associative and compatible with
  successive open restriction for condensed module sheaves". Eight results, including
  `PresheafOfModules.pushforward_assoc`, `SheafOfModules.pushforward_assoc`, and
  continuous-site pushforward comparison formulas: no exact derived condensed statement.
- msearch Mathlib grep: `rightDerivedFunctorCompIso|rightDerived.*[Cc]omp`, restricted
  to CategoryTheory. Eleven hits, general localization comparisons and right-derived
  natural transformations; no exact theorem.
- rg of the upstream `WeilConjectures`, the shared `lean/WeilConjectures` framework,
  and `lean/Sheaf`: derived/open coherence and derived-pushforward-composition patterns.
  Found and reused generic `RightDerivedFunctor.Comp`, `RightDerivedFunctor.Adjunction`,
  `RightDerivedFunctor.KInjective`, and `mapDerivedCategory` comparisons. Existing
  `ProEtaleDerivedOpenRestriction` has finite constant coefficients and omits these
  coherence equations, so is not an existing match.
- grep for the exact node id in upstream `WeilConjectures`: no occurrence. New declaration
  names were checked by rg against Mathlib-facing upstream names and both project roots;
  no collision was found. No new independent notion was introduced, so no new node
  searches or blueprint ancestor records are necessary.

No STATEMENT-DISPUTED flag or source fault was found. The node statement is unchanged.
Only lean and the addition of the already landed open extension-by-zero statement
dependency are changed relative to the current base.

Original packet validation: `scompile.py Q13 lem-sfb-derived-direct-image-open-coherence` compiled
the delivered module cleanly in both sandbox and module-path passes (25.2 s and
18.8 s respectively, each below the unchanged 60-second limit). No warnings were
reported. The only postponed proof is the main theorem.

## Second reading by Q13

Author's second reading for direct delivery; the maintainer supplies the independent
review. Reopened the full node and the finished module. Matched the prime, positive
characteristic and characteristic inequality; both coefficient cases with the existing
finite-subextension convention; the separated finite-type over-field binders; ordinary
unbounded internal-module categories; all three numbered clauses and identity cases
as described above. Checked the direction of every functor and comparison. In the
associativity equation the first path is kappa_(h,gf) followed by Rh(kappa_(g,f)),
while the second uses the explicit scheme-associativity transport and kappa_(hg,f)
followed by kappa_(h,g) at Rf. In the open composition equation the two component
paths have exactly the same source and target, and the vertical pasting gives gf.
In successive restriction, the inverse comparison at the source and the forward
comparison at the target have the required directions.

This reading corrected the attempted use of a nonexistent scheme `FiniteType` class
into the exact pair `LocallyOfFiniteType` and `QuasiCompact`. The repaired version uses
Mathlib site composition directly in all public signatures
and construction bodies, and imports the open-counit theorem non-publicly for its proof.
Only the open extension-by-zero interface is added as a statement dependency. No
mathematical statement correction or dependency replacement resulted.


## Repair of returned head b91fff144cfc

H2: Expanded all five occurrences of the open-counit module's `objectComposition`
abbreviation to its exact body, `MorphismProperty.Over.map (f := j/i) ⊤
(inferInstance : WeaklyEtale j/i)`, in the two section helpers and the sectionwise
normalization. The expansion is definitionally equal: the module's abbreviation was
read at its source and has precisely that body. The open-counit import is now
non-public, and its node is removed from the delivery's added `stmt_deps` while
retained unchanged in `proof_deps`. Updated `lean.note` accordingly.

Compared the saved node with current main: besides `lean`, the sole remaining
change is the addition of `sk-def-sfb-module-lower-shriek` to `stmt_deps`, justified
by the real K-injective-preservation instance. The main theorem signature is
unchanged. Rechecked the modified section domains, coprojection evaluations and
fibre-product arrow: they use the exact same Mathlib functor as before, including
identity and empty cases. No definition node, theorem, hypothesis or universe
restriction has been added. This is the direct-expansion repair requested by L.

Repair validation: `scompile.py` compiled the repaired file cleanly in both sandbox
and module-path passes (7.5 s and 9.6 s); exit 0, no warnings. The self-check confirms
that `lean.statement` is verbatim, all five abbreviation occurrences are expanded,
the counit import is non-public, the sole postponed proof is the main theorem,
and every Lean line has at most 100 characters.
