## Worker report

The module `Sheaf.CategoryTheory.ResolutionRoofInjectiveTranspose` states the item as
`CategoryTheory.ResolutionRoof.injectiveTranspose` and the internal invariant-inclusion
clause as `CategoryTheory.ResolutionRoof.internalTransposeFactorization`. Both theorem
proofs are exactly `sorry`. Five auxiliary definitions contain their full canonical data;
none chooses an arbitrary map or a new adjunction. The node changes only in `lean`.

Clause-by-clause reading:

- The abelian categories are `B : Type uB`, `E : Type uE`, with independent morphism
  universes `vB`, `vE`, `Abelian` instances and independent localization universes
  `HasDerivedCategory.{wB} B`, `HasDerivedCategory.{wE} E`. The Grothendieck assumption is
  `IsGrothendieckAbelian.{g} E`; its Grothendieck universe is independent as well. No
  Grothendieck or enough-injectives condition is imposed on B.
- The specified additive adjoints are `L`, `R`, `[L.Additive]`, `[R.Additive]`, `adj : L ⊣ R`.
  Exactness of L is `[PreservesFiniteLimits L] [PreservesFiniteColimits L]`.
- `X : B`, `N : E`, `P : CochainComplex E ℤ`, `[P.IsStrictlyLE 0]`, and
  `e : P ⟶ (CochainComplex.singleFunctor E 0).obj (L.obj X)` with `[QuasiIso e]`
  are exactly the specified objects, positive-degree vanishing and quasi-isomorphism.
- `I : InjectiveResolution N` retains the entire specified nonnegative injective
  resolution, not just an arbitrary K-injective complex. `I.cochainComplex` is Mathlib's
  extension by zero to integer indices; `I.ι'` is its actual augmentation. All choices of
  I are quantified. `q : ℤ`, `hq : 0 ≤ q` retain the integer and its inequality.
- `f : P ⟶ ((CochainComplex.singleFunctor E 0).obj N)⟦q⟧` is the node's u.
  The existential h has source `(LX)[0]` and target `I.cochainComplex⟦q⟧`.
  `Nonempty (Homotopy (e ≫ h) (f ≫ I.ι'⟦q⟧'))` is exactly he homotopic to a[q]u
  (Lean composes left to right). `Q.map h = roof e f ≫ Q.map (I.ι'⟦q⟧')` is the first
  displayed equation, with `roof e f = inv (Q.map e) ≫ Q.map f`.
- The second conjunct quantifies over every h with that homotopy. Requiring the first
  displayed equation again would be redundant: it follows by localization and cancellation
  of Qe. There is no selected representative and no projectivity assumption on P.
- `termwiseTranspose` applies `adj.mapHomologicalComplex.homEquiv` after the existing
  `HomologicalComplex.singleMapHomologicalComplex` identification L(X[0]) ≅ (LX)[0].
  Thus it is the termwise transpose of the given h, not another map with the same
  cohomology class. Its zero component is R(h⁰)η_X under the single-object identifications.
- `transposeFlat` shifts this very map by -q, applies the termwise R shift comparison,
  then `shiftShiftNeg`. It is the same degree-zero component now in degree q, giving
  X[0][-q] → RI with no extra scalar or sign. Shifting source notation as X[0][-q]
  retains exactly the node's X[-q].
- `resolutionComparison R I.ι'` is β_a explicitly as
  `R.rightDerivedFunctorUnitQ I ≫ inv (R.rightDerivedFunctor.map (Q.map I.ι'))`.
  The augmentation is a quasi-isomorphism; I is bounded below and termwise injective,
  hence K-injective. The existing right-derived unit is therefore invertible on I,
  so this is the canonical injective-resolution isomorphism in the stated direction.
  The helper is defined as its actual morphism, sufficient for the displayed equation.
- `shiftedDerivedTranspose` is Φ_q, using the fixed
  `adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv`, with L's exact-localization
  and single-complex comparisons on the source. It then applies Q's shift comparison,
  the existing K-injective right-derived shift comparison, shifts by -q, and cancels
  target shifts. No shift structure or Hom equivalence is supplied by a hypothesis.
  The final equality is `Q.map (transposeFlat ...) ≫ resolutionComparison ... =
  shiftedDerivedTranspose ... (roof e f)`.
- For the internal clause, `CondensedBar.Modules A` and `Equivariant A G` are precisely
  the existing internal-module and internal-action categories, with arbitrary topological
  group G (no profiniteness or discreteness restriction on G). The existing
  `trivial`, `invariants A G`, and their normalized adjunction supply L and R.
  `internalTransposeFactorization` explicitly states that composing each component of
  that same termwise transpose with the invariant inclusion gives the underlying
  component of h, after the canonical single-complex comparison. Its second conjunct
  says every cochain map with those factors equals the termwise transpose. Existing
  `actionAbelian`, `actionGrothendieck`, `trivialAdditive`, `trivialLimits`,
  `trivialColimits`, and the invariants additive instance instantiate the general theorem;
  the ordinary derived categories use whichever `HasDerivedCategory` instances are fixed.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic;
  `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian`,
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic.
- `def-weil-size-convention` is metatheoretic, implemented by the explicit independent
  universes above; no extra definition is needed.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, `Q`,
  Mathlib.Algebra.Homology.DerivedCategory.Basic.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective`, `InjectiveResolution`,
  Mathlib.CategoryTheory.Preadditive.Injective.Basic / Resolution; integer extension
  `InjectiveResolution.cochainComplex`, `ι'`, Mathlib.CategoryTheory.Abelian.Injective.Extend.
- `lem-trf-bounded-below-derived-adjunction`: `Adjunction.derivedPlus`,
  `derivedPlus_unit_app_fac`, `derivedPlus_counit_app_fac`,
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction.
  The record has only the declaration list, so its source was found by searching those
  names. The unbounded canonical counterpart used in the formula is
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`, in the sibling Adjunction module.
- `lem-sp-canonical-right-derived-adjunction-shift`:
  `CategoryTheory.canonicalRightDerivedAdjunctionShift`,
  Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift. Its fixed right-derived
  functor and existing CommShift, rather than an arbitrary transported structure, are used.
- `def-sfb-condensed-action-module`: `Profinite.CondensedAction.ActionModule`, `trivial`,
  `Invariants`, `Invariants.transpose`, `Invariants.injective`,
  Sheaf.CategoryTheory.CondensedActionModule (reexported by the restriction calculus).
- `lem-sfb-condensed-derived-restriction-calculus`:
  Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus, including its public
  CondensedDerivedInvariants infrastructure: `invariants`, `actionGrothendieck` and the
  exactness instances for trivial inflation. The node's coefficient/cup theorems are
  broader than this specialization and do not need to be restated or repaired.
- Proof-only imports retain the node's normalized resolving adjunction,
  Sheaf.SixFunctors.ResolvingDerivedAdjunction (`derivedAdjunctionOfResolvingClass`),
  and arbitrary-quasi-isomorphism right-derived interface,
  Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions.
  K-injective existence uses the already public
  WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution instance;
  homotopy adjunction comes from the public canonical-adjunction imports;
  exact-functor factorization comes from Mathlib's ExactFunctor module;
  Mathlib.Algebra.Homology.DerivedCategory.KInjective supplies the Hom bijection.

Edge cases checked: q = 0 retains the canonical zero-shift comparisons and has no excluded
identity case. Zero X or N, the zero resolution and zero cochain maps remain permitted.
P can be unbounded to the left and have no projective terms. The Hom-bijection source
is arbitrary P, so no bounded-below assumption was introduced on P. Changing I or h is
allowed by their universal quantification. G can be trivial; the factorization then
uses the same normalized inclusion and still has the asserted uniqueness. All category,
Hom, localization and Grothendieck universes are bound and independent.

Searches (msearch.py, Q82, this item):

- LeanFinder: "An exact left adjoint and its right derived adjoint take roofs represented
  in an injective resolution to the termwise transpose, compatibly with shifts" returned
  eight hits, including `Adjunction.derived`, `derivedε`, and injective-resolution maps.
  These are ingredients, not the arbitrary-roof shifted-transpose assembly.
- Loogle: "CategoryTheory.Adjunction.derived, CochainComplex.IsKInjective.Qh_map_bijective"
  returned zero hits.
- LeanSearch: "Derived adjunction computed by termwise transpose into a shifted injective
  resolution" returned eight generic derived-adjunction/right-derived-functor hits,
  including `Adjunction.derived_unit` and `Adjunction.derived`; none states this item.
- Mathlib grep: "homEquiv|bijective|rightDerived" in Algebra/Homology/DerivedCategory
  returned 25 hits: K-injective/projective Hom bijections and right-derived infrastructure.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, resolution roof/transpose
  names, canonical derived adjunction, injective comparison and shift interfaces found
  no statement of the item. `ResolutionRoof` in SimplicialDerivedColimitComputation is
  about a different simplicial colimit construction. Exact item-id grep in
  lean/WeilConjectures returned no match. The existing comparison and transpose APIs
  found in these searches are used rather than copied.

Source reading: the current `literature/blueprint/latest/` direct-images proof paragraph
(3), and literature/stacks-project/derived.tex at lemma-K-injective,
lemma-bounded-below-injectives-K-injective, lemma-K-injective-defined and
lemma-adjoint-preserve-K-injectives. The blueprint paragraph gives the direct-image route;
this auxiliary calculation is the agent-extracted argument explicitly recorded in the
node. No source-based correction or disputed statement was necessary.

Validation: scompile.py checked the module in sandbox and final module mode. The initial
namespace error for the single-complex comparison was corrected to
`HomologicalComplex.singleMapHomologicalComplex`. The next pass elaborated all declarations;
its sole long-line warning was repaired before final preflight. Every theorem remains sorry.

## Second reading by Q82

I reread the node and the complete module after elaboration, checking both equations in
left-to-right composition order. The single-complex isomorphism points from L(X[0]) to
(LX)[0]; the exact-derived factor points from D(L)Q(X[0]) to Q(L(X[0])). Their composite
therefore has the correct source for the canonical Hom equivalence. For beta, the unit
points from Q(RI) to RR(QI), and the inverse image of the actual augmentation points to
RR(QN), as required. For Phi, the Q and RR shift comparisons point to the shifted target,
and shifting by -q then shiftShiftNeg cancels it with no sign. The same termwise transpose
is used in both the shifted identity and the internal factorization. I also checked that
the universal h clause needs only its homotopy, with the first formula a consequence;
that no projective, bounded-below-on-P, or enough-injectives-on-B binder slipped in;
and that all seven declaration names are recorded. The namespace and line-length issues
were repaired; no mathematical mismatch was found. This is an in-session second reading,
not an independent agent review: the dispatch brief forbids starting other agents, and
the maintainer's independent review remains the delivery review.
