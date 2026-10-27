## Worker report

Stage 2, Q101, 2026-10-22. The stage-1 delivery by Q155 has landed and been reviewed;
that does not state this node in Lean. This delivery preserves every existing node field
and adds only its `lean` record. It supplies
`Sheaf.Paper.FiniteSpanModuleDerivedComparison`, namespace
`AlgebraicGeometry.ProEtale.FiniteSpanComparison`.

The main theorem `finiteSpanModuleDerivedComparison` asserts existence of comparison data
satisfying the full `Properties` and `ExchangeProperty`. Witnesses are not used to define
any object by choice. The scalar-transport equivalence is a real construction:
`Mod.comapEquivalenceOfIsIso theta.inv` followed by the existing section-module equivalence.
The maps retained as witness data are fixed by the explicit normalization equations, not
arbitrary natural isomorphisms. The ordinary section adjunction is constructed independently
by `SheafOfModules.PullbackConstruction.adjunction`.

Hypotheses and clauses, in node order (the descriptive clause labels are comments
in the conjunction `Properties`, rather than additional declarations):

- A prime ell is `l : ℕ` with `[Fact l.Prime]`. Omega and its topology are the existing
  `PadicAlgCl l`. The coefficient is `Profinite.padicAlgClRingObj l`, whose sections take
  values in a finite subextension, rather than the larger ring of all continuous maps.
- Every scheme is `Scheme.{u}`. Its original small pro-etale site is `X.ProEt`, with
  object universe u+1 and Hom universe u. Abelian groups, rings, modules and derived Hom
  universes are u+1. No equality between the site's two universes is imposed. The
  small-model existence and resolution structures are part of the asserted existence,
  not additional hypotheses on the theorem.
- A_Z is `condensedRingObj (Profinite.padicAlgClRingObj l) X`; `internal l X` is precisely
  its internal module category. `nativeAb` is the existing native locally finite-span
  function sheaf, obtained by forgetting the native coefficient-field action.
- R_Z is `ring l X`, using the dependency's `sectionRingSheaf` reconstruction on the
  native ring object. Its unit, multiplication and restrictions come from the existing
  native pointwise ring object. This is the native sheaf representative of the stated
  sheafification; no claim about objectwise colimits on non-quasi-compact schemes is used.
- `rho` is defined as the adjunct of the actual native `adicConstantSheafToLowerStar`.
  The `coefficient_sections` conjunct explicitly states precomposition with the first
  base-change projection for the ring map used by module direct image.
- `theta` is a family of abelian-sheaf isomorphisms with `IsMonHom` forward maps.
  Consequently these are ring-sheaf isomorphisms. The first conjunct of `Properties`
  is the exact finite-field chart equation in `locallyFiniteCoefficientRing_realization`;
  it fixes c_Z to that normalized realization, including every finite coefficient field.
- `coefficient_square` and its inverse-image form render both the adjunct coefficient
  square and c_Z alpha_v = rho_v v^-1(c_W). The next conjuncts assert invertibility of
  rho and its compositor equation for arbitrary composable scheme morphisms.
- `equivalence` explicitly restricts the internal scalar action along theta inverse and
  reconstructs sectionwise modules. Being an equivalence gives preservation of finite
  limits and colimits; the two additive-instance fields make both directions exact.
  `underlying` is equality of full underlying abelian-sheaf functors, on objects and maps,
  and therefore retains all restrictions literally. `finiteFree_sections` preserves
  finite free chart bases with the identical basis vectors at every site object.
- `direct` is `SheafOfModules.pushforward` with precisely the normalized precomposition
  coefficient map. `inverse` is presheaf tensor pullback followed by sheafification.
  Its ordinary adjunction is the actual tensor-formula adjunction. The coefficient square
  and invertible rho identify this with inverse image and action transport by rho inverse;
  alpha gives the corresponding internal action transport. There is no replacement map
  or extension along a different ring map.
- `pullComparison` and `pushComparison` have exactly the two functor-isomorphism types
  displayed in the node. `push_identity` is the identity on every underlying section.
  `ordinary_mate` identifies the specified ordinary adjunctions; transposes of identities
  give equality of units and counits. Thus the pullback comparison is fixed by ordinary
  transposition, not an arbitrary iso of endpoint functors.
- `pushComposition_sections` fixes the direct-image compositor to geometric base-change
  rebracketing; `pullComposition_mate` fixes its inverse-image adjunction mate.
  `ordinary_composition` is the full comparison equation for inverse-image compositors.
- `kinjective_forward` and `kinjective_inverse` are the two preservation assertions for
  all unbounded cochain complexes, with the recorded `CochainComplex.IsKInjective`.
- `derivedPushComparison` is an isomorphism of TOTAL functors on the unbounded derived
  categories. `derived_push_normalization` identifies it relative to the actual
  right-derived units and the degreewise ordinary comparison. The recorded right-derived
  unit is invertible on K-injectives, so this is exactly the comparison obtained by
  applying ordinary direct image to K-injective resolutions. This is not a collection
  of per-degree cohomology comparisons.
- The final conjunct of `Properties` introduces `k : Type u`, `[Field k]`, positive
  characteristic p, p prime, and p != l. The schemes are objects of `Over (Spec (.of k))`
  with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structure maps, exactly
  separated finite type. Arrows are k-morphisms. Earlier assertions retain all schemes.
- In this field setting the derived mate equation compares the canonical derived
  adjunctions obtained by deriving the two independently specified ordinary adjunctions.
  The exact-localization internal pullback model is canonically identified with the
  published left-derived pullback by its exact-functor comparison; this changes no maps.
  The second part explicitly says that, for EVERY complex L and K-injective I, the
  derived transpose of the class of a chain map into I, followed by the standard
  K-injective right-derived computation iso, is the class of its ordinary transpose.
  Identity transposes give the units and counits. Localizing `ordinary_composition`
  gives the specified derived pullback compositors.
- `ExchangeProperty` retains four arbitrary separated finite-type k-schemes, a Cartesian
  square (`IsPullback`), and EVERY object K of the unbounded source derived category.
  `square` is the two-compositor inverse-image comparison using the square equation;
  `internalExchange` and `nativeExchange` are the actual `mateEquiv` constructions.
  The property is equality of these morphisms after the specified source and target
  comparisons. No properness, constructibility, boundedness, or exchange-invertibility
  assumption occurs.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and topology.
- `def-weil-size-convention` is the recorded metatheoretic convention; explicit universe
  binders and the stated derived-category existence structures implement it.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `condensedPullbackHom`, `condensedPushforwardHom`.
- `Sheaf.Paper.CartesianCoefficients`: `CartesianCoefficientProperty`,
  `cartesianCoefficientLift`, `cartesianCoefficientPullbackIso`, `cartesianCoefficients`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionRingSheaf`, `sectionModuleEquivalence`.
- `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`:
  `AlgebraicGeometry.ProEtale.locallyFiniteCoefficientRing_realization` and its
  `chartComparison` normalization, read in full.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, whose
  underlying `SheafOfModules` is used directly.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: original pro-etale base change,
  inverse image, direct image, adjunction, and their small-model transport interface.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and
  `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`: the universal total right-derived
  pair and its resolution-normalized morphism computation. The generic upstream
  `rightDerivedFunctor` is the canonical monomorphic-resolution representative of that
  same universal pair; no choice of a different derived functor is stipulated.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the recorded field setting, rendered by explicit Over-scheme binders (no constructibility
  condition is used).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and projections.
- Proof interfaces are explicitly imported: `SectionModuleOperationsData`,
  `InternalModuleOperationsTransport`, `SectionDerivedPushpullNormalization`,
  `RingedSiteKInjectiveResolutionsOfUniverses`, Mathlib derived exact functors,
  derived adjunctions, K-injective derived Hom, and `mateEquiv`.

Edge cases checked: rank-zero charts use `Fin 0`; zero objects/complexes are included;
the empty scheme and all its test objects are included; identity and arbitrary composable
scheme maps appear in the unrestricted compositor assertions; no quasi-compactness is
assumed before the explicit field setting; ell equal to a scheme's characteristic is not
excluded from the ordinary/total-right-derived assertions; positive-characteristic
normalizations require exactly p != ell; the terminal field need not be algebraically
closed. Full unbounded derived objects, not merely images of bounded complexes, occur
in the exchange statement.

Searches (actual calls, recorded by the prescribed wrapper in searches.jsonl):

- LeanFinder: "Finite span coefficient transport of ordinary module operations and derived
  adjunctions for condensed algebraic closure l adic coefficients". Eight hits concerned
  `AdicCompletion` and Hausdorffification; none is this statement.
- Loogle: "SheafOfModules.pushforwardCongr, CategoryTheory.mateEquiv". Zero hits.
- Mathlib grep: "finiteSpan.*[Cc]omparison|finite_span.*comparison|locallyFiniteCoefficient".
  Zero hits.
- LeanSearch: "An exact equivalence of module sheaf categories preserves K injective
  complexes and compares right derived direct image adjunctions". Eight hits included
  `HomotopyEquiv.isKInjective`, `CochainComplex.isKInjective_of_iso`, equivalences of sites,
  preservation of injectives, and `SheafOfModules.PullbackConstruction.adjunction`.
  These supply generic pieces, not this normalized finite-span comparison.
- `rg` of the item tag in `lean/WeilConjectures` returned no existing theorem. Concept
  searches in both source roots found `LocallyFiniteCoefficientRingRealization`,
  `PadicAlgClSheafIso`, `PadicAlgClSheafRing`, and the internal/section ordinary and derived
  comparison modules. These are reused; none states this full assembly.

No statement correction, disputed statement, new node, or dependency replacement is made.
The former failure concerned re-splitting an already reviewed stage-1 assignment; this is
its missing stage-2 statement, so no stage-1 repair note is required.

## Second reading by Q101

This is a self-review; no separate agent was started, as the dispatcher explicitly
forbids that. Independent review remains the maintainer's delivery review. The node and
module were read together. Scalar actions, mate directions, the inverse compositor in the
square, and the right-derived unit normalization were checked against the named source
signatures. The finite-field and geometric-precomposition normalizations are retained.
The large equality conditions are propositions rather than fields of the comparison-data
class, avoiding expensive generated recursors without weakening any assertion.

## Validation

`scompile.py Q101 lem-sf-finite-span-module-derived-comparison` compiled the complete
module both under its sandbox name (23.5 s) and library name (19.5 s), with no errors
or warnings. The copied node differs only in `lean`; its signature was checked verbatim
against the file. The sole postponed proof is the named main theorem, with its complete
source-based proof docstring. No definition contains postponed data.
