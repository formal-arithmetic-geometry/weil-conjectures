## Worker report

The module `Sheaf.Paper.CondensedOpenSquareScalarComparison` states
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_square_scalar_comparison`.
Its sole theorem has `sorry` as its entire proof. Its docstring carries the nine-step
accepted DAG proof. Two transparent helper definitions belong to the square comparison
of this node and are listed in `lean.declarations`: `openSquareModulePullbackIso` and
`openSquareComplexComparison`. Neither chooses any data or contains a postponed proof.
No node statement, dependency interface or DAG edge was changed.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Field k of positive characteristic different from ell | `{k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`; positive field characteristic is prime |
| Schemes over k and k-morphisms | `{W Y X : Over (Spec (.of k))}` and `(r : W ⟶ X) (i : Y ⟶ X)`; `.left` is the underlying scheme map, and X is the node's Y-bar |
| Separated finite type for every scheme | `[LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]` for A = W,Y,X; the fourth scheme is their actual pullback and inherits these conditions |
| Admissible commutative condensed coefficient | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, `[MonObj Λ] [IsCommMonObj Λ]`, and `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` |
| Finite-subextension-valued Qbar coefficient included | The last disjunct of the recorded admissibility predicate is `Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))`; this is the recorded Qbar construction, not an identification with all continuous Qbar-valued maps |
| Small pro-etale site and category C_T | `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)`, with the project's site/universe convention unchanged |
| Coefficients pulled back from the point | `condensedRingObj Λ T`, definitionally `(upperStarFromPoint T).obj Λ` |
| Quasi-compact open immersion i | `[IsOpenImmersion i.left] [QuasiCompact i.left]` |
| U, j, p | `pullback r.left i.left`, `pullback.fst r.left i.left`, `pullback.snd r.left i.left`; j is an open immersion by base change, without a further hypothesis |
| Fixed abelian inverse-image square comparison c | `ringSheafSquareComparison r.left i.left`, the recorded `upperStarCompIso` of `pullback.condition` |
| Canonical alpha_f | `condensedPullbackHom Λ f` throughout |
| Coefficient equation | First conjunct: `c.inv.app Λ_X ≫ j^{-1}.map α_r ≫ α_j = p^{-1}.map α_i ≫ α_p`; Lean composition is diagrammatic |
| Actual f-star = Ext(alpha_f) mapMod(f-inverse) | Every `upperStar Λ f` is precisely the recorded condensed module pullback, with extension of scalars retained |
| Actual open h-shriek = linear h-shriek Res(alpha_h) | Every `openImmersionLowerShriek Λ h` is precisely the recorded scalar restriction followed by linear open extension |
| Lambda_W-linear natural beta: r-star i-shriek iso j-shriek p-star | `∃ β : openImmersionLowerShriek Λ i.left ⋙ upperStar Λ r.left ≅ upperStar Λ p ⋙ openImmersionLowerShriek Λ j`; this is an isomorphism in module-valued functors, so each component is Lambda_W-linear |
| Canonical scalar transport of arbitrary-ring comparison | The adjunct equation fixes beta uniquely for the specified adjunction, unit and theta. Thus the scalar-transported comparison of the arbitrary-ring mate theorem is exactly this beta, rather than an unspecified isomorphism. `Mod.extendScalarsIsoComapInv` is imported for that proof; beta's canonical normalization is not an extra assumption |
| Fixed theta from rj=ip | `openSquareModulePullbackIso Λ r.left i.left` is `(upperStarComp Λ p i).symm`, followed by `eqToIso (congrArg (upperStar Λ) pullback.condition.symm)`, followed by `upperStarComp Λ j r` |
| Adjunct of beta inverse | `∀ T : Mod ... Λ_Y, (openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _ (β.inv.app T) = (upperStar Λ p).map (unit_i.app T) ≫ theta.hom.app (i_!.obj T)` |
| All four functors exact | Eight conjuncts give `PreservesFiniteLimits` and `PreservesFiniteColimits` for r-star, i-shriek, p-star, j-shriek. Their additivity is already supplied by the recorded definitions |
| Ordinary unbounded derived beta_D | `∃ βD : i_!.mapDerivedCategory ⋙ r^*.mapDerivedCategory ≅ p^*.mapDerivedCategory ⋙ j_!.mapDerivedCategory`; no Plus or bounded-constructible subcategory occurs |
| Localization of degreewise beta on every complex | The `∀ K : CochainComplex (Mod ... Λ_Y) ℤ` equation identifies `βD.hom.app (Q.obj K)`, after the two target factorizations, with the source factorizations followed by `Q.map (openSquareComplexComparison ... β K)` |
| Exact termwise composition comparisons | `openSquareComplexComparison` is `mapHomologicalComplexCompIso.hom`, then `NatTrans.mapHomologicalComplex β.hom`, then the target `mapHomologicalComplexCompIso.inv`. These canonical termwise identifications have identity degreewise components |
| Every canonical integer shift | `NatTrans.CommShift βD.hom ℤ` with the inferred composition of the canonical `mapDerivedCategory.CommShift ℤ` structures |
| No properness, boundedness, constructibility assumptions | None occur in the binders or conclusions. Every cochain complex, including unbounded ones, is quantified |

The normalized equation on complexes is the expanded form of conjugating D(beta) by
`mapDerivedCategoryCompIso` on both sides. It uses each individual exact functor's
factorization, so does not need an additional instance for exactness of a composite.
`openSquareComplexComparison` is a chain map with entry beta at K.X n, not a substitute
cohomology isomorphism. The resulting iso is an iso of derived functors, as required
by the 2026-10-21 complex-isomorphism convention.

Dependency declarations read and used (including interfaces carried transitively by
public imports):

| Module | Declarations |
| --- | --- |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | `CondensedRing.compactificationOverField`; the separated finite-type Over-field convention, without assuming bounded constructibility or using the compactification |
| `Sheaf.Paper.LocalizingAdmissibleCoefficients` | `ProEtale.IsLocalizingAdmissibleCoefficient` |
| `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` | `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj` (via admissibility) |
| `Mathlib.AlgebraicGeometry.Sites.Proetale` | `Scheme.ProEt`, `Scheme.ProEt.topology` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` | `coefficientRing`, `condensedRingObj`, `condensedPullbackHom`, `coefficientPullbackIso`, `condensedPushforwardHom_comp` |
| `Mathlib.CategoryTheory.Monoidal.Mod` | `CategoryTheory.Mod`, `Mod.comap` |
| `Mathlib.AlgebraicGeometry.OpenImmersion` | `AlgebraicGeometry.IsOpenImmersion` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` | `CondensedRing.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, `lowerStarComp`, `upperStarComp`; additive and exactness instances |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | `CondensedRing.openImmersionLowerShriek`, `linearOpenImmersionLowerShriek`, `openImmersionLowerShriekUpperStarAdjunction`; additive and exactness instances |
| `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` | Recorded ambient derived-category convention; the statement uses ordinary `DerivedCategory`, `DerivedCategory.Q` and exact induced functors, not total right derivation |
| `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `pullback`, `pullback.fst`, `pullback.snd`, `pullback.condition` |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations` | `ringSheafSquareComparison`, and the arbitrary-ring operations used by the proof |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates` | `ringSheaf_baseChange_mates` (proof) |
| `WeilConjectures.CategoryTheory.ModuleObjects.MapMod` | `Mod.extendScalarsIsoComapInv`, `Mod.comapEquivalenceOfIsIso` (scalar normalization in proof) |
| `Mathlib.CategoryTheory.Localization.Predicate` | `Localization.liftNatIso`, `Localization.liftNatTrans_app`, `Localization.natTrans_ext` |
| `Sheaf.CategoryTheory.ExactDerivedComposition` | `Functor.existsUnique_mapDerivedCategoryCompIso` |
| `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` | `Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso`, and their factorization equations |
| `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` | `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`, canonical shift structures |
| `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` | Re-export of `ProEtale.upperStarComp`; `upperStarCompIso` is supplied by the recorded Iso module |
| `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars` | `Mod.extendRestrictAdjunction` |
| `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` | `Adjunction.mapModLeftAdjunction` |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod` | `Functor.mapMod`, `Functor.modObjObj` (the closed upstream transport node has no lean record) |
| `Mathlib.CategoryTheory.Adjunction.CompositionIso`, `.Basic`, `.Mates` | `Adjunction.leftAdjointCompIso`, `Adjunction.comp`, `unit_conjugateEquiv_symm` |
| `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare` | `Functor.ProjectionFormula.mapModLeftComapIso` |
| `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `.QuasiSeparated` | qcqs-over-affine interfaces |
| `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme` | `Scheme.IdealSheafData.reduced_induced_closed_subscheme` |
| `Sheaf.Paper.CartesianCoefficients` | Recorded coefficient pullback exactness and scalar identification interfaces |

Edge cases checked before drafting: i = identity (the coefficient cocycle and the
normalized identity mate); empty Y (zero extension on both sides); identity r
(compositor normalization); zero module T; zero and unbounded complexes; positive,
zero and negative shifts, including odd negative n with its differential sign.
No map r was assumed proper. The square orientation is c : j-inverse r-inverse to
p-inverse i-inverse, while theta goes from p-star i-star to j-star r-star; accordingly
c inverse and theta hom occur in the two displayed equations. The source of the
adjunct is p-star T, so it is beta inverse that is transposed. All universes are
explicit, `autoImplicit` is false, and no equality between different site universes
has been imposed. The site and coefficients use exactly the published u/u+1 encoding.

Searches for an existing statement:

- `msearch.py ... leanfinder`, query: "Open extension by zero base change for internal
  modules over pulled back condensed rings with coefficient compatibility and exact
  unbounded derived comparison". Eight hits: `Condensed.profiniteSolid`,
  `CondensedMod.IsSolid`, `CondensedMod.LocallyConstant.functor`, `Condensed.free`,
  `LightCondensed.instIsGrothendieckAbelianLightCondMod`,
  `LightCondensed.instMonoidalClosedLightCondMod`,
  `LightCondensed.instMonoidalCategoryLightCondMod`, and
  `Condensed.profiniteSolidification`. None states this theorem.
- `msearch.py ... loogle`, query: `CategoryTheory.Localization.liftNatIso,
  CategoryTheory.Functor.mapDerivedCategoryNatIso`. Zero hits; unknown identifier
  `CategoryTheory.Functor.mapDerivedCategoryNatIso` in the remote Mathlib index
  (it is a project declaration, read directly).
- `msearch.py ... grep`, query: `openImmersion.*BaseChange|mapDerivedCategoryNatIso`
  in `CategoryTheory`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, queries:
  `lem-sfb-condensed-open-square-scalar-comparison|condensedOpenSquare|openImmersion.*BaseChange`.
  No existing declaration for this node or helper name. The abelian open base-change
  comparison has the wrong coefficient category. The module-object upstream
  `Derived.OpenLowerShriekBaseChange` treats bounded constructible finiteness
  coefficients and does not give this arbitrary unbounded statement with its
  coefficient equation and complex normalization. `IntegralBoundedStratumBaseChange`
  treats integral bounded inputs; its pullbackSquare is already derived and cannot
  replace the present underived module compositor. The generic localization and
  composition interfaces are used rather than redefined.

No STATEMENT-DISPUTED issue or statement correction was needed. The obsolete
CompactObject example module is withdrawn; its node now points to the upstream
`WeilConjectures.CategoryTheory.CompactObject`, so current module-mode conventions
were followed directly. No upstream file or script was edited, no git command was
run by the worker, and all compiler invocations used scompile.py.

Validation: each module compile uses the prescribed server wrapper. Final compiler
and delivery preflight results are recorded by the delivery wrapper. The maintainer
performs the independent review; no independent second-reader claim is made here.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
