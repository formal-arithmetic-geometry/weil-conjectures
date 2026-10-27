# AlgebraicGeometry.ProEtale.towerP and the compatible-tower constructions

## Reason

The equality-only split needs the actual canonical constructions while the normalization theorem
imports the split. Keeping the constructions in the theorem module would create an import cycle.
Move the thirteen existing constructions verbatim into
`Sheaf.Paper.ProEtaleCompositionTowerDefinitions`, publicly imported by the original module.
This is a dependency separation for a genuine logical decomposition, not a split to evade a compile
limit. No construction, target meaning, signature, universe, public name or visibility changes.
No WeilConjectures module is edited. The canonical origin composition still uses the independently
specified `originCompositionAmbient`; it is not redefined as the desired tower formula.

## Old

In `Sheaf.Paper.ProEtaleCompositionTowerNormalization`:

```lean
/-- Ordinary derived direct image P on the small pro-etale site.
Source: Construction, notation P (blueprint: lem-trf-proetale-composition-tower-normalization). -/
abbrev towerP {X Y : Scheme.{u}} (t : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} Λ) t).rightDerivedFunctor

/-- Exact derived extension by zero J on the small pro-etale site.
Source: Construction, notation J (blueprint: lem-trf-proetale-composition-tower-normalization). -/
abbrev towerJ {X Y : Scheme.{u}} (v : X ⟶ Y) [IsOpenImmersion v] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v).mapDerivedCategory

/-- Exact derived restriction along a scheme map.
Source: Construction, i_p^* (blueprint: lem-trf-proetale-composition-tower-normalization). -/
abbrev towerPull {X Y : Scheme.{u}} (v : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategory

/-- Exact inverse image is left adjoint to total direct image.
Source: Construction, ambient exchange adjunctions
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerPullPushAdjunction {X Y : Scheme.{u}} (v : X ⟶ Y) :
    towerPull Λ v ⊣ towerP Λ v :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).ofNatIsoLeft
    (Functor.leftDerivedFunctorIsoMapDerivedCategory _)

/-- Canonical pullback comparison of the commutative square, descended termwise.
Source: Construction, unit--square--counit exchange
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerPullSquare {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) (w : b ≫ p = r ≫ i) :
    towerPull Λ i ⋙ towerPull Λ r ≅ towerPull Λ p ⋙ towerPull Λ b :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarComp (ModuleCat.{u + 1} Λ) r i).symm ≪≫
        eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ)) w.symm) ≪≫
        upperStarComp (ModuleCat.{u + 1} Λ) b p) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The actual ambient exchange Ex^p: unit for r, square, counit for p.
Source: Construction, exchange normalization
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerExchange {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) (w : b ≫ p = r ≫ i)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))) :
    (towerPull Λ i).obj ((towerP Λ p).obj K) ⟶
      (towerP Λ r).obj ((towerPull Λ b).obj K) :=
  (towerPullPushAdjunction Λ r).unit.app _ ≫
    (towerP Λ r).map ((towerPullSquare Λ b i r p w).hom.app _ ≫
      (towerPull Λ b).map ((towerPullPushAdjunction Λ p).counit.app K))

/-- The open unit eta_b, induced from the actual sheaf adjunction unit.
Source: Construction, inverse open unit
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerOpenUnit {X Y : Scheme.{u}} (b : X ⟶ Y) [IsOpenImmersion b] :
    𝟭 _ ≅ towerJ Λ b ⋙ towerPull Λ b :=
  (Functor.mapDerivedCategoryIdIso _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b).unit) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Lambda is Ex^p on J_b N followed by P_r of inverse eta_b.
Source: Construction, displayed lambda
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerLambda {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) [IsOpenImmersion b]
    (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology H) (ModuleCat.{u + 1} Λ))) :
    (towerPull Λ i).obj ((towerP Λ p).obj ((towerJ Λ b).obj N)) ⟶
      (towerP Λ r).obj N :=
  towerExchange Λ b i r p w ((towerJ Λ b).obj N) ≫
    (towerP Λ r).map ((towerOpenUnit Λ b).inv.app N)

/-- Gamma is defined by the Hom bijection from inverse lambda, not by site transport.
The IsIso argument is proof data furnished in the theorem, not an extra hypothesis there.
Source: Construction, displayed open-adjoint prescription
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerGamma {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) [IsOpenImmersion b] [IsOpenImmersion i]
    (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology H) (ModuleCat.{u + 1} Λ)))
    (hLambda : IsIso (towerLambda Λ b i r p w N)) :
    (towerJ Λ i).obj ((towerP Λ r).obj N) ⟶
      (towerP Λ p).obj ((towerJ Λ b).obj N) :=
  letI := hLambda
  (((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryAdjunction).homEquiv _ _).symm
      (inv (towerLambda Λ b i r p w N))

/-- E is the unique open-extension compositor conjugate to composite restriction.
Source: Construction, final open compositor
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerOpenComposition {U H T : Scheme.{u}} (j : U ⟶ H) (b : H ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    towerJ Λ j ⋙ towerJ Λ b ≅ towerJ Λ (j ≫ b) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b)).leftAdjointUniq
          ((openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} Λ) (j ≫ b)).ofNatIsoRight
              (upperStarComp (ModuleCat.{u + 1} Λ) j b)))

/-- Canonical change of candidate on the full etale-origin class. Transport the
canonical etale common-refinement comparison through the named site comparisons,
then descend it uniquely along the etale-origin equivalence. This is not a choice
of an arbitrary isomorphism.
Source: Construction, independence under compactification comparisons
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerCandidateComparison [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X
  let model := compactSupportSiteComparison Λ c ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ c d)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory ≪≫
    (compactSupportSiteComparison Λ d).symm
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model

/-- Alpha^p on the supplied candidates. Conjugate the published canonical origin
composition by the canonical comparisons from e.restrict and d to the chosen models,
and from the chosen composite to d.comp e. Existence of compactifications is a Prop
and cannot select models: the explicit comparison factors here retain the candidates.
This construction does not refer to exchange, lambda or gamma.
Source: thm-sf-comp-composition, Construction and independence
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerOriginComposition [Finite Λ] {U V W : Scheme.{u}}
    (h : U ⟶ V) (f : V ⟶ W) [QuasiCompact h] [QuasiCompact f]
    (d : Compactification f) (e : Compactification (h ≫ d.i))
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        e.restrict).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj L.obj)) ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
      (d.comp e)).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj L.obj) :=
  letI : HasCompactification h := e.restrict.hasCompactification
  letI : HasCompactification f := d.hasCompactification
  letI : HasCompactification (h ≫ f) := (d.comp e).hasCompactification
  let O := (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) U).obj L
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d).map
      ((towerCandidateComparison Λ e.restrict
        (HasCompactification.compactification h)).hom.app O) ≫
    (towerCandidateComparison Λ d (HasCompactification.compactification f)).hom.app
      ((originCompactSupport Λ h).obj O) ≫
    (originCompositionAmbient Λ h f).hom.app O ≫
    (towerCandidateComparison Λ (HasCompactification.compactification (h ≫ f))
      (d.comp e)).hom.app O

/-- Equality transport for open extension, used with bj=a.
Source: Construction, compatible triangle
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerOpenCongr {X Y : Scheme.{u}} {v v' : X ⟶ Y}
    [IsOpenImmersion v] [IsOpenImmersion v'] (w : v = v') :
    towerJ Λ v ≅ towerJ Λ v' := by
  subst v'
  exact Iso.refl _
```

## New

Exactly the same declarations and bodies, byte for byte, now in
`Sheaf.Paper.ProEtaleCompositionTowerDefinitions`. The original module adds:

```lean
public import Sheaf.Paper.ProEtaleCompositionTowerDefinitions
```

The existing `def-sf-origin-candidate-comparison` Lean attachment follows its unchanged construction.
The new construction node records the other twelve declarations. The normalization theorem keeps
its exact original signature and combines a proved witness/invertibility argument with the new
canonical-composition equality theorem. No target definition changes its mathematical meaning.

## Users

`tools/downstream.py Sheaf.Paper.ProEtaleCompositionTowerNormalization` finds the following users.
The direct importers are ProperCompositionSiteTransport, ClosedSectionCompactOrigin,
FiniteTripleProductNormalForms, ProductExchangeCounitCoordinates and ProjectionCompatibleTriangleAssembly.
No user needs a forced adaptation. All original public imports remain publicly available.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.ClosedSectionCompactOrigin | B9 | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | No edit: the original import publicly reexports all unchanged declarations. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | C2 | No edit: the original import publicly reexports all unchanged declarations. |

## Status

landed 20261025T123039-L-1827473 2026-10-25 (merge of deliver/H2/Sheaf.Paper.ProEtaleCompositionTowerNormalization)
