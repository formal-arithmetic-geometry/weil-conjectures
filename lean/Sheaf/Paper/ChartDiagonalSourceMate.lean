module

public import Sheaf.Paper.ChartDncVectorFactors
public import Sheaf.SmoothPurity.TensorMateEtalePrecomp
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.Paper.CohomologicalSmoothEtaleLocality
public import Sheaf.Paper.CohomologicalSmoothnessTheorem
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal
import Sheaf.Paper.ChartCartesianDomain
import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization
import Sheaf.Paper.FiniteSiteCounitProjectionTransport
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import Sheaf.Paper.CanonicalOriginCompactSupportComposition

/-! # Counit-normalized source comparison for coordinate diagonals

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md, Steps 1 and 3.
(blueprint: lem-pur-chart-diagonal-source-mate).

The canonical finite etale-origin coordinates retain the actual maps: alpha is the
inverse self-product counit mate restricted to the diagonal, c is inverse normalized
etale locality, and a is the published section comparison through U times_Y A.
The last assertion compares this a with its construction on every smaller open
neighbourhood of the diagonal. Site comparison transports these equalities to the
constructible pro-etale section objects, with the published pullback comparisons.

## Main definitions and statements

* `alpha`, `target`, `viaQ`: the specified ordinary-etale comparisons.
* `alphaProEtale`, `targetProEtale`: their canonical site transports.
* `IsCompatible`: the actual mate equation, the prescribed open, and restriction.
* `chartDiagonalSourceMate`: compatibility for every etale coordinate chart.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.ChartDiagonalSourceMate

/-- The specified diagonal alpha, without a choice of orientation.
Source: chart proof Step 3 and lem-pur-diagonal-base-change, final display
(blueprint: lem-pur-chart-diagonal-source-mate). -/
def alpha (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := Dnc.compactifiable P h aY
  letI := (P.comparedDiagonalBaseChange d h (h ≫ aY) aY rfl).2.2.2.1
  P.diagonalComparedRestriction h
    (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback h h).flip))

/-- The specified c_e: conjugate exceptional composition followed by etale locality.
The normalized sum-extension comparison fixes its counit, so this is not a choice
of an isomorphism of its endpoints. Source: chart proof Step 3, first paragraph
(blueprint: lem-pur-chart-diagonal-source-mate). -/
def target (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  letI := P.noetherian aY
  letI := P.noetherian (h ≫ aY)
  letI := P.noetherian (p ≫ aY)
  letI : IsSeparated (e ≫ p) := by rw [w]; infer_instance
  letI : IsSeparated e := IsSeparated.of_comp e p
  letI := Dnc.compactifiable P p aY
  letI := Dnc.compactifiable P h aY
  letI : HasCompactification (e ≫ p) := HasCompactification.of_eq w.symm
  let c : Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) h ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) (e ≫ p) :=
    eqToIso (by cases w; rfl)
  (c ≪≫
    (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N e p).symm.app (𝟙_ _) ≪≫
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) e).app _).symm)

/-- The two projection equations and the diagonal equation for e times e, together
with its etale finite-type domain. Source: chart proof Step 1 and node final paragraph
(blueprint: lem-pur-chart-diagonal-source-mate).
Proof: factor through U times_Y A. Each factor is a base change of e; their
composition is etale. Separatedness follows by cancellation from the separated map
h, and finite type and quasi-compactness follow from the Noetherian finite-type
field domain. The three equations follow from the pullback universal property. -/
theorem productGeometry (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :
    Etale (ChartFactors.selfMap d h e w) ∧
    IsSeparated (ChartFactors.selfMap d h e w) ∧
    QuasiCompact (ChartFactors.selfMap d h e w) ∧
    ChartFactors.selfMap d h e w ≫ pullback.fst
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = pullback.fst h h ≫ e ∧
    ChartFactors.selfMap d h e w ≫ pullback.snd
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = pullback.snd h h ≫ e ∧
    pullback.diagonal h ≫ ChartFactors.selfMap d h e w =
      e ≫ pullback.diagonal (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) := by
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  let pA := pullback.fst p p
  let t := ChartFactors.sourceLift d h e w
  have ht := ChartFactors.sourceLift_geometry d h e w
  have : Etale t := ht.1
  have : IsSeparated t := ht.2.1
  have : QuasiCompact t := ht.2.2.1
  have : IsSeparated (e ≫ p) := by rw [w]; infer_instance
  have : IsSeparated e := IsSeparated.of_comp e p
  have := P.noetherian (h ≫ aY)
  have : QuasiCompact e := inferInstance
  have hm : ChartFactors.selfMap d h e w = t ≫ pullback.fst pA e := by
    simp [t, pA, p, ChartFactors.sourceLift]
  refine ⟨?_, ?_, ?_, ChartFactors.selfMap_fst d h e w, ?_, ?_⟩
  · rw [hm]
    infer_instance
  · rw [hm]
    infer_instance
  · rw [hm]
    infer_instance
  · simp [ChartFactors.selfMap]
  · apply pullback.hom_ext <;> simp [ChartFactors.selfMap]


/-- The exact closed complement removed from the self-product: the image of the
non-diagonal component of U times_A U. Source: chart proof Step 1
(blueprint: lem-pur-chart-diagonal-source-mate). -/
def neighbourhoodCarrier {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) : Set ↥(pullback h h) :=
  ((pullback.map e e h h (𝟙 U) (𝟙 U)
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
      (w.trans (Category.id_comp h).symm)
      (w.trans (Category.id_comp h).symm)) ''
    (Set.range (pullback.diagonal e))ᶜ)ᶜ

/-- The target-etale unit arrow D_u = Ru!(eta_e) c_(u,e), with the same
compact-support compositor used for the exceptional comparisons.
Source: node proof Step 5, definition of D_j; finite etale normalization (3)
(blueprint: lem-pur-chart-diagonal-source-mate). -/
def targetUnit (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (O : (pullback h h).Opens) :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  let v := O.ι ≫ pullback.fst h h
  letI := P.noetherian aY
  letI := P.noetherian (h ≫ aY)
  letI := P.noetherian (p ≫ aY)
  letI : IsSeparated (e ≫ p) := by rw [w]; infer_instance
  letI : IsSeparated e := IsSeparated.of_comp e p
  letI := Dnc.compactifiable P e (p ≫ aY)
  letI := Dnc.compactifiable P v (h ≫ aY)
  letI := Dnc.compactifiable P (v ≫ e) (p ≫ aY)
  let eta := (N.adjunction e (HasCompactification.compactification e)
    (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) e)
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) e)).exists.choose
  (ProEtale.smoothExceptionalCompIso P.Coefficient v e).hom.app (𝟙_ _) ≫
    (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) v).map
      ((eta.app (𝟙_ _) ≪≫
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) e).app _).symm ≪≫
        Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) e).hom)

/-- The actual i,q construction on an open neighbourhood. In the inverse direction,
first insert section pullback coherence, then invert q locality, apply D_u, and
apply open locality. Inverting this composite gives exactly the requested a.
Source: chart proof Step 3 and node proof Step 5
(blueprint: lem-pur-chart-diagonal-source-mate). -/
def viaQ (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (O : (pullback h h).Opens) (sO : U ⟶ O.toScheme)
    (hsO : sO ≫ O.ι = pullback.diagonal h)
    (hD : IsIso (targetUnit P d h aY e w N O)) :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  let pA := pullback.fst p p
  let v := O.ι ≫ pullback.fst h h
  let q := O.ι ≫ ChartFactors.selfMap d h e w
  letI := P.noetherian aY
  letI := P.noetherian (h ≫ aY)
  letI := P.noetherian (p ≫ aY)
  letI := P.noetherian (pA ≫ p ≫ aY)
  letI := P.noetherian (pullback.fst h h ≫ h ≫ aY)
  letI := P.noetherian (v ≫ h ≫ aY)
  letI := (productGeometry P d h aY e w).1
  letI := (productGeometry P d h aY e w).2.1
  letI := (productGeometry P d h aY e w).2.2.1
  letI : IsSeparated (e ≫ p) := by rw [w]; infer_instance
  letI : IsSeparated e := IsSeparated.of_comp e p
  letI := Dnc.compactifiable P pA (p ≫ aY)
  letI := Dnc.compactifiable P v (h ≫ aY)
  letI := Dnc.compactifiable P (v ≫ e) (p ≫ aY)
  letI := Dnc.compactifiable P (q ≫ pA) (p ≫ aY)
  let wq : q ≫ pA = v ≫ e := by
    dsimp [q, pA, v]
    rw [Category.assoc, (productGeometry P d h aY e w).2.2.2.1, Category.assoc]
  let sd : sO ≫ q = e ≫ pullback.diagonal p := by
    dsimp [q]
    rw [← Category.assoc, hsO]
    exact (productGeometry P d h aY e w).2.2.2.2.2
  let E := (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) q).app _ ≪≫
    (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N q pA).app (𝟙_ _) ≪≫
    (conjugateIsoEquiv
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) (q ≫ pA))
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient) (v ≫ e))
      (Etale.unboundedEtaleLowerShriekCongr P.Coefficient wq.symm)).app (𝟙_ _)
  letI := hD
  let D := asIso (targetUnit P d h aY e w N O)
  let Q := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      e (pullback.diagonal p)).symm.app _ ≪≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      sO q (e ≫ pullback.diagonal p) sd.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) sO).leftDerivedFunctor.mapIso
      (E ≪≫ D) ≪≫
    (P.chartSectionEtaleRestriction N O.ι (pullback.fst h h) v rfl
      (pullback.diagonal h) sO hsO).symm
  Q.symm

/-- Alpha in the actual pro-etale section coordinates, through the canonical
section-origin presentation, with the identical inverse-beta normalization.
Source: lem-pur-diagonal-base-change, final chain; chart proof Step 3
(blueprint: lem-pur-chart-diagonal-source-mate). -/
def alphaProEtale (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := Dnc.compactifiable P h aY
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aY) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso (alpha P d h aY)

/-- The actual finite constructible c_e, transported from the specified etale
adjunction locality and followed by canonical comparison of the two pullbacks.
Source: chart proof Step 3, first paragraph
(blueprint: lem-pur-chart-diagonal-source-mate). -/
def targetProEtale (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  letI := Dnc.compactifiable P h aY
  letI := Dnc.compactifiable P p aY
  (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (target P d h aY e w N) ≪≫
    (Dnc.pullComparison P e
      (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p)).symm

/-- The mate square and its invariance under all further open restrictions. These are
maps in the canonical etale-origin coordinates for the finite constructible category.
The exact carrier specifies O by removing the off-diagonal component. Subsequent
restriction is quantified over precisely the smaller opens still containing the section.
Source: chart proof Steps 1 and 3, node displayed equality and final paragraph
(blueprint: lem-pur-chart-diagonal-source-mate). -/
def IsCompatible (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) : Prop :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  letI : SmoothOfRelativeDimension d p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  letI := Dnc.compactifiable P h aY
  letI := Dnc.compactifiable P p aY
  ∀ N : Etale.EtaleCompactSupportNormalization P.Coefficient,
    (ChartFactors.source P d h aY e w N).hom ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.map
          (alphaProEtale P d p aY).hom =
      (alphaProEtale P d h aY).hom ≫ (targetProEtale P d h aY e w N).hom ∧
    ∃ O : (pullback h h).Opens,
      (O : Set ↥(pullback h h)) = neighbourhoodCarrier d h e w ∧
      ∃ (sO : U ⟶ O.toScheme) (hsO : sO ≫ O.ι = pullback.diagonal h),
        ∃ hD : IsIso (targetUnit P d h aY e w N O),
          viaQ P d h aY e w N O sO hsO hD = ChartFactors.sourceOrdinary P d h aY e w N ∧
          ∀ (V : (pullback h h).Opens) (_hV : V ≤ O) (sV : U ⟶ V.toScheme)
            (hsV : sV ≫ V.ι = pullback.diagonal h),
            ∃ hDV : IsIso (targetUnit P d h aY e w N V),
              viaQ P d h aY e w N V sV hsV hDV = viaQ P d h aY e w N O sO hsO hD


/-- The specified diagonal source maps commute with etale coordinate locality.
Source: current blueprint chart proof, Step 3 first paragraph, with Step 1's domains
(blueprint: lem-pur-chart-diagonal-source-mate).

Proof:
1. lem-pur-chart-cartesian-domain gives O and the Cartesian square of centres.
   The products U times_Y A identify the two projection equations; the intermediate
   maps t and b are etale base changes of e. Smooth permanence and finite type over
   the field give smoothness and Noetherianity; Nagata supplies compactifications.
2. Work with the ordinary finite etale origins. lem-amb-etale-adjoint-locality fixes
   E by its composite counit. prop-asd-smooth-base-change makes each beta invertible.
   lem-pur-finite-site-counit-projection-transport preserves these actual transposes
   and reflects equality on bounded constructible inputs.
3. Apply lem-amb-etale-left-comparison-base-change to e,p and base change h. Its right
   mates, by lem-weil-pbc-mate-pasting, give E_t beta_hh = t*beta_ph p2*E_e.
4. Composite-base-change coherence gives beta_ph = beta_pA,e b*beta_pp. Hence for
   T = t*beta_pA,e inverse followed by E_t, one has
   T beta_hh = (e times e)*beta_pp p2*E_e. This calculation holds on the full product.
5. lem-pur-finite-etale-dualizing-normalization identifies T with etale composition
   and the target etale unit. On O it is inverse open locality, inverse target-unit
   comparison, then q locality. Associativity gives the same composite on every
   further open, which is exactly viaQ and its equality with sourceOrdinary.
6. Pull the equation of Step 4 along the diagonal. By lem-pur-diagonal-base-change,
   alpha is the inverse beta pulled to the section. The second projection restricts
   to identity, and (e times e) Delta_U = Delta_A e. Pullback composition cancels
   the section constraints. Multiplying by the inverse diagonal beta factors gives
   a followed by e*alpha_p = alpha_h followed by c_e. Canonical site comparison
   carries the identical equation to the specified finite pro-etale morphisms.
-/
theorem chartDiagonalSourceMate (P : PurityFiniteSetting.{u}) (_hE : P.extension = ⊥)
    {U Y : Scheme.{u}} [IsAffine Y]
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :
    IsCompatible P d h aY e w := by
  sorry

end WeilConjectures.PurityFiniteSetting.ChartDiagonalSourceMate
