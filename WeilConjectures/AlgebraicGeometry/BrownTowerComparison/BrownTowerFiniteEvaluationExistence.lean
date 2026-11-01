/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerFiniteEvaluation
public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.BrownTowerFiniteGeometry
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemBrownConstruction
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemEvaluationBound
import all WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProperSingletonEvaluation
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownOpenScalarTransportExistence
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownEvaluationMate
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.NumberTheory.Padics.NonunitCoefficientStages
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
/-! # Canonical finite support and Brown evaluation

Source: Zheng Constructions 4.1 and 5.15, Lemmas 5.16 and 5.22.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The direct-image comparison is fixed on sections and by its universal
right-derived unit. The inverse-image comparison is its adjunction mate.
Source: Zheng Construction 5.15; Stacks 07A4.
(blueprint: def-route-brown-canonical-finite-support). -/
structure NormalizedFiniteImage {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    (RV : Realization V.smallEtaleTopology O t n)
    (RW : Realization W.smallEtaleTopology O t n) where
  ordinaryRight : A.right n ⋙ levelRealization W.smallEtaleTopology O t n ≅
    levelRealization V.smallEtaleTopology O t n ⋙
      Etale.lowerStar (ModuleCat.{u + 1} (Ring O t n)) g
  ordinary_sections : ∀ (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
      (x : ((A.right n).obj M).val.obj U),
    (ordinaryRight.hom.app M).hom.app U x =
      ((A.rightUnderlying n).hom.app M).hom.app U x
  right : B.direct ⋙ RW.derived ≅ RV.derived ⋙
    (Etale.lowerStar (ModuleCat.{u + 1} (Ring O t n)) g).rightDerivedFunctor
  right_unit : ∀ K : CochainComplex (strictEtaleLevel V O t n) ℤ,
    RW.derived.map (B.directUnit.app K) ≫ right.hom.app (DerivedCategory.Q.obj K) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} (Ring O t n)) g).rightDerivedFunctor.map
        (RV.factors.hom.app K) =
    RW.factors.hom.app (((A.right n).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinaryRight.hom (.up ℤ)).app K) ≫
      strictEtaleBrownRightUnit O t g n
        (((levelRealization V.smallEtaleTopology O t n).mapHomologicalComplex
          (.up ℤ)).obj K)
  inverse : RW.derived ⋙
      (Etale.upperStar (ModuleCat.{u + 1} (Ring O t n)) g).mapDerivedCategory ≅
    B.inverse ⋙ RV.derived
  inverse_mate :
    (mateEquiv B.adjunction
      (Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (Ring O t n)) g).mapDerivedCategoryRightDerivedAdjunction
      (.mk _ _ _ _ inverse.hom)).natTrans = right.hom

/-- Normalized proper/open realization data. The open comparison is fixed by
its inverse mate; the proper comparison is fixed by sections and the derived unit.
Source: Steps 2--4 of the geometric transport plan, Zheng Constructions 4.1 and 5.15.
(blueprint: def-route-brown-canonical-finite-support). -/
structure CanonicalFiniteSupport (S : StrictEtaleCompactSupport O t c)
    (RX : ∀ n, Realization X.smallEtaleTopology O t n)
    (RY : ∀ n, Realization Y.smallEtaleTopology O t n) where
  middle : ∀ n, Realization c.Z.smallEtaleTopology O t n
  proper : ∀ n, NormalizedFiniteImage c.g n S.properImage
    (S.properDerived.level n) (middle n) (RY n)
  openImage : ∀ n, NormalizedFiniteImage c.i n S.openImage
    (S.openDerived.level n) (RX n) (middle n)
  openComparison : ∀ n, S.levelDerivedOpen n ⋙ (middle n).derived ≅
    (RX n).derived ⋙
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (Ring O t n))
        c.i).mapDerivedCategory
  openComparison_mate : ∀ n,
    (mateEquiv (S.levelDerivedOpenAdjunction n)
      (((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (Ring O t n))
        c.i).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (Etale.upperStar (ModuleCat.{u + 1} (Ring O t n))
            c.i).rightDerivedFunctorIsoMapDerivedCategory)
      (.mk _ _ _ _ (openComparison n).inv)).natTrans = (openImage n).inverse.inv

/-- The canonical finite support comparison is the composite of the normalized
proper direct-image square and the inverse mate for open extension. All associators
are explicit; no independent natural automorphism is chosen.
Source: geometric transport plan Steps 2--4.
(blueprint: def-route-brown-canonical-finite-support). -/
def CanonicalFiniteSupport.comparison {S : StrictEtaleCompactSupport O t c}
    {RX : ∀ n, Realization X.smallEtaleTopology O t n}
    {RY : ∀ n, Realization Y.smallEtaleTopology O t n}
    (L : CanonicalFiniteSupport S RX RY) (n : ℕ) :
    S.levelFunctor n ⋙ (RY n).derived ≅ (RX n).derived ⋙
      Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (Ring O t n)) c :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (L.proper n).right ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (L.openComparison n) _ ≪≫
    Functor.associator _ _ _

/-- Finite evaluation with the specified canonical proper/open support comparison.
This condition adds geometric normalization beyond the finite counit equation:
twisting `data.lower` and compensating in `finiteRight` does not supply `lower_eq`.
Source: geometric transport plan Steps 2--4.
(blueprint: def-route-brown-canonical-finite-support). -/
structure CanonicalFiniteEvaluation (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) where
  data : FiniteEvaluation S G
  support : CanonicalFiniteSupport S data.realizationX data.realizationY
  lower_eq : ∀ n, data.lower n = support.comparison n

private theorem realizationBound
    {W : Scheme.{u}} {P : StrictEtaleEvaluation W O t}
    (R : StrictEtaleBrownRealization O t W P) (n : ℕ)
    (K : DerivedCategory (strictEtaleLevel W O t n)) (a : ℤ) :
    K.IsGE a ↔ ((R.derived n).obj K).IsGE a := by
  let := strictEtaleLevelDerived W O t n
  let F : strictEtaleLevel W O t n ⥤
      Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (Ring O t n)) :=
    strictEtaleBrownConstant O t W n
  have : F.Additive := R.val.ordinaryAdditive n
  have : PreservesFiniteLimits F := (brownConstant_exact W (.of (Ring O t n))).1
  have : PreservesFiniteColimits F := (brownConstant_exact W (.of (Ring O t n))).2
  have : F.Faithful := brownConstant_faithful W (.of (Ring O t n))
  let e : R.derived n ≅ F.mapDerivedCategory := Localization.liftNatIso
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (DerivedCategory.Q ⋙ R.derived n) (DerivedCategory.Q ⋙ F.mapDerivedCategory)
    (R.derived n) F.mapDerivedCategory (R.factors n ≪≫ F.mapDerivedCategoryFactors.symm)
  constructor
  · intro h
    have := h
    have := F.isGE_mapDerivedCategory_obj K a
    exact DerivedCategory.TStructure.t.isGE_of_iso (e.app K).symm a
  · intro h
    have := h
    have hm := DerivedCategory.TStructure.t.isGE_of_iso (e.app K) a
    apply (DerivedCategory.isGE_iff K a).mpr
    intro i hi
    exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isGE_iff _ a).mp hm i hi)

private def towerRealization
    {W : Scheme.{u}} {P : StrictEtaleEvaluation W O t}
    (R : StrictEtaleBrownRealization O t W P) (n : ℕ) :
    Realization W.smallEtaleTopology O t n where
  derived := R.derived n
  factors := R.factors n
  equivalence := R.val.equivalence n
  bound := realizationBound R n

private def normalizedImage
    {V W : Scheme.{u}} {g : V ⟶ W} {n : ℕ}
    {A : StrictEtaleOrdinaryImage O t g}
    {B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n)}
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    {RV : StrictEtaleBrownRealization O t V PV}
    {RW : StrictEtaleBrownRealization O t W PW}
    (R : StrictEtaleBrownImageRealization O t g n A B RV RW) :
    NormalizedFiniteImage g n A B (towerRealization RV n) (towerRealization RW n) where
  ordinaryRight := R.val.ordinaryRight
  ordinary_sections := R.property.1
  right := R.val.right
  right_unit := R.property.2.1
  inverse := R.val.inverse
  inverse_mate := R.property.2.2

private def constructionFromGeometry
    (S : StrictEtaleCompactSupport O t c) (G : EtaleTowerBrownAdjunction S)
    (H : StrictEtaleBrownGeometry O t c S) : StrictEtaleBrownConstruction O t c S := by
  letI := G.leftAdditive
  letI := G.leftShift
  letI := G.rightAdditive
  letI := G.adjunction.rightAdjointCommShift ℤ
  letI : S.functor.IsTriangulated := G.leftExact
  letI : G.adjunction.CommShift ℤ := G.adjunction.commShift_of_leftAdjoint ℤ
  refine {
    componentsX := brownComponents X O t S.PX
    componentsZ := brownComponents c.Z O t S.PZ
    componentsY := brownComponents Y O t S.PY
    additive := G.leftAdditive
    shift := G.leftShift
    exact := G.leftExact
    coproducts := G.coproducts
    scalarX := G.scalarX
    scalarY := G.scalarY
    linear := G.leftLinear
    right := G.right
    adjunction := G.adjunction
    rightAdditive := G.rightAdditive
    rightShift := inferInstance
    shiftAdjunction := inferInstance
    rightExact := G.adjunction.isTriangulated_rightAdjoint
    rightLinear := G.rightLinear
    unitLinear := ?_
    counitLinear := ?_
    realizationX := H.realizationX
    realizationZ := H.realizationZ
    realizationY := H.realizationY
    properRealization := H.properRealization
    openRealization := H.openRealization
    openComparison := H.openComparison
    openComparison_mate := H.openComparison_mate
    levelComparison := H.levelComparison
    levelComparison_def := H.levelComparison_def
    openProjection := H.openProjection
    openMate := H.openMate
    properProjection := H.properProjection
    properMate := H.properMate
    projection := H.projection
    projection_def := H.projection_def
    projection_recorded_q := H.projection_recorded_q
    properInsertion := strictEtaleBrownProperInsertion O t c S
    properInsertion_conjugate := strictEtaleBrownProperInsertion_conjugate O t c S
    properInsertionMate := strictEtaleBrownProperInsertionMate O t c S H.properInsertionBelow
    properInsertionMate_def := fun _ ↦ rfl
    openInsertion := strictEtaleBrownOpenInsertion O t c S
    openInsertion_conjugate := strictEtaleBrownOpenInsertion_conjugate O t c S
    leftExtension := strictEtaleBrownLeftExtension O t c S H.properInsertionBelow
    leftExtension_def := fun _ ↦ rfl
    leftExtension_below := H.leftExtension_below }
  · intro r M
    simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
      (G.scalarX.derived r).naturality (G.adjunction.unit.app M)
  · intro r M
    simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
      ((G.scalarY.derived r).naturality (G.adjunction.counit.app M)).symm

private theorem singletonUnit
    {W : Scheme.{u}} (P : StrictEtaleEvaluation W O t) (n : ℕ)
    (K : DerivedCategory (strictEtaleLevel W O t n)) :
    (P.derivedAdj n).unit.app K =
      ((P.derivedBelow (Nat.le_refl n)) ≪≫ P.derivedUnit n).inv.app K := by
  let η := (P.derivedAdj n).unit.app K
  let M := (P.derivedExtension n).obj K
  have hh := below_transpose P (Nat.le_refl n) K M (𝟙 M)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at hh
  have ht := congrArg ((P.scalar (Nat.le_refl n)).derivedAdj.homEquiv _ _)
    (actual_transition_identity P n M)
  rw [Equiv.apply_symm_apply] at ht
  rw [ht] at hh
  rw [← Adjunction.homEquiv_naturality_left] at hh
  have hu := ((P.scalar (Nat.le_refl n)).derivedAdj.homEquiv _ _).injective hh
  have hn := (P.derivedUnit n).hom.naturality η
  dsimp only [Functor.id_map] at hn
  change (P.derivedBelow (Nat.le_refl n)).inv.app K =
    (P.scalar (Nat.le_refl n)).derived.map η ≫ (P.derivedUnit n).hom.app _ at hu
  rw [hn] at hu
  dsimp only [Functor.id_obj] at hu
  change η = (P.derivedUnit n).inv.app K ≫
    (P.derivedBelow (Nat.le_refl n)).inv.app K
  rw [hu, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem projectionRestriction
    (S : StrictEtaleCompactSupport O t c) (G : EtaleTowerBrownAdjunction S)
    (B : StrictEtaleBrownConstruction O t c S) {m n : ℕ} (h : n ≤ m) :
    (mateEquiv (S.PX.scalar h).derivedAdj (S.PY.scalar h).derivedAdj
      (.mk _ _ _ _ (B.projection h).inv)).natTrans =
      (etaleTowerBrownRestriction S G.openRestriction h).hom := by
  have hp : (mateEquiv (S.PZ.scalar h).derivedAdj (S.PY.scalar h).derivedAdj
      (.mk _ _ _ _ (B.properProjection h).inv)).natTrans =
      (S.properDerived.restrictedDirect h).hom := by
    rw [B.properMate]
    rw [iterated_mateEquiv_conjugateEquiv]
    exact congrArg Iso.hom (scalar_conjugate
      (S.PY.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
      (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
      (S.properDerived.derivedTensor h) (S.properDerived.restrictedDirect h)
      (S.properDerived.restrictedDirect_mate h))
  have hc := scalar_conjugate (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
    (S.openDerived.level m).adjunction (S.openDerived.level n).adjunction
    (S.openDerived.derivedTensor h) (S.openDerived.restrictedDirect h)
    (S.openDerived.restrictedDirect_mate h)
  have hi := scalar_inverse_mate (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
    (S.openDerived.level m).adjunction (S.openDerived.level n).adjunction
    (S.openDerived.derivedTensor h) (S.openDerived.restrictedDirect h)
    (S.openDerived.restrictedInverse h) hc (S.openDerived.restrictedInverse_mate h)
  have ho : (mateEquiv (S.PX.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
      (.mk _ _ _ _ (B.openProjection h).inv)).natTrans =
      (G.openRestriction h).hom := by
    have hh := iterated_mateEquiv_conjugateEquiv
      (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
      (S.PX.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
      (.mk _ _ _ _ (B.openProjection h).hom)
    have hb := congrArg (fun z ↦
      (mateEquiv (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
        (.mk _ _ _ _ z)).natTrans) (B.openMate h)
    have he : conjugateIsoEquiv
        ((S.levelDerivedOpenAdjunction m).comp (S.PZ.scalar h).derivedAdj)
        ((S.PX.scalar h).derivedAdj.comp (S.levelDerivedOpenAdjunction n))
        (B.openProjection h) = S.openDerived.restrictedInverse h :=
      Iso.ext (hh.symm.trans (hb.trans hi))
    apply (mateEquiv (S.levelDerivedOpenAdjunction n)
      (S.levelDerivedOpenAdjunction m)).injective
    change (mateEquiv (S.levelDerivedOpenAdjunction n)
      (S.levelDerivedOpenAdjunction m)
      (mateEquiv (S.PX.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
        (.mk _ _ _ _ (B.openProjection h).inv))).natTrans = _
    exact (iterated_mateEquiv_conjugateEquiv
      (S.PX.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
      (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
      (.mk _ _ _ _ (B.openProjection h).inv)).trans
      ((congrArg Iso.inv he).trans (G.openRestrictionMate h).symm)
  let α := TwoSquare.mk _ _ _ _ (B.openProjection h).inv
  let β := TwoSquare.mk _ _ _ _ (B.properProjection h).inv
  have he : (B.projection h).inv = (α ≫ₕ β).natTrans := by
    rw [B.projection_def]
    simp [TwoSquare.hComp, α, β]
  rw [he]
  have hh := congrArg TwoSquare.natTrans
    (mateEquiv_vcomp (S.PX.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
      (S.PY.scalar h).derivedAdj α β)
  change (mateEquiv (S.PX.scalar h).derivedAdj (S.PY.scalar h).derivedAdj
    (α ≫ₕ β)).natTrans = _
  rw [hh]
  apply NatTrans.ext
  funext K
  simp only [TwoSquare.vComp_app]
  change (S.properDerived.level m).direct.map
    ((mateEquiv (S.PX.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj α).natTrans.app K) ≫
    (mateEquiv (S.PZ.scalar h).derivedAdj (S.PY.scalar h).derivedAdj β).natTrans.app
      ((S.levelDerivedOpen n).obj K) = _
  rw [ho, hp]
  simp [etaleTowerBrownRestriction]

/-- Finite evaluation retaining the canonical support normalization.
Source: Zheng Construction 4.1, Lemmas 5.16 and 5.22; original geometric transport
plan Steps 1--9. (blueprint: lem-route-brown-tower-finite-evaluation-exists).

Proof: The uniformizer hypotheses give finite coefficient quotients at every positive
level, including level zero of the tower. Restrict along the constant-ring
sheafification unit and localize the resulting exact equivalences at X, Z and Y.
Ordinary geometric direct images agree on sections with rightUnderlying. The universal
right-derived units uniquely determine the proper and open direct-image comparisons;
their mates determine inverse image. Take the inverse mate of the open inverse-image
comparison along the two open-extension adjunctions. Paste this with the normalized
proper comparison, with the displayed associators, to define the canonical support
comparison. Transfer the ordinary finite exceptional adjunction through the realization
equivalences using precisely this composite. Its counit equation determines finiteRight
and gives finite_counit, without changing the supplied tower Brown adjunction.

Take the proper and open scalar projections as the mates of the recorded derivedTensor
maps. Their restriction mates agree with the recorded restriction squares, by mate
pasting. The singleton comparisons have these projections as their evaluations below
the singleton index and zero evaluations above it, so joint conservativity makes them
invertible. Paste the singleton comparisons to get chi; its evaluation transpose is
the inverse support-evaluation map by the triangle identities. Conjugate chi under the
singleton/Brown and finite-support/singleton adjunctions to get evaluation, with counit
normalization. Transpose this counit equation along the actual system transitions to
obtain the quotient mates and transition identity. The scalar unit, associator, and
mate-pasting identities give their identity and composition laws. This constructs
FiniteEvaluation with lower equal to the canonical composite just defined; retain its
proper/open data as support and the defining equality as lower_eq. Empty schemes and
zero quotient coefficients use the same universal maps; no noncanonical automorphism
of the support comparison is introduced. -/
theorem brownTowerFiniteEvaluation_exists
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (t : Padic.coefficientExtensionIntegers l E)
    (_ht : Ideal.span ({t} : Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E) t c)
    (G : EtaleTowerBrownAdjunction S) :
    Nonempty (CanonicalFiniteEvaluation S G) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  let : IsLocalRing O := hdvr.2.2.2.1
  let : IsDiscreteValuationRing O := hdvr.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({t} : Set O) = IsLocalRing.maximalIdeal O :=
    _ht.trans (IsLocalRing.eq_maximalIdeal (R := O) hdvr.2.2.2.2.1)
  have ht : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr hgen.symm
  obtain ⟨hfinite, _, _, _⟩ :=
    Padic.nonunit_coefficient_stages l E t ht.ne_zero ht.not_isUnit
  let : ∀ n, Finite (Ring O t n) := hfinite
  obtain ⟨H⟩ := brownTowerFiniteGeometry_exists O t hfinite c S
  let B := constructionFromGeometry S G H
  let RX (n : ℕ) := towerRealization H.realizationX n
  let RY (n : ℕ) := towerRealization H.realizationY n
  let support : CanonicalFiniteSupport S RX RY := {
    middle := fun n ↦ towerRealization H.realizationZ n
    proper := fun n ↦ normalizedImage (H.properRealization n)
    openImage := fun n ↦ normalizedImage (H.openRealization n)
    openComparison := H.openComparison
    openComparison_mate := H.openComparison_mate }
  have hleft (n : ℕ) : (S.levelFunctor n).IsLeftAdjoint := by
    have := H.realizationX.val.equivalence n
    have := H.realizationY.val.equivalence n
    have := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification (Ring O t n) c
    have : (S.levelFunctor n ⋙ H.realizationY.derived n).IsLeftAdjoint :=
      Functor.isLeftAdjoint_of_iso (H.levelComparison n).symm
    exact (Functor.isLeftAdjoint_comp_iff_left (S.levelFunctor n)
      (H.realizationY.derived n)).mp inferInstance
  let g (n : ℕ) := @Functor.rightAdjoint _ _ _ _ (S.levelFunctor n) (hleft n)
  let adjN (n : ℕ) : S.levelFunctor n ⊣ g n :=
    @Adjunction.ofIsLeftAdjoint _ _ _ _ (S.levelFunctor n) (hleft n)
  let θ (n : ℕ) := evaluationIso B G.adjunction adjN n
  let fr (n : ℕ) : g n ⋙ (RX n).derived ≅
      (RY n).derived ⋙ ordinaryFiniteRight (Ring O t n) c := by
    have : (RX n).derived.IsEquivalence := (RX n).equivalence
    have : (RY n).derived.IsEquivalence := (RY n).equivalence
    let a := (mateEquiv (adjN n) (ordinaryFiniteAdjunction (Ring O t n) c)
      (.mk _ _ _ _ (H.levelComparison n).inv)).natTrans
    letI : IsIso a := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
      (adjN n) (ordinaryFiniteAdjunction (Ring O t n) c)
      (RX n).derived (RY n).derived (H.levelComparison n).symm
    exact asIso a
  let data : FiniteEvaluation S G := by
    refine {
      finite := hfinite
      realizationX := RX
      realizationY := RY
      lower := H.levelComparison
      right := g
      adjunction := adjN
      finiteRight := fr
      finite_counit := ?_
      chi := fun n ↦ (B.leftExtension n).symm
      chi_transpose := ?_
      evaluation := θ
      counit := evaluationIso_counit B G.adjunction adjN
      projection := B.projection
      projection_mate := ?_
      mate := strictEtaleBrownQuotientMate B adjN
      mate_def := fun _ ↦ rfl
      transition := fun h Q ↦ (evaluationIso_transition B G.adjunction adjN h Q).symm
      mate_identity := coefficient_identity B adjN
      mate_composition := coefficient_composition B adjN }
    · intro n Q
      have he := mateEquiv_counit (adjN n) (ordinaryFiniteAdjunction (Ring O t n) c)
        (.mk _ _ _ _ (H.levelComparison n).inv) Q
      change (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (Ring O t n)) c).map ((fr n).hom.app Q) ≫
        (ordinaryFiniteAdjunction (Ring O t n) c).counit.app ((RY n).derived.obj Q) =
        (H.levelComparison n).inv.app ((g n).obj Q) ≫
          (RY n).derived.map ((adjN n).counit.app Q) at he
      change (H.levelComparison n).hom.app ((g n).obj Q) ≫ _ ≫ _ = _
      erw [he, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    · intro n P
      have hh := unit_mateEquiv (S.PX.derivedAdj n) (S.PY.derivedAdj n)
        (.mk _ _ _ _ (B.leftExtension n).inv) P
      change (S.levelFunctor n).map ((S.PX.derivedAdj n).unit.app P) ≫
        (mateEquiv (S.PX.derivedAdj n) (S.PY.derivedAdj n)
          (.mk _ _ _ _ (B.leftExtension n).inv)).natTrans.app
            ((S.PX.derivedExtension n).obj P) =
        (S.PY.derivedAdj n).homEquiv _ _ ((B.leftExtension n).inv.app P) at hh
      rw [(etaleBrownEvaluationMate B n).2, singletonUnit] at hh
      exact hh.symm
    · exact projectionRestriction S G B
  exact ⟨{ data := data
           support := support
           lower_eq := H.levelComparison_def }⟩
end BrownTowerComparison
end AlgebraicGeometry
