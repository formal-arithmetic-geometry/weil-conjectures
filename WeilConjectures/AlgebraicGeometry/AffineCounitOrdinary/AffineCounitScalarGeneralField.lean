/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteCompactCoefficients.FiniteCoefficientCompactSupportCompatibility
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import Mathlib.Algebra.CharP.Basic
public import WeilConjectures.AlgebraicGeometry.Affine.AffineCompactificationComparisonNormalization
public import WeilConjectures.AlgebraicGeometry.Affine.AffineLineCanonicalScalarCounit
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
public import WeilConjectures.AlgebraicGeometry.EtalePullbackTwistTorWindowField
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.OrderedCompactificationScalarSquareFiniteCoefficients
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Ordered affine counit under ordinary coefficient extension

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: iterated projective-line integration
(blueprint: lem-sp-affine-counit-scalar).
All coefficient arrows use the ordinary scalar left adjoint to exact restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open ProEtale.OrdinaryScalarSite

namespace AffineCounitOrdinary

/-- The ordinary scalar tensorator, transported through the unit-compatible uniqueness
of scalar left adjoints. The middle map is the K-flat derived tensor comparison.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def tensorIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (M L : DerivedCategoryModule A T) :
    (scalar T.smallEtaleTopology φ).obj (M ⊗ L) ≅
      (scalar T.smallEtaleTopology φ).obj M ⊗ (scalar T.smallEtaleTopology φ).obj L :=
  (ExceptionalCoefficients.tensorIso φ T).app (M, L)

/-- Inverse-image balancing for the ordinary scalar functor, with the existing exact
inverse-image identifications at both ends.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def pullbackIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFinitePullback A f ⋙ scalar X.smallEtaleTopology φ ≅
      scalar Y.smallEtaleTopology φ ⋙ ordinaryFinitePullback B f :=
  (scalarPullbackIso φ f).symm

/-- Scalar balancing on the concrete root line. Adjoint uniqueness for the two
sheafified Z/N extension functors fixes the map on every scalar/root tensor.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def tateSheafIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (CoefficientScalarRepresentatives.ordinaryExtension T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N A hA) ≅ Scheme.finiteEtaleTateLine T N B hB := by
  let J := T.smallEtaleTopology
  let rA := Scheme.finiteEtaleTwistScalar N A hA
  let rB := Scheme.finiteEtaleTwistScalar N B hB
  have hr : rB = φ.comp rA := Subsingleton.elim _ _
  let a := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rA).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} A))
  let b := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rB).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} B))
  let c := a.comp (CoefficientScalarRepresentatives.ordinaryAdjunction J φ)
  let r : Sheaf.restrictScalars J φ ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rA)) ≅
      sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rB) :=
    NatIso.ofComponents (fun L ↦
      Functor.isoWhiskerLeft L.obj (ModuleCat.restrictScalarsComp' rA φ rB hr).symm)
      (by intro L M f; ext W x; rfl)
  exact ((c.ofNatIsoRight r).leftAdjointUniq b).app (Scheme.finiteEtaleMuModulePresheaf T N)

/-- The derived scalar arrow on one Tate line is the transpose of its ordinary
root-normalized map, with the exact restriction/single comparison displayed.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def tateMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (scalar T.smallEtaleTopology φ).obj (ordinaryFiniteLine A N hA T) ⟶
      ordinaryFiniteLine B N hB T :=
  ProEtale.reductionEtaleTateExtensionMap φ T N hA hB

/-- Commute ordinary scalar extension with the even shift on the root line.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def shiftedLineMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (scalar T.smallEtaleTopology φ).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  letI : (scalar T.smallEtaleTopology φ).CommShift ℤ :=
    (CoefficientScalarRepresentatives.adjunction T.smallEtaleTopology φ).leftAdjointCommShift ℤ
  ((scalar T.smallEtaleTopology φ).commShiftIso (2 : ℤ)).hom.app _ ≫
    (tateMap φ T N hA hB)⟦(2 : ℤ)⟧'

/-- One projective coordinate: tensor balancing, pullback balancing, and the shifted
root-line map, in that order.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def p1Map {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (K : DerivedCategoryModule A S) :
    (scalar (ProjectiveLine S).smallEtaleTopology φ).obj
        ((ordinaryFiniteP1Right A N hA S).obj K) ⟶
      (ordinaryFiniteP1Right B N hB S).obj ((scalar S.smallEtaleTopology φ).obj K) :=
  (tensorIso φ (ProjectiveLine S)
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)).hom ≫
    ((pullbackIso φ (ProjectiveLine S ↘ S)).hom.app K ⊗ₘ
      shiftedLineMap φ (ProjectiveLine S) N hA hB)

/-- Restrict the projective-coordinate scalar comparison to its standard affine chart.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def lineMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (K : DerivedCategoryModule A S) :
    (scalar (AffineSpace PUnit.{u + 1} S).smallEtaleTopology φ).obj
        ((affineTraceLineRight A N hA S).obj K) ⟶
      (affineTraceLineRight B N hB S).obj ((scalar S.smallEtaleTopology φ).obj K) :=
  (pullbackIso φ (ProjectiveLine.affineChart S)).hom.app _ ≫
    (ordinaryFinitePullback B (ProjectiveLine.affineChart S)).map (p1Map φ S N hA hB K)

/-- The canonical arrow a_(d,K), recursively on ordered coordinates; at zero it is
literally the identity. Its factors are ordinary tensor/pullback, Tate, and shift maps.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def rightMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (d : ℕ) → (K : DerivedCategoryModule A S) →
      (scalar (affineTraceTower S d).smallEtaleTopology φ).obj
          ((affineTraceRight A N hA S d).obj K) ⟶
        (affineTraceRight B N hB S d).obj ((scalar S.smallEtaleTopology φ).obj K)
  | 0, _K => 𝟙 _
  | d + 1, K => lineMap φ (affineTraceTower S d) N hA hB
      ((affineTraceRight A N hA S d).obj K) ≫
      (affineTraceLineRight B N hB (affineTraceTower S d)).map (rightMap φ S N hA hB d K)

/-- The coefficient-free ordered left comparison with the specified compactification.
Its factors are the canonical proper/open composition and refinement comparisons.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def leftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    (c : Compactification (affineTraceProjection S d)) →
    affineTraceLeft A S d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Nat.rec (motive := fun n ↦ ∀ c : Compactification (affineTraceProjection S n),
      affineTraceLeft A S n ≅
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun c ↦
      (Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).symm ≪≫
        rightDerivedLowerShriekOfCompactificationIso A
          (Compactification.ofIsProper (𝟙 S)) c)
    (fun n ih c ↦
      let cp := HasCompactification.compactification (affineTraceProjection S n)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
          (rightDerivedLowerShriekOfCompactificationIso A
            (affineTraceLineCompactification (affineTraceTower S n)) ce.restrict) _ ≪≫
        Functor.isoWhiskerLeft _ (ih cp) ≪≫
        rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
        rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c) d


/-- Transport the actual ordered counit along the coefficient-free left comparison.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts (blueprint: lem-sp-affine-counit-scalar). -/
def counit (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (c : Compactification (affineTraceProjection S d)) (K : DerivedCategoryModule A S) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      ((affineTraceRight A N hA S d).obj K) ⟶ K :=
  (leftIso A S d c).inv.app _ ≫
    (affineTraceAdjunction A N hA (projectiveLineTraceTransport N hN A hA)
      (fun T _ hT ↦ projectiveLineTraceDatum N hN A hA T hT) S hS d).counit.app K

private theorem ordinary_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (k : Type u) [Field k]
    (S : Scheme.{u}) [IsNoetherian S] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (AffineCounitOrdinary.leftIso A S d c).hom.app M.obj =
      (orderedFiniteCompactificationComparison A k S d c M).hom := by
  exact affineCompactificationComparison_normalization A k S d c M

private theorem ordinary_tower_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    orderedFiniteAffineCoefficientMap φ S d ((affineTraceRight A N hA S d).obj K) ≫
      (affineTraceLeft B S d).map (AffineCounitOrdinary.rightMap φ S N hA hB d K) ≫
      (affineTraceAdjunction B N hB (projectiveLineTraceTransport N hN B hB)
        (fun T _ hT ↦ projectiveLineTraceDatum N hN B hB T hT) S hS d).counit.app
          ((scalar S.smallEtaleTopology φ).obj K) =
    (scalar S.smallEtaleTopology φ).map
      ((affineTraceAdjunction A N hA (projectiveLineTraceTransport N hN A hA)
        (fun T _ hT ↦ projectiveLineTraceDatum N hN A hA T hT) S hS d).counit.app K) := by
  rw [ordered_finite_exchange]
  have hr : AffineCounitOrdinary.rightMap φ S N hA hB d K =
      right_exchange
        (fun r ↦ affineTraceLineRight A N hA (affineTraceTower S r))
        (fun r ↦ affineTraceLineRight B N hB (affineTraceTower S r))
        (fun r ↦ scalar (affineTraceTower S r).smallEtaleTopology φ)
        (fun r M ↦ AffineCounitOrdinary.lineMap φ (affineTraceTower S r) N hA hB M)
        d K := by
    induction d with
    | zero => rfl
    | succ d ih => simp only [AffineCounitOrdinary.rightMap, right_exchange, ih]
  rw [hr]
  unfold affineTraceAdjunction
  apply tower_counit_scalar
  intro r
  have := affineTraceNoetherian S r
  rw [ordinary_beta_eq, ordinary_line_map_eq φ N hA hB _ (affineTraceInvertible N S hS r)]
  exact line_scalar_counit φ N hN hA hB _ (affineTraceInvertible N S hS r)
    (projectiveLineTraceTransport N hN A hA) (projectiveLineTraceTransport N hN B hB)
    (projectiveLineTraceDatum N hN A hA _ _) (projectiveLineTraceDatum N hN B hB _ _) _

private theorem ordered_finite_exchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (S : Scheme.{u}) (d : ℕ) (M : DerivedCategoryModule A (affineTraceTower S d)) :
    orderedFiniteAffineCoefficientMap φ S d M =
      (affineTraceExchangeTower
        (fun r ↦ affineTraceLineLeft A (affineTraceTower S r))
        (fun r ↦ affineTraceLineLeft B (affineTraceTower S r))
        (fun r ↦ scalar (affineTraceTower S r).smallEtaleTopology φ)
        (fun r ↦ ProEtale.FiniteCompactCoefficients.beta φ
          (affineTraceLineCompactification (affineTraceTower S r))) d).app M := by
  induction d with
  | zero =>
    simp only [orderedFiniteAffineCoefficientMap, affineTraceExchangeTower_zero]
    rfl
  | succ d ih =>
    rw [orderedFiniteAffineCoefficientMap, affineTraceExchangeTower_succ, ← ih]

private theorem ordinary_line_map_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (K : DerivedCategoryModule A S) :
    AffineCounitOrdinary.lineMap φ S N hA hB K =
      (ProEtale.reductionEtaleLineScalarIso φ S N hA hB hS K).hom := by
  simp only [AffineCounitOrdinary.lineMap, AffineCounitOrdinary.p1Map,
    AffineCounitOrdinary.tensorIso, AffineCounitOrdinary.pullbackIso,
    AffineCounitOrdinary.shiftedLineMap, AffineCounitOrdinary.tateMap,
    ProEtale.reductionEtaleLineScalarIso, ProEtale.reductionEtaleP1ScalarIso,
    ProEtale.reductionEtaleShiftedLineIso, ProEtale.reductionEtaleTateIso,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.prod_hom, Functor.uncurry_obj_map, asIso_hom, ordinaryFiniteTensor,
    MonoidalCategory.tensorHom_def]
  rfl

private theorem ordinary_beta_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ProEtale.FiniteCompactCoefficients.beta φ c = compactScalarMap φ c := by
  unfold ProEtale.FiniteCompactCoefficients.beta compactScalarMap
    ExceptionalCoefficients.compactSupportMap
  rw [ordinary_gamma_eq, ordinary_open_eq]
  rfl

private theorem ordinary_open_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    ProEtale.FiniteCompactCoefficients.etOpen φ j = ExceptionalCoefficients.openIso φ j := by
  apply Iso.ext
  ext M
  simp [ProEtale.FiniteCompactCoefficients.etOpen, ExceptionalCoefficients.openIso,
    Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit,
    Adjunction.comp_unit, Adjunction.comp_counit, scalarRestrictionPullbackIso,
    derivedOpenImmersionLowerShriekUpperStarAdjunction,
    Category.assoc, CoefficientScalarRepresentatives.adjunction,
    CoefficientScalarRepresentatives.extension]
  rfl

private theorem ordinary_gamma_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleGamma φ f = scalarMate φ f := by
  unfold etaleGamma scalarMate
  rw [← exact_geometric_adjunction A f, ← exact_geometric_adjunction B f]
  ext M
  have hp := congrArg Iso.hom (scalarPullback_eq φ f)
  simp only [ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_hom] at hp
  dsimp only [ProEtale.scalarPullbackReverseEtale,
    CoefficientScalarRepresentatives.adjunction] at hp
  simp only [etaleIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Functor.map_comp, Category.assoc,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  erw [hp]
  dsimp only [scalar, scalarExtension, CoefficientScalarRepresentatives.extension,
    ProEtale.pbcFixedScalarExtension, Functor.comp_obj, Functor.comp_map,
    TwoSquare.mk, TwoSquare.natTrans]
  simp only [Category.id_comp]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc]

private theorem exact_geometric_adjunction
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) =
      mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f := by
  have hd : derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f =
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm := by
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
        (upperStar (ModuleCat.{u + 1} A) f)).symm
  rw [hd]
  apply Adjunction.ext
  ext M
  simp [Adjunction.ofNatIsoLeft_unit, ← Functor.map_comp, Category.assoc]

private theorem compactification_counit_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L Lc : C ⥤ D} {R : D ⥤ C} {L' Lc' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R') (U : C ⥤ E) (V : D ⥤ F)
    (e : L ≅ Lc) (e' : L' ≅ Lc') (K : D)
    (b : V.obj (L.obj (R.obj K)) ⟶ L'.obj (U.obj (R.obj K)))
    (bc : V.obj (Lc.obj (R.obj K)) ⟶ Lc'.obj (U.obj (R.obj K)))
    (r : U.obj (R.obj K) ⟶ R'.obj (V.obj K))
    (sq : V.map (e.hom.app (R.obj K)) ≫ bc = b ≫ e'.hom.app (U.obj (R.obj K)))
    (hc : b ≫ L'.map r ≫ a'.counit.app (V.obj K) = V.map (a.counit.app K)) :
    bc ≫ Lc'.map r ≫ e'.inv.app (R'.obj (V.obj K)) ≫
      a'.counit.app (V.obj K) = V.map (e.inv.app (R.obj K) ≫ a.counit.app K) := by
  apply (cancel_epi (V.map (e.hom.app (R.obj K)))).mp
  simp only [Functor.map_comp]
  rw [← Category.assoc, sq]
  have hn := e'.inv.naturality r
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp] using hc

private theorem affine_right_domain (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k) (hchar : ringChar k ≠ ell)
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ)
    (hA : ((ell ^ n : ℕ) : A) = 0) (S : Scheme.{u})
    [S.Over (Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
    (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S)
    (hK : ProEtale.FiniteCompactCoefficients.Input A S K) :
    ProEtale.FiniteCompactCoefficients.Input A (affineTraceTower S d)
      ((affineTraceRight A (ell ^ n) hA S d).obj K) := by
  cases d with
  | zero => exact hK
  | succ d =>
    let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
      (S ↘ Spec (.of k))
    let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
    let : IsNoetherian S := ⟨⟩
    let X := affineTraceTower S (d + 1)
    let : X.Over (Spec (.of k)) := ⟨affineTraceProjection S (d + 1) ≫ (S ↘ Spec (.of k))⟩
    let : (affineTraceProjection S (d + 1)).IsOver (Spec (.of k)) := ⟨rfl⟩
    have : LocallyOfFiniteType (X ↘ Spec (.of k)) := by
      change LocallyOfFiniteType (affineTraceProjection S (d + 1) ≫ (S ↘ Spec (.of k)))
      infer_instance
    have : QuasiCompact (X ↘ Spec (.of k)) := by
      change QuasiCompact (affineTraceProjection S (d + 1) ≫ (S ↘ Spec (.of k)))
      infer_instance
    have : IsSeparated (X ↘ Spec (.of k)) := by
      change IsSeparated (affineTraceProjection S (d + 1) ≫ (S ↘ Spec (.of k)))
      infer_instance
    obtain ⟨a, b, hab, ht⟩ := hK.2
    obtain ⟨P, hf, hc, hz, eP⟩ :=
      (hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel A S a b hab K hK.1).1 ht
    have : IsSeparated (Over.mk (S ↘ Spec (.of k))).hom :=
      ‹IsSeparated (S ↘ Spec (.of k))›
    have : LocallyOfFiniteType (Over.mk (S ↘ Spec (.of k))).hom :=
      ‹LocallyOfFiniteType (S ↘ Spec (.of k))›
    have : QuasiCompact (Over.mk (S ↘ Spec (.of k))).hom :=
      ‹QuasiCompact (S ↘ Spec (.of k))›
    have : IsSeparated (Over.mk (X ↘ Spec (.of k))).hom :=
      ‹IsSeparated (X ↘ Spec (.of k))›
    have : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of k))).hom :=
      ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    have : QuasiCompact (Over.mk (X ↘ Spec (.of k))).hom :=
      ‹QuasiCompact (X ↘ Spec (.of k))›
    let f : Over.mk (X ↘ Spec (.of k)) ⟶ Over.mk (S ↘ Spec (.of k)) :=
      Over.homMk (affineTraceProjection S (d + 1)) (comp_over _ _)
    have h := (etale_pullback_twist_tor_window_finite_or_algClosed k hk ell Fact.out hchar
      (Over.mk (S ↘ Spec (.of k))) (Over.mk (X ↘ Spec (.of k))) f n A hA a b hab).1
      K hK.1 ht P eP (fun i ↦ (hf i).tensorRight) hc hz (d + 1)
      (2 * ((d + 1 : ℕ) : ℤ))
    let e := (orderedAffineRightIso A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA S hS (d + 1)).app K
    let L := (_root_.DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
      (Scheme.finiteEtaleTateTwist X (ell ^ n) A hA (d + 1))
    let e' : (orderedAffineRight A (ell ^ n) hA S (d + 1)).obj K ≅
        pullbackTwistDerived A (affineTraceProjection S (d + 1)) (ell ^ n) hA K
          (d + 1) (2 * ((d + 1 : ℕ) : ℤ)) :=
      (shiftFunctor _ (2 * ((d + 1 : ℕ) : ℤ))).mapIso
        ((derivedTensorRight (ModuleCat.{u + 1} A) X L).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
            (affineTraceProjection S (d + 1))).app K))
    let v := e ≪≫ e'
    have ht' := (_root_.DerivedCategory.torAmplitudeIn _
      (a - 2 * ((d + 1 : ℕ) : ℤ)) (b - 2 * ((d + 1 : ℕ) : ℤ))).prop_of_iso v.symm
        (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 h.2.2.2.2.2.2)
    refine ⟨?_, a - 2 * ((d + 1 : ℕ) : ℤ), b - 2 * ((d + 1 : ℕ) : ℤ),
      sub_le_sub_right hab _, DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 ht'⟩
    obtain ⟨hc', a', b', hab', hz'⟩ := h.2.2.2.2.2.1
    refine ⟨?_, a', b', hab', fun q hq ↦ (hz' q hq).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso v)⟩
    intro q
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (pullbackTwistDerived A (affineTraceProjection S (d + 1)) (ell ^ n) hA K
            (d + 1) (2 * ((d + 1 : ℕ) : ℤ)))) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc' q)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso v).symm)

private theorem tower_counit_scalar {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {L' : ∀ d, C' (d + 1) ⥤ C' d}
    {R : ∀ d, C d ⥤ C (d + 1)} {R' : ∀ d, C' d ⥤ C' (d + 1)}
    (a : ∀ d, L d ⊣ R d) (a' : ∀ d, L' d ⊣ R' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ⟶ (R' d).obj ((B d).obj K))
    (K : C 0)
    (h : ∀ d, (e d).app ((R d).obj ((affineTraceRightTower R d).obj K)) ≫
      (L' d).map (r d ((affineTraceRightTower R d).obj K)) ≫
        (a' d).counit.app ((B d).obj ((affineTraceRightTower R d).obj K)) =
        (B d).map ((a d).counit.app ((affineTraceRightTower R d).obj K))) (d : ℕ) :
    (affineTraceExchangeTower L L' B e d).app ((affineTraceRightTower R d).obj K) ≫
      (affineTraceLeftTower L' d).map (right_exchange R R' B r d K) ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) =
    (B 0).map ((affineTraceAdjunctionTower a d).counit.app K) := by
  induction d with
  | zero =>
    rw [affineTraceExchangeTower_zero]
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = (B 0).map (𝟙 K)
    simp
  | succ d ih =>
    let M := (affineTraceRightTower R d).obj K
    let q := right_exchange R R' B r d K
    have hn := (a' d).counit.naturality q
    simp only [Functor.comp_map, Functor.id_map] at hn
    have hi : (e d).app ((R d).obj M) ≫
        (L' d).map (r d M ≫ (R' d).map q) ≫
        (a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K)) =
        (B d).map ((a d).counit.app M) ≫ q := by
      rw [Functor.map_comp, Category.assoc, hn]
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ q) (h d)
    rw [affineTraceExchangeTower_succ, affineTraceAdjunctionTower_counit_succ,
      affineTraceAdjunctionTower_counit_succ]
    change (_ ≫ (affineTraceLeftTower L' d).map ((e d).app ((R d).obj M))) ≫
      (affineTraceLeftTower L' d).map
        ((L' d).map (r d M ≫ (R' d).map q)) ≫
      (affineTraceLeftTower L' d).map
        ((a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K))) ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) = _
    have hi' := congrArg (fun z ↦ (affineTraceLeftTower L' d).map z) hi
    simp only [Functor.map_comp, Category.assoc] at hi'
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hi']
    have he := (affineTraceExchangeTower L L' B e d).naturality ((a d).counit.app M)
    simp only [Functor.comp_map] at he
    change _ ≫ (affineTraceExchangeTower L L' B e d).app M =
      (affineTraceExchangeTower L L' B e d).app
        ((L d).obj ((affineTraceRightTower R (d + 1)).obj K)) ≫ _ at he
    rw [← Category.assoc, ← Category.assoc, ← he]
    simp only [Category.assoc]
    rw [ih, ← Functor.map_comp]

private def right_exchange {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (R : ∀ d, C d ⥤ C (d + 1)) (R' : ∀ d, C' d ⥤ C' (d + 1))
    (B : ∀ d, C d ⥤ C' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ⟶ (R' d).obj ((B d).obj K)) :
    (d : ℕ) → (K : C 0) →
      (B d).obj ((affineTraceRightTower R d).obj K) ⟶
        (affineTraceRightTower R' d).obj ((B 0).obj K)
  | 0, _ => 𝟙 _
  | d + 1, K => r d _ ≫ (R' d).map (right_exchange R R' B r d K)

private theorem base_unit (ell : ℕ) (hell : ell.Prime)
    (k : Type u) [Field k] (hchar : ringChar k ≠ ell) (n : ℕ)
    (S : Scheme.{u}) [S.Over (Spec (.of k))] :
    IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)) := by
  have h : IsUnit (ell : k) := isUnit_iff_ne_zero.2
    (CharP.cast_ne_zero_of_ne_of_prime k hell hchar)
  let f : k →+* Γ(S, ⊤) :=
    (S ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  simpa only [map_pow, map_natCast, Nat.cast_pow] using (h.pow n).map f

end AffineCounitOrdinary

/-- The ordered affine-space counit compatibility over a finite or algebraically closed field.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: iterated projective-line integration
(blueprint: lem-sp-affine-counit-scalar).

Proof (the four DAG steps):
1. Transport bounded constructibility and finite Tor amplitude through the ordered right
   normal form and the chart-domain theorem. Finite type over the field makes every
   coordinate scheme Noetherian. Since the characteristic differs from ell, the common
   annihilator ell^n is invertible, also in characteristic zero.
2. Apply the canonical single-coordinate scalar-counit identity at every right-tower input.
   Induct on the actual composite adjunction tower. Naturality of the last line counit and
   the previous coefficient arrow pastes the equations. The right exchange tower is exactly
   AffineCounitOrdinary.rightMap. At d = 0 its factors and counit are identities.
3. Apply orderedCompactification_scalar_square to the bounded-below right input. Identify
   both bounded comparison components with AffineCounitOrdinary.leftIso using the affine
   compactification normalization. This fixes the coefficient map for the chosen c.
4. Precompose the claimed equation with scalar extension of the left comparison hom.
   Substitute the square of step 3 and use naturality of the inverse B-left comparison at
   the right scalar comparison. Cancel these isomorphisms and apply step 2 and functoriality.
   This proves the actual transported compactification-counit equation, including d = 0.
-/
theorem affine_counit_scalar_general_field (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (_hchar : ringChar k ≠ ell)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (hA : ((ell ^ n : ℕ) : A) = 0)
    (hB : ((ell ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] (d : ℕ)
    (c : Compactification (affineTraceProjection S d))
    (K : DerivedCategoryModule A S)
    (_hK : ProEtale.FiniteCompactCoefficients.Input A S K) :
    ∃ (hNoeth : IsNoetherian S) (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))),
      (ProEtale.FiniteCompactCoefficients.beta φ c).app
          ((affineTraceRight A (ell ^ n) hA S d).obj K) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          (AffineCounitOrdinary.rightMap φ S (ell ^ n) hA hB d K) ≫
        @AffineCounitOrdinary.counit.{u} (ell ^ n)
          (pow_pos (Fact.out : ell.Prime).pos n) B _ _ hB S hNoeth hS d c
          ((scalar S.smallEtaleTopology φ).obj K) =
      (scalar S.smallEtaleTopology φ).map (@AffineCounitOrdinary.counit.{u} (ell ^ n)
        (pow_pos (Fact.out : ell.Prime).pos n) A _ _ hA S hNoeth hS d c K) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (S ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : IsNoetherian S := ⟨⟩
  have hS := base_unit ell Fact.out k _hchar n S
  refine ⟨inferInstance, hS, ?_⟩
  let M := (affineTraceRight A (ell ^ n) hA S d).obj K
  have hM := affine_right_domain ell k _hk _hchar A n hA S hS d K _hK
  have hplus : _root_.DerivedCategory.TStructure.t.plus M := by
    obtain ⟨hc, a, b, hab, hz⟩ := hM.1
    exact ⟨a, (DerivedCategory.isGE_iff _ a).2 (fun i hi ↦ hz i (Or.inl hi))⟩
  let P : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨M, hplus⟩
  obtain ⟨hMB, hs, _⟩ := orderedCompactification_scalar_square_finiteCoefficients
    ell k _hk _hchar φ n hA hB S d c P hM
  have hs' : (scalar S.smallEtaleTopology φ).map
        ((AffineCounitOrdinary.leftIso A S d c).hom.app M) ≫
      (ProEtale.FiniteCompactCoefficients.beta φ c).app M =
    orderedFiniteAffineCoefficientMap φ S d M ≫
      (AffineCounitOrdinary.leftIso B S d c).hom.app
        ((scalar (affineTraceTower S d).smallEtaleTopology φ).obj M) := by
    rw [ordinary_normalization A k S d c P,
      ordinary_normalization B k S d c
        ⟨(scalar (affineTraceTower S d).smallEtaleTopology φ).obj P.obj, hMB⟩]
    exact hs
  unfold AffineCounitOrdinary.counit
  exact compactification_counit_transport _ _ _ _
    (AffineCounitOrdinary.leftIso A S d c) (AffineCounitOrdinary.leftIso B S d c)
    K _ _ _ hs'
    (ordinary_tower_scalar φ (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
      hA hB S hS d K)

end AlgebraicGeometry.Etale
