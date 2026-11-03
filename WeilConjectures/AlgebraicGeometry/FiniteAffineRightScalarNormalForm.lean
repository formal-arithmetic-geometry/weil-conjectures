/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteAffineScalarChartPresentation
public import WeilConjectures.AlgebraicGeometry.FiniteAffineScalarNormalFormStep
public import WeilConjectures.AlgebraicGeometry.FiniteAffineTateScalarNormalization
public import WeilConjectures.AlgebraicGeometry.FiniteAffineSiteTransportLeft
public import WeilConjectures.AlgebraicGeometry.FiniteAffineSiteTransportRight

/-! # Ordered affine scalar exchange and its single normal form

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, retained Steps 4 and 10--11
(blueprint: lem-sp-finite-affine-right-scalar-normal-form).

The single reassociation is constructed independently of the tower exchange from
scalar shift, tensor, inverse image and ordinary root balancing. All tensor powers
retain their order. The left-Tate convention of the published chart operation is
related to the right-Tate convention of the ordered tower by its canonical symmetry.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Derived change of coefficients of the actual finite Tate power, by the ordinary
balanced map on roots. The scalar/single map is the adjunction transpose of the scalar
unit. Source: Charts, flat Tate line (blueprint: lem-sp-finite-affine-right-scalar-normal-form).
-/
def finiteAffineTateScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (d : ℕ) :
    (scalarExtension φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist T N A hA d)) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist T N B hB d) :=
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T _ ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map
      (ProEtale.chartEtaleTateScalarIso φ T N hA hB d).hom

/-- Single scalar/tensor/pullback reassociation, with the Tate factor on the right.
It uses the normalized scalar tensorator, inverse scalar/pullback comparison, ordinary
Tate balancing, then the shift. Source: Charts, displayed single reassociation
(blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineNormalScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (b : ℤ)
    (K : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj
        ((ordinaryFinitePullback A f ⋙ derivedTensorRight (ModuleCat.{u + 1} A) X
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist X N A hA d)) ⋙ shiftFunctor _ b).obj K) ⟶
      (ordinaryFinitePullback B f ⋙ derivedTensorRight (ModuleCat.{u + 1} B) X
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist X N B hB d)) ⋙ shiftFunctor _ b).obj
            ((scalarExtension φ S).obj K) :=
  (FiniteSmoothPurity.scalarShiftIso φ X b).hom.app _ ≫
    (shiftFunctor _ b).map
      ((ExceptionalCoefficients.tensorIso φ X).hom.app
          ((ordinaryFinitePullback A f).obj K,
            (_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist X N A hA d)) ≫
        derivedTensorHom (ModuleCat.{u + 1} B)
          ((scalarPullbackIso φ f).inv.app K) (finiteAffineTateScalarMap φ X N hA hB d))

/-- The single normal-form comparison, with the literal identity at zero coordinates.
Source: Charts, unit conventions (blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineOrderedScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) : (d : ℕ) → (K : DerivedCategoryModule A S) →
    (scalarExtension φ (affineTraceTower S d)).obj
        ((orderedAffineRight A N hA S d).obj K) ⟶
      (orderedAffineRight B N hB S d).obj ((scalarExtension φ S).obj K)
  | 0, K => 𝟙 ((scalarExtension φ S).obj K)
  | d + 1, K =>
      finiteAffineNormalScalarMap φ N hA hB (affineTraceProjection S (d + 1))
        (d + 1) (2 * ((d + 1 : ℕ) : ℤ)) K

/-- Exact-derived version of the scalar/pullback comparison, using the canonical
exact-to-left-derived identifications. Source: Charts, etale chart restriction
(blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineExactPullbackScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙ scalarExtension φ X ≅
      scalarExtension φ S ⋙ (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _ ≪≫
    (scalarPullbackIso φ f).symm ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)

/-- The same single reassociation in the published chart operation's left-Tate
convention. Source: Charts, restriction to e (blueprint:
lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineChartScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (b : ℤ)
    (K : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj
        ((ProEtale.AdjunctionTransfer.etaleChartOperation A N hA f d b).obj K) ⟶
      (ProEtale.AdjunctionTransfer.etaleChartOperation B N hB f d b).obj
        ((scalarExtension φ S).obj K) :=
  (FiniteSmoothPurity.scalarShiftIso φ X b).hom.app _ ≫
    (shiftFunctor _ b).map
      ((ExceptionalCoefficients.tensorIso φ X).hom.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist X N A hA d),
            (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K) ≫
        derivedTensorHom (ModuleCat.{u + 1} B) (finiteAffineTateScalarMap φ X N hA hB d)
          ((finiteAffineExactPullbackScalarIso φ f).hom.app K))

/-- Expand the identity normal form at zero into its canonical pullback, Tate-unit
and zero-shift presentation; positive dimensions already have that presentation.
Source: Charts, zero-coordinate units (blueprint:
lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineExpandOrderedIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) : (d : ℕ) →
    orderedAffineRight A N hA S d ≅
      ordinaryFinitePullback A (affineTraceProjection S d) ⋙
        derivedTensorRight (ModuleCat.{u + 1} A) (affineTraceTower S d)
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist (affineTraceTower S d) N A hA d)) ⋙
        shiftFunctor _ (2 * (d : ℤ))
  | 0 =>
      (Functor.isoWhiskerRight (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫
        Functor.isoWhiskerRight
          ((derivedTensorRightFunctor (ModuleCat.{u + 1} A) S).mapIso
            (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S) ≪≫
              derivedTensorRightUnitorNatIso (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ shiftFunctorZero _ ℤ).symm
  | _ + 1 => Iso.refl _

/-- Expand the prescribed tower normal form and restrict it to a chart. The ordered
Tate pullback is followed by the canonical symmetry converting to the chart operation's
left-Tate convention. Source: Charts, ordered normal form and chart restriction
(blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineChartNormalIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A e).obj ((affineTraceRight A N hA S d).obj K) ≅
      (ProEtale.AdjunctionTransfer.etaleChartOperation A N hA
        (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).obj K :=
  (ordinaryFinitePullback A e).mapIso
      (((orderedAffineRightIso A N hN hA S hS d).app K) ≪≫
        (finiteAffineExpandOrderedIso A N hA S d).app K) ≪≫
    (tensorEPullback (ModuleCat.{u + 1} A) N
      (fun X r ↦ Scheme.finiteEtaleTateSheaf A N X hA (r : ℤ))
      (fun f hX r ↦ (Scheme.finiteEtaleTwistPullbackData A N hN hA).c f hX
        (affineTracePullbackInvertible N f hX) r)
      e (affineTraceInvertible N S hS d) d (2 * (d : ℤ))).app
        ((ordinaryFinitePullback A (affineTraceProjection S d)).obj K) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((derivedTensorRight (ModuleCat.{u + 1} A) U
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist U N A hA d))).mapIso
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e
            (affineTraceProjection S d)).symm.app K) ≪≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) U).app
          ((ordinaryFinitePullback A (e ≫ affineTraceProjection S d)).obj K)).app
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist U N A hA d)) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} A) U).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist U N A hA d))).mapIso
              ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
                (e ≫ affineTraceProjection S d)).app K))

private theorem finiteAffineNormalScalarMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (hX : IsUnit (N : Γ(X, ⊤)))
    (d : ℕ) (b : ℤ) (K : DerivedCategoryModule A S) :
    IsIso (finiteAffineNormalScalarMap φ N hA hB f d b K) := by
  have := (finiteAffineTateScalar_normalization φ X N hN hA hB hX).2.2.1 d
  unfold finiteAffineNormalScalarMap derivedTensorHom
  infer_instance

private theorem finiteAffineOrderedScalarMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    IsIso (finiteAffineOrderedScalarMap φ N hA hB S d K) := by
  cases d with
  | zero => exact IsIso.id _
  | succ d =>
    exact finiteAffineNormalScalarMap_isIso φ N hN hA hB _
      (affineTraceInvertible N S hS (d + 1)) _ _ K

/-- The ordered coordinate exchange agrees with the independently constructed
single scalar reassociation after the specified ordered normal forms.

Source: Charts, retained Steps 4 and 10 (blueprint:
lem-sp-finite-affine-right-scalar-normal-form).
Proof: induct on d, starting with identity exchanges and normal forms. At a successor,
expand the coordinate exchange and the recursion defining orderedAffineRightIso.
Scalar/pullback composition and tensor compatibility move the old scalar exchange
through the new pullback. Balanced Tate change commutes with the ordered Tate product
and its pullback; the pure-section map is (z tensor a) tensor b mapped to
z tensor phi(a)b. Shift compatibility adds the two even shifts. The two resulting
composites are equal by tensor associativity and unit coherence, with no permutation
of Tate factors. Flatness of the Tate line makes its scalar/single map invertible.
All comparisons in the single reassociation are therefore invertible. -/
theorem finiteAffineRightScalarNormalForm
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S)
    (_hBounded : _root_.DerivedCategory.TStructure.t.bounded K)
    (_hConstructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj K))
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) a b K) :
    IsIso (finiteAffineOrderedScalarMap φ N hA hB S d K) ∧
      (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K).hom ≫
          (orderedAffineRightIso B N hN hB S hS d).hom.app ((scalarExtension φ S).obj K) =
        (scalarExtension φ (affineTraceTower S d)).map
            ((orderedAffineRightIso A N hN hA S hS d).hom.app K) ≫
          finiteAffineOrderedScalarMap φ N hA hB S d K := by
  have h : ∀ n : ℕ, ∀ L : DerivedCategoryModule A S,
      (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS n L).hom ≫
          (orderedAffineRightIso B N hN hB S hS n).hom.app ((scalarExtension φ S).obj L) =
        (scalarExtension φ (affineTraceTower S n)).map
            ((orderedAffineRightIso A N hN hA S hS n).hom.app L) ≫
          finiteAffineOrderedScalarMap φ N hA hB S n L := by
    intro n
    induction n with
    | zero =>
      intro L
      simp [ProEtale.reductionEtaleAffineScalarIso, orderedAffineRightIso,
        finiteAffineOrderedScalarMap, affineTraceTower]
    | succ n ih =>
      intro L
      have hi : (scalarExtension φ (affineTraceTower S n)).map
            ((orderedAffineRightIso A N hN hA S hS n).hom.app L) ≫
          finiteAffineOrderedScalarMap φ N hA hB S n L ≫
          (orderedAffineRightIso B N hN hB S hS n).inv.app ((scalarExtension φ S).obj L) =
          (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS n L).hom := by
        rw [← Category.assoc, ← ih L, Category.assoc, Iso.hom_inv_id_app,
          Category.comp_id]
      have hs := finiteAffineScalarNormalForm_step φ N hN hA hB S hS n L
      rw [hi] at hs
      simpa only [ProEtale.reductionEtaleAffineScalarIso, Iso.trans_hom,
        Functor.mapIso_hom, Category.assoc] using hs
  exact ⟨finiteAffineOrderedScalarMap_isIso φ N hN hA hB S hS d K, h d K⟩

private theorem scalarChart_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (P : C ⥤ E) (Q : D ⥤ F) (T : C ⥤ D) (U : E ⥤ F)
    (γ : P ⋙ U ≅ T ⋙ Q) {G N : C} {H M : D} {V : E} {W : F}
    (i : G ≅ N) (j : H ≅ M) (a : T.obj G ⟶ H) (n : T.obj N ⟶ M)
    (c : P.obj G ≅ V) (d : Q.obj H ≅ W) (r : U.obj V ⟶ W)
    (hn : a ≫ j.hom = T.map i.hom ≫ n)
    (h : γ.hom.app N ≫ Q.map n ≫ Q.map j.inv ≫ d.hom =
      U.map (P.map i.inv ≫ c.hom) ≫ r) :
    γ.hom.app G ≫ Q.map a ≫ d.hom = U.map c.hom ≫ r := by
  have hh := congrArg (fun z ↦ U.map (P.map i.hom) ≫ z) h
  have hγ := γ.hom.naturality i.hom
  dsimp only [Functor.comp_map] at hγ
  simp only [← Category.assoc] at hh
  rw [hγ] at hh
  have heq : T.map i.hom ≫ n ≫ j.inv = a := by
    rw [← Category.assoc, ← hn, Category.assoc, j.hom_inv_id, Category.comp_id]
  have hQ := congrArg Q.map heq
  simp only [Functor.map_comp] at hQ
  simp only [Category.assoc] at hh
  rw [reassoc_of% hQ] at hh
  simpa only [← U.map_comp_assoc, ← U.map_comp, ← P.map_comp_assoc,
    i.hom_inv_id, P.map_id, Category.id_comp] using hh

/-- Restricting the ordered equation to any separated etale finite-type chart gives
its single canonical reassociation. The chart normal form uses canonical unit maps
also when d=0. Source: Charts, retained Steps 10--11
(blueprint: lem-sp-finite-affine-right-scalar-normal-form).
Proof: compose the ordered equation with the inverse scalar/pullback comparison for e.
Use its composition law for e and p_d and the tensor/pullback comparison. The Tate
pullback and ordinary balancing square agree on root/coefficient sections; shift
compatibility preserves the even accumulated shift. The resulting composite is
finiteAffineChartScalarMap. The canonical symmetry only converts the published chart
notation from right Tate to left Tate, and does not permute the ordered Tate factors. -/
theorem finiteAffineRightScalarNormalForm_chart
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} [IsNoetherian U] (e : U ⟶ affineTraceTower S d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : DerivedCategoryModule A S)
    (_hBounded : _root_.DerivedCategory.TStructure.t.bounded K)
    (_hConstructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj K))
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) a b K) :
    (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e K).hom ≫
        (finiteAffineChartNormalIso B N hN hB S hS d e ((scalarExtension φ S).obj K)).hom =
      (scalarExtension φ U).map (finiteAffineChartNormalIso A N hN hA S hS d e K).hom ≫
        finiteAffineChartScalarMap φ N hA hB (e ≫ affineTraceProjection S d)
          d (2 * (d : ℤ)) K := by
  have hm := (finiteAffineRightScalarNormalForm φ N hN hA hB S hS d K
    _hBounded _hConstructible _hTor).2
  have h := scalarChart_transport
    (ordinaryFinitePullback A e) (ordinaryFinitePullback B e)
    (scalarExtension φ (affineTraceTower S d)) (scalarExtension φ U)
    (scalarPullbackIso φ e).symm
    ((orderedAffineRightIso A N hN hA S hS d).app K)
    ((orderedAffineRightIso B N hN hB S hS d).app ((scalarExtension φ S).obj K))
    (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K).hom
    (finiteAffineOrderedScalarMap φ N hA hB S d K)
    (finiteAffineChartNormalIso A N hN hA S hS d e K)
    (finiteAffineChartNormalIso B N hN hB S hS d e ((scalarExtension φ S).obj K))
    (finiteAffineChartScalarMap φ N hA hB (e ≫ affineTraceProjection S d)
      d (2 * (d : ℤ)) K) hm
    (finiteAffineScalar_chartPresentation φ N hN hA hB S hS d e K)
  simpa only [ProEtale.reductionEtaleChartScalarIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h

/-- Identify the chosen pro-etale scalar adjoint with the total left derived
extension, by the unique comparison of left adjoints to the same restriction.
Source: Charts, exact site transport (blueprint:
lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineProScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ≅
      L(ProEtale.sheafExtendScalars φ T) :=
  letI := φ.toAlgebra
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ)).leftAdjointUniq
      (ProEtale.leftDerivedSheafExtendScalarsAdjunction A B T)

/-- The canonical scalar/site comparison, with the total left derived extension
used by the chart reassociation. Source: Charts, exact site transport
(blueprint: lem-sp-finite-affine-right-scalar-normal-form). -/
def finiteAffineSiteScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        L(ProEtale.sheafExtendScalars φ T) ≅
      scalarExtension φ T ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (finiteAffineProScalarIso φ T).symm ≪≫
    ProEtale.pbcComparisonReduction T φ

private theorem shiftedComparison_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (A : C ⥤ D) (P : D ⥤ E) (R : C ⥤ F) (B : F ⥤ E)
    (S : E ⥤ E) (T : F ⥤ F) (c : A ⋙ P ≅ R ⋙ B) (β : T ⋙ B ≅ B ⋙ S)
    (K : C) :
    ((Functor.associator A P S).symm ≪≫ Functor.isoWhiskerRight c S ≪≫
      Functor.associator R B S ≪≫ Functor.isoWhiskerLeft R β.symm ≪≫
      (Functor.associator R T B).symm).hom.app K =
        S.map (c.hom.app K) ≫ β.inv.app (R.obj K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private theorem siteChartComparison_shift
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hR : (N : R) = 0) {X S : Scheme.{u}} (f : X ⟶ S)
    (d : ℕ) (b : ℤ) (K : DerivedCategoryModule R S) :
    (ProEtale.AdjunctionTransfer.chartOperationComparison R N hR f d b).hom.app K =
      (shiftFunctor _ b).map ((sitePreComparison R N hR f d).hom.app K) ≫
        (Functor.commShiftIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory b).inv.app
            ((siteEtalePreOperation R N hR f d).obj K) := by
  exact shiftedComparison_app
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) S).mapDerivedCategory
    (siteProPreOperation R N hR f d) (siteEtalePreOperation R N hR f d)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory
    (shiftFunctor _ b) (shiftFunctor _ b) (sitePreComparison R N hR f d)
    (Functor.commShiftIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory b) K

private theorem siteProOperation_map
    (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (b : ℤ)
    {K L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R))} (v : K ⟶ L) :
    (ProEtale.AdjunctionTransfer.proEtaleChartOperation R N hR f d b).map v =
      (shiftFunctor _ b).map ((siteProPreOperation R N hR f d).map v) := rfl

private theorem siteProScalar_shift
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (b : ℤ)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :
    ProEtale.chartScalarReassociationMap φ N hA hB f d b K =
      (letI := φ.toAlgebra
       letI : L(ProEtale.sheafExtendScalars φ X).CommShift ℤ :=
         (ProEtale.leftDerivedSheafExtendScalarsAdjunction A B X).leftAdjointCommShift ℤ
       (L(ProEtale.sheafExtendScalars φ X).commShiftIso b).hom.app
           ((siteProPreOperation A N hA f d).obj K) ≫
         (shiftFunctor _ b).map (siteProPreScalar φ N hA hB f d K)) := by
  dsimp only [ProEtale.chartScalarReassociationMap, siteProPreScalar]

private theorem siteEtaleScalar_shift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (b : ℤ)
    (K : DerivedCategoryModule A S) :
    finiteAffineChartScalarMap φ N hA hB f d b K =
      (FiniteSmoothPurity.scalarShiftIso φ X b).hom.app
          ((siteEtalePreOperation A N hA f d).obj K) ≫
        (shiftFunctor _ b).map (siteEtalePreScalar φ N hA hB f d K) := by
  dsimp only [finiteAffineChartScalarMap, siteEtalePreScalar, siteEtalePreOperation,
    ProEtale.AdjunctionTransfer.etaleChartOperation]

private theorem siteScalarShiftPasting
    {E₁ E₂ P₁ P₂ : Type*} [Category E₁] [Category E₂] [Category P₁] [Category P₂]
    (F : P₁ ⥤ P₂) (G : E₁ ⥤ E₂) (C : E₁ ⥤ P₁) (D : E₂ ⥤ P₂)
    (sP₁ : P₁ ⥤ P₁) (sP₂ : P₂ ⥤ P₂) (sE₁ : E₁ ⥤ E₁) (sE₂ : E₂ ⥤ E₂)
    (a : sP₁ ⋙ F ≅ F ⋙ sP₂) (ca : sE₁ ⋙ C ≅ C ⋙ sP₁)
    (cb : sE₂ ⋙ D ≅ D ⋙ sP₂) (g : sE₁ ⋙ G ≅ G ⋙ sE₂)
    (t : C ⋙ F ≅ G ⋙ D)
    {X : P₁} {Y : E₁} {Z : E₂} {W : P₂}
    (x : X ⟶ C.obj Y) (y : W ⟶ D.obj Z) (r : F.obj X ⟶ W) (s : G.obj Y ⟶ Z)
    (h₀ : r ≫ y = F.map x ≫ t.hom.app Y ≫ D.map s)
    (hshift : F.map (ca.inv.app Y) ≫ t.hom.app (sE₁.obj Y) ≫ D.map (g.hom.app Y) =
      a.hom.app (C.obj Y) ≫ sP₂.map (t.hom.app Y) ≫ cb.inv.app (G.obj Y)) :
    a.hom.app X ≫ sP₂.map r ≫ sP₂.map y ≫ cb.inv.app Z =
      F.map (sP₁.map x ≫ ca.inv.app Y) ≫ t.hom.app (sE₁.obj Y) ≫
        D.map (g.hom.app Y ≫ sE₂.map s) := by
  have ha := a.hom.naturality x
  have hb := cb.inv.naturality s
  dsimp only [Functor.comp_map] at ha hb
  calc
    _ = a.hom.app X ≫ sP₂.map (r ≫ y) ≫ cb.inv.app Z := by
      simp only [Functor.map_comp, Category.assoc]
    _ = a.hom.app X ≫ sP₂.map (F.map x ≫ t.hom.app Y ≫ D.map s) ≫
        cb.inv.app Z := by rw [h₀]
    _ = F.map (sP₁.map x) ≫ a.hom.app (C.obj Y) ≫ sP₂.map (t.hom.app Y) ≫
        cb.inv.app (G.obj Y) ≫ D.map (sE₂.map s) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% ha, hb]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hshift]

/-- Exact comparison pullback identifies the etale reassociation with the specified
pro-etale chart reassociation, through its actual scalar, tensor, inverse-image and
shift comparisons. In particular this is the map rho in the setting of the recorded
chart-scalar-reassociation node.

Source: Charts, retained Steps 4 and 11 (blueprint:
lem-sp-finite-affine-right-scalar-normal-form).
Proof: apply exact comparison inverse image to the chart equation. On flat-term
K-flat representatives scalar/site and scalar/pullback comparisons are the same
B-linear balancing map. Their tensor comparison is the signed total tensor map;
ordinary Tate balancing commutes with comparison inverse image and identifies the
same ordered root powers. The exact inverse image commutes with shifts. These
squares paste to the displayed equation with chartOperationComparison. Consequently
its pro-etale path is precisely chartScalarReassociationMap. For d=0, its Tate,
identity-pullback and shift maps are the canonical unit comparisons. -/
theorem finiteAffineRightScalarNormalForm_site
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (_hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (_hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} [IsNoetherian U] (e : U ⟶ affineTraceTower S d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : DerivedCategoryModule A S)
    (_hBounded : _root_.DerivedCategory.TStructure.t.bounded K)
    (_hConstructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj K))
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) a b K) :
    ProEtale.chartScalarReassociationMap φ N hA hB (e ≫ affineTraceProjection S d)
        d (2 * (d : ℤ))
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj K) ≫
      (ProEtale.AdjunctionTransfer.proEtaleChartOperation B N hB
        (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).map
          ((finiteAffineSiteScalarIso φ S).hom.app K) ≫
      (ProEtale.AdjunctionTransfer.chartOperationComparison B N hB
        (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).hom.app
          ((scalarExtension φ S).obj K) =
    L(ProEtale.sheafExtendScalars φ U).map
        ((ProEtale.AdjunctionTransfer.chartOperationComparison A N hA
          (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).hom.app K) ≫
      (finiteAffineSiteScalarIso φ U).hom.app
        ((ProEtale.AdjunctionTransfer.etaleChartOperation A N hA
          (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).obj K) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory.map
        (finiteAffineChartScalarMap φ N hA hB (e ≫ affineTraceProjection S d)
          d (2 * (d : ℤ)) K) := by
  let := φ.toAlgebra
  let : L(ProEtale.sheafExtendScalars φ U).CommShift ℤ :=
    (ProEtale.leftDerivedSheafExtendScalarsAdjunction A B U).leftAdjointCommShift ℤ
  have h := siteScalarShiftPasting
    L(ProEtale.sheafExtendScalars φ U) (scalarExtension φ U)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory
    (shiftFunctor _ (2 * (d : ℤ))) (shiftFunctor _ (2 * (d : ℤ)))
    (shiftFunctor _ (2 * (d : ℤ))) (shiftFunctor _ (2 * (d : ℤ)))
    (L(ProEtale.sheafExtendScalars φ U).commShiftIso (2 * (d : ℤ)))
    (Functor.commShiftIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory
      (2 * (d : ℤ)))
    (Functor.commShiftIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory
      (2 * (d : ℤ)))
    (FiniteSmoothPurity.scalarShiftIso φ U (2 * (d : ℤ)))
    (finiteAffineSiteScalarIso φ U)
    ((sitePreComparison A N hA (e ≫ affineTraceProjection S d) d).hom.app K)
    ((sitePreComparison B N hB (e ≫ affineTraceProjection S d) d).hom.app
      ((scalarExtension φ S).obj K))
    (siteProPreScalar φ N hA hB (e ≫ affineTraceProjection S d) d
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj K) ≫
      (siteProPreOperation B N hB (e ≫ affineTraceProjection S d) d).map
        ((finiteAffineSiteScalarIso φ S).hom.app K))
    (siteEtalePreScalar φ N hA hB (e ≫ affineTraceProjection S d) d K)
    (by
      simpa only [Category.assoc] using
        finiteAffineSiteTransportLeft φ N hA hB (e ≫ affineTraceProjection S d) d _hN
          (affineTracePullbackInvertible N (e ≫ affineTraceProjection S d) _hS) K)
    (finiteAffineSiteTransportRight φ U (2 * (d : ℤ))
      ((siteEtalePreOperation A N hA (e ≫ affineTraceProjection S d) d).obj K))
  set_option maxRecDepth 8192 in
    simpa only [siteProScalar_shift, siteChartComparison_shift, siteProOperation_map,
      siteEtaleScalar_shift, ProEtale.AdjunctionTransfer.etaleChartOperation,
      ProEtale.AdjunctionTransfer.proEtaleChartOperation, siteEtalePreOperation,
      siteProPreOperation, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
      Category.assoc] using h

end AlgebraicGeometry.Etale
