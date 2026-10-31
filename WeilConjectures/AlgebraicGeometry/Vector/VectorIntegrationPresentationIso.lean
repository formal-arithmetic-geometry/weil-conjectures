/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceIsoTraceInvariance
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix
import WeilConjectures.CategoryTheory.Etale.EtaleDegreeZeroHom
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-! # Integration under an isomorphism of bundle presentations over a fixed base -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local implicit_reducible] Scheme.Modules ordinaryFiniteDegreeZero
  ordinaryFiniteSingleFunctor vectorIntegrationCoefficient vectorIntegrationSource

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient vectorBundleIntegration
  VectorBundleZeroSection.scheme VectorBundleZeroSection.π

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1
  DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

private theorem square_inv_composite (A : Type (u + 1)) [CommRing A]
    {X Y S T : Scheme.{u}} {a : Y ⟶ X} {r : Y ⟶ T} {p : X ⟶ S} {f : T ⟶ S}
    (sq : CommSq a r p f) (m : Y ⟶ S) (hm : m = a ≫ p)
    (L : DerivedCategoryModule A S) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app L =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p m hm).inv.app L ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r f m (hm.trans sq.w)).hom.app L := by
  subst m
  rfl

private theorem coefficient_paste (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y S T : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (e : Y ⟶ X)
    (he : e ≫ p = q) (f : T ⟶ S) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (a : affineTraceTower T d ⟶ Y)
    (sa : IsPullback a (affineTraceProjection T d) q f)
    (se : IsPullback (a ≫ e) (affineTraceProjection T d) p f)
    (L : DerivedCategoryModule A S)
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a e).hom.app
        ((ordinaryFinitePullback A p).obj L) ≫
      (ordinaryFinitePullback A a).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e p q he.symm).inv.app L) ≫
      (vectorIntegrationCartesianCoefficient A N hA t q f hT d a sa L b).hom =
    (vectorIntegrationCartesianCoefficient A N hA t p f hT d (a ≫ e) se L b).hom := by
  have hc := leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) a e p (a ≫ e) q (a ≫ q) rfl he.symm
    (by rw [Category.assoc, he]) L
  simp only [vectorIntegrationCartesianCoefficient, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom]
  rw [square_inv_composite A sa.toCommSq (a ≫ q) rfl L,
    square_inv_composite A se.toCommSq (a ≫ q) (by rw [Category.assoc, he]) L]
  dsimp only [ordinaryFinitePullback] at hc ⊢
  rw [reassoc_of% hc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem exchange_paste_named
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {p'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] [HasCompactification p'] [HasCompactification p'']
    [QuasiCompact p'] [QuasiCompact p'']
    (sq₁ : IsPullback v' p' p v) (sq₂ : IsPullback w' p'' p' w)
    (z : X'' ⟶ X) (c : Y'' ⟶ Y) (hz : z = w' ≫ v') (hc : c = w ≫ v)
    (sq : IsPullback z p'' p c) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v c hc).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' z hz).hom.app K) := by
  subst hz hc
  exact affineLinearExchange_paste A sq₁ sq₂ K

private theorem prefix_paste (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y S T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian S] [IsNoetherian T]
    (p : X ⟶ S) (q : Y ⟶ S) (e : Y ⟶ X) (he : e ≫ p = q)
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [HasCompactification p]
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] [HasCompactification q]
    (sq : IsPullback e q p (𝟙 S))
    (f : T ⟶ S) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (a : affineTraceTower T d ⟶ Y)
    (sa : IsPullback a (affineTraceProjection T d) q f)
    (se : IsPullback (a ≫ e) (affineTraceProjection T d) p f)
    (L : DerivedCategoryModule A S)
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    (ordinaryFinitePullback A f).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app _ ≫
          (rightDerivedLowerShriekBaseChangeMap A sq).app
            ((ordinaryFinitePullback A p).obj L) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e p q he.symm).inv.app L)) ≫
      vectorIntegrationCartesianPrefix N hN A hA t q f hT d a sa L b =
    vectorIntegrationCartesianPrefix N hN A hA t p f hT d (a ≫ e) se L b := by
  let := affineTraceNoetherian T d
  let K := (ordinaryFinitePullback A p).obj L
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)
  let ce := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e p q he.symm).inv.app L
  have hn := (rightDerivedLowerShriekBaseChangeMap A sa).naturality ce
  simp only [Functor.comp_map] at hn
  have hp := exchange_paste_named A sq sa (a ≫ e) f rfl
    (Category.comp_id f).symm se K
  have hunit :
      (ordinaryFinitePullback A f).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app
            ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj K)) =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f (𝟙 S) f
          (Category.comp_id f).symm).hom.app _ := by
    apply (cancel_mono ((ordinaryFinitePullback A f).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app _))).mp
    dsimp only [ordinaryFinitePullback]
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    exact (leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) f
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj K)).symm
  have hc := coefficient_paste A N hA t p q e he f hT d a sa se L b
  unfold vectorIntegrationCartesianPrefix
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [ordinaryFinitePullback, K, ce] at hn hp hunit hc ⊢
  rw [reassoc_of% hn, reassoc_of% hp, hunit]
  simp only [Functor.id_obj, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
  rw [hc]

private theorem derived_eq_of_cover (A : Type (u + 1)) [CommRing A]
    {S : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}} (a : ∀ i, U i ⟶ S)
    [∀ i, Etale (a i)]
    (ha : ∀ x : S, ∃ (i : I) (y : U i), (a i).base y = x)
    {K : DerivedCategoryModule A S}
    {M N : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M)
    (φ ψ : K ⟶ (_root_.DerivedCategory.singleFunctor _ 0).obj N)
    (h : ∀ i, (ordinaryFinitePullback A (a i)).map φ =
      (ordinaryFinitePullback A (a i)).map ψ) : φ = ψ := by
  obtain ⟨ell, hell⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective (α.inv ≫ φ)
  obtain ⟨mu, hmu⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective (α.inv ≫ ψ)
  have he : α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell = φ := by
    rw [hell, ← Category.assoc, α.hom_inv_id, Category.id_comp]
  have hm : α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map mu = ψ := by
    rw [hmu, ← Category.assoc, α.hom_inv_id, Category.id_comp]
  have hf : JointlyFaithful (fun i ↦ upperStar (ModuleCat.{u + 1} A) (a i)) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro P Q z hz
    exact isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A) a ha z hz
  have heq : ell = mu := by
    apply hf.map_injective
    intro i
    have hh := congrArg (etaleDegreeZeroHomEquiv A (a i) α) (h i)
    rw [← he, ← hm, etaleDegreeZeroHomEquiv_map, etaleDegreeZeroHomEquiv_map] at hh
    rw [← NatIso.naturality_2 (upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} A) (a i) inferInstance) ell,
      ← NatIso.naturality_2 (upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} A) (a i) inferInstance) mu, hh]
  rw [← he, ← hm, heq]

private def restrict_frame (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    {U V : S.Opens} (h : U ≤ V) (e : VectorBundleZeroSection.Trivialization S d F V) :
    VectorBundleZeroSection.Trivialization S d F U := by
  letI : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin d)))
      (Scheme.Modules.restrictFunctor (S.homOfLE h)) :=
    (Scheme.Modules.restrictAdjunction (S.homOfLE h)).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  exact Scheme.Modules.restrictCompIso F V.ι (S.homOfLE h) U.ι (S.homOfLE_ι h) ≪≫
    (Scheme.Modules.restrictFunctor (S.homOfLE h)).mapIso e ≪≫
    (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor (S.homOfLE h))
      (ULift.{u} (Fin d)) (Scheme.Modules.restrictUnitIso (S.homOfLE h)).symm).symm

private theorem integration_normalized (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    VectorIntegrationNormalization N hN A hA S hS d F
      (vectorBundleIntegration N hN A hA S hS d F) := by
  unfold vectorBundleIntegration vectorIntegrationGluing
  exact (existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.exists.choose_spec.2

private theorem comp_transport (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : h = f ≫ g) (K : DerivedCategoryModule A Z) :
    (eqToIso (congrArg (ordinaryFinitePullback A) w)).app K ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g h w).app K := by
  subst h
  apply Iso.ext
  exact Category.id_comp _

private theorem square_transport_iso (A : Type (u + 1)) [CommRing A]
    {X Y S T : Scheme.{u}} {a : Y ⟶ X} {r : Y ⟶ T} {p : X ⟶ S} {f : T ⟶ S}
    (sq : CommSq a r p f) (L : DerivedCategoryModule A S)
    {Z : DerivedCategoryModule A Y}
    (b : (ordinaryFinitePullback A r).obj ((ordinaryFinitePullback A f).obj L) ≅ Z) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p).symm.app L ≪≫
        (eqToIso (congrArg (ordinaryFinitePullback A) sq.w)).app L ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r f).app L ≪≫ b =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm.app L ≪≫ b := by
  have h := comp_transport A r f (a ≫ p) sq.w L
  calc
    _ = (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p).symm.app L ≪≫
        (((eqToIso (congrArg (ordinaryFinitePullback A) sq.w)).app L ≪≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r f).app L) ≪≫ b) :=
      congrArg (fun z ↦
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p).symm.app L ≪≫ z)
        (Iso.trans_assoc _ _ _).symm
    _ = (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p).symm.app L ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r f (a ≫ p) sq.w).app L ≪≫ b :=
      congrArg (fun z ↦
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p).symm.app L ≪≫ z ≪≫ b) h
    _ = (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm.app L ≪≫ b :=
      (Iso.trans_assoc _ _ _).symm

private theorem chart_coefficient (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    vectorIntegrationChartCoefficient A N hA t S hS d F V e =
      vectorIntegrationCartesianCoefficient A N hA t (VectorBundleZeroSection.π S d F)
        V.ι (affineTracePullbackInvertible N V.ι hS) d
        (vectorIntegrationChart S d F V e) (vectorIntegrationChart_isPullback S d F V e)
        (affineLinearBaseCoefficient A N hA S d)
        (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) := by
  exact square_transport_iso A
    (vectorIntegrationChart_isPullback S d F V e).toCommSq
    (affineLinearBaseCoefficient A N hA S d)
    ((ordinaryFinitePullback A (affineTraceProjection V.toScheme d)).mapIso
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) ≪≫
      (affineLinearCoefficientDescent A N hA t V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d).symm)

private theorem local_trace_prefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [IsAffineHom (VectorBundleZeroSection.π S d F)]
    [LocallyOfFiniteType (VectorBundleZeroSection.π S d F)]
    (V : S.Opens) [IsNoetherian V.toScheme]
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    vectorIntegrationLocalTrace N hN A hA t D S hS d F V e =
      vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π S d F)
        V.ι (affineTracePullbackInvertible N V.ι hS) d
        (vectorIntegrationChart S d F V e) (vectorIntegrationChart_isPullback S d F V e)
        (affineLinearBaseCoefficient A N hA S d)
        (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) ≫
      affineTraceCounit A N hA t D V.toScheme (affineTracePullbackInvertible N V.ι hS) d := by
  unfold vectorIntegrationLocalTrace vectorIntegrationCartesianPrefix
  rw [chart_coefficient]
  simp only [vectorIntegrationCoefficient, Category.assoc]

/-- Integration is invariant under an arbitrary isomorphism of total spaces over one base.
Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, degree-zero descent of scalar traces;
lem-pur-vector-integration-cartesian-trace, proof step 2.
(blueprint: lem-pur-vector-integration-presentation-iso).

Proof: choose simultaneous frame opens for the two bundles. The given isomorphism,
restricted to each open and then to a geometric fibre, identifies two affine d-spaces.
The ordered affine trace sends the class of a rational point to one: in rank one this
is the projective-line degree normalization, and in rank d it is its ordered product.
An isomorphism pulls a rational point back to a rational point, with multiplicity one.
Consequently it preserves the top compact-support degree map, including the canonical
Tate coefficient comparison. Compact-support exchange identifies this fibre action with
the map displayed below. Both global compact-support sources have cohomology only in
degree zero. Exact inverse image and full faithfulness of the degree-zero embedding
reduce their trace equality to equality of module-sheaf maps, detected at all geometric
stalks. The comparison from pullback along the identity to the identity functor removes
the bottom identity edge; pullback composition supplies exactly the coefficient map.
At rank zero every fibre is a point and these are unit comparisons. The zero coefficient
ring and the empty base give the unique maps. No linearity or zero-section condition on
the isomorphism is used. This is only invariance over a fixed base, with no base-change
map between different bases and no exceptional inverse image.
-/
theorem vectorIntegration_presentationIso
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [G.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π S d F)]
    [HasCompactification (VectorBundleZeroSection.π S d G)]
    [QuasiCompact (VectorBundleZeroSection.π S d G)]
    (e : VectorBundleZeroSection.scheme S d G ≅ VectorBundleZeroSection.scheme S d F)
    (he : e.hom ≫ VectorBundleZeroSection.π S d F = VectorBundleZeroSection.π S d G)
    (sq : IsPullback e.hom (VectorBundleZeroSection.π S d G)
      (VectorBundleZeroSection.π S d F) (𝟙 S)) :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app
        (vectorIntegrationSource A N hA S d F) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app
        (vectorIntegrationCoefficient A N hA S d F) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d G)).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e.hom
          (VectorBundleZeroSection.π S d F) (VectorBundleZeroSection.π S d G)
          he.symm).inv.app (affineLinearBaseCoefficient A N hA S d)) ≫
      vectorBundleIntegration N hN A hA S hS d G =
    vectorBundleIntegration N hN A hA S hS d F := by
  classical
  let := (vectorIntegration_geometry S d F).1
  let := (vectorIntegration_geometry S d F).2.1
  let := (vectorIntegration_geometry S d F).2.2
  let := (vectorIntegration_geometry S d G).1
  let := (vectorIntegration_geometry S d G).2.1
  let := (vectorIntegration_geometry S d G).2.2
  let B : vectorIntegrationSource A N hA S d F ⟶ vectorIntegrationSource A N hA S d G :=
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app _ ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d G)).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e.hom
          (VectorBundleZeroSection.π S d F) (VectorBundleZeroSection.π S d G)
          he.symm).inv.app (affineLinearBaseCoefficient A N hA S d))
  suffices hh : B ≫ vectorBundleIntegration N hN A hA S hS d G =
      vectorBundleIntegration N hN A hA S hS d F by
    simpa only [B, vectorIntegrationSource, Functor.id_obj, Category.assoc] using hh
  obtain ⟨I, V, hV, eF⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
  obtain ⟨J, U, hU, eG⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free G (r := d)
  let O : I × J → S.Opens := fun ij ↦ V ij.1 ⊓ U ij.2
  have hO : ∀ x : S, ∃ (ij : I × J) (y : (O ij).toScheme), (O ij).ι.base y = x := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hU.ge (Set.mem_univ x) : x ∈ ⨆ j, U j)
    exact ⟨(i, j), ⟨x, hi, hj⟩, rfl⟩
  apply derived_eq_of_cover A (fun ij : I × J ↦ (O ij).ι) hO
    (vectorIntegrationGluing N hN A hA S hS d F).1
  intro ij
  let W := O ij
  let : TopologicalSpace.NoetherianSpace W.toScheme :=
    W.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian W.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let fF := restrict_frame S d F (inf_le_left : W ≤ V ij.1) (eF ij.1).some
  let fG := restrict_frame S d G (inf_le_right : W ≤ U ij.2) (eG ij.2).some
  let aF := vectorIntegrationChart S d F W fF
  let aG := vectorIntegrationChart S d G W fG
  let sF := vectorIntegrationChart_isPullback S d F W fF
  let sG := vectorIntegrationChart_isPullback S d G W fG
  have sE : IsPullback (aG ≫ e.hom) (affineTraceProjection W.toScheme d)
      (VectorBundleZeroSection.π S d F) W.ι := by
    simpa only [Category.comp_id] using sG.paste_horiz sq
  let a := sE.isoIsPullback _ _ sF
  have ha : a.hom ≫ aF = aG ≫ e.hom := IsPullback.isoIsPullback_hom_fst _ _ sE sF
  have hp : a.hom ≫ affineTraceProjection W.toScheme d =
      affineTraceProjection W.toScheme d := IsPullback.isoIsPullback_hom_snd _ _ sE sF
  have sa : IsPullback a.hom (affineTraceProjection W.toScheme d)
      (affineTraceProjection W.toScheme d) (𝟙 W.toScheme) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hp⟩
  obtain ⟨t, D, _, _⟩ := exists_affineSpaceTopTrace N hN A hA
  let L := affineLinearBaseCoefficient A N hA S d
  let b := vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS d
  let P := ordinaryFinitePullback A W.ι
  let C := affineTraceCounit A N hA t D W.toScheme
    (affineTracePullbackInvertible N W.ι hS) d
  let zF := vectorIntegrationCartesianPrefix N hN A hA t
    (VectorBundleZeroSection.π S d F) W.ι (affineTracePullbackInvertible N W.ι hS)
    d aF sF L b
  let zG := vectorIntegrationCartesianPrefix N hN A hA t
    (VectorBundleZeroSection.π S d G) W.ι (affineTracePullbackInvertible N W.ι hS)
    d aG sG L b
  have hF : P.map (vectorBundleIntegration N hN A hA S hS d F) ≫
      (ordinaryFiniteUnitPullback A W.ι).hom = zF ≫ C := by
    rw [integration_normalized N hN A hA S hS d F t D W fF,
      local_trace_prefix N hN A hA t D S hS d F W fF]
  have hG : P.map (vectorBundleIntegration N hN A hA S hS d G) ≫
      (ordinaryFiniteUnitPullback A W.ι).hom = zG ≫ C := by
    rw [integration_normalized N hN A hA S hS d G t D W fG,
      local_trace_prefix N hN A hA t D S hS d G W fG]
  have hpre : P.map B ≫ zG = zF ≫
      affineLinearTraceAction N hN A hA t W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d a.hom sa := by
    have h₁ := prefix_paste N hN A hA t _ _ e.hom he sq W.ι
      (affineTracePullbackInvertible N W.ι hS) d aG sG sE L b
    have h₂ := vectorIntegrationCartesianPrefix_action N hN A hA t
      (VectorBundleZeroSection.π S d F) W.ι (affineTracePullbackInvertible N W.ι hS)
      d aF (aG ≫ e.hom) sF sE a.hom sa ha.symm L b
    simpa only [P, B, zG, zF, L, vectorIntegrationSource, vectorIntegrationCoefficient]
      using h₁.trans h₂
  apply (cancel_mono (ordinaryFiniteUnitPullback A W.ι).hom).mp
  change P.map (B ≫ vectorBundleIntegration N hN A hA S hS d G) ≫ _ = _
  rw [P.map_comp, Category.assoc, hG, ← Category.assoc, hpre, Category.assoc,
    affineSpaceIsoTraceInvariance N hN A hA t D W.toScheme
      (affineTracePullbackInvertible N W.ι hS) d a sa, hF]

end AlgebraicGeometry.Etale
