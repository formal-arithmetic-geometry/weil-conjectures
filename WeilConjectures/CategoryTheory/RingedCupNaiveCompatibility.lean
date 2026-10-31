/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.ModulePullbackTensorIso
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.RingedPullbackTensorLocalization

/-! # Compatibility of the ringed-topos cup with the naive complex pairing

Source: Stacks Project, Cohomology on Sites, Tag 0FPK,
`lemma-cup-compatible-with-naive`, and `remark-cup-product`
(blueprint: lem-sf-ringed-cup-naive-compatibility).

The corner and model below specialize the recorded representative interface to the native
localization tensor. The adjunction is the derived adjunction of the ordinary module
adjunction, including its canonical comparison maps. The naive cup is its ordinary
cochain analogue, using the signed direct-sum total comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules.RingedCup

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})
  [HasDerivedCategory.{w} (CategoryTheory.RingedDerivedNative.Modules.{u, u, u} J R)]

/-- The recorded tensor corner, with its tensor fixed to the native derived tensor.
Source: Stacks 06YT and 0FPK (blueprint: lem-sf-ringed-cup-naive-compatibility). -/
def corner : RingedTensorCorner.{u, w} where
  site := C
  topology := J
  ring := R
  tensor := @tensor (DerivedCategory (CategoryTheory.RingedDerivedNative.Modules.{u, u, u} J R)) _
    (CategoryTheory.RingedDerivedNative.monoidal.{u, u, u, w} J R)

/-- The native localization tensorator, directed from derived tensor to ordinary total tensor.
Source: Stacks 06YT and 0FPK (blueprint: lem-sf-ringed-cup-naive-compatibility). -/
def tau (K M : CochainComplex (corner J R).mateModules ℤ) :
    (corner J R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M) ⟶
      DerivedCategory.Q.obj (K ⊗ M) :=
  letI := CategoryTheory.RingedDerivedNative.monoidal.{u, u, u, w} J R
  letI := CategoryTheory.RingedDerivedNative.lax.{u, u, u, w} J R
  Functor.LaxMonoidal.μ DerivedCategory.Q K M

/-- The native representative model, restricted to flat-term K-flat complexes.
Its components are the inverses of the canonical localization tensorators.
Source: Stacks 06YT and 0FPK (blueprint: lem-sf-ringed-cup-naive-compatibility). -/
def model : RingedTensorModel (corner J R) where
  representative := NatIso.ofComponents
    (fun P ↦ CategoryTheory.RingedDerivedNative.tensorIso.{u, u, u, w} J R P.1.obj P.2.obj
      (Or.inl ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
        (R := R) P.1.obj).2 P.1.property.1)))
    (fun f ↦ CategoryTheory.RingedDerivedNative.tensorIso_naturality.{u, u, u, w} J R
      _ _ _ _ _ _ f.1.hom f.2.hom)

private theorem tau_naturality
    {A B A' B' : CochainComplex (corner J R).mateModules ℤ}
    (f : A ⟶ A') (g : B ⟶ B') :
    (corner J R).tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
        tau J R A' B' = tau J R A B ≫ DerivedCategory.Q.map (f ⊗ₘ g) := by
  let : MonoidalCategory (DerivedCategory (corner J R).mateModules) :=
    RingedDerivedNative.monoidal.{u, u, u, w} J R
  let : (DerivedCategory.Q : CochainComplex (corner J R).mateModules ℤ ⥤ _).LaxMonoidal :=
    RingedDerivedNative.lax.{u, u, u, w} J R
  exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q f g

variable {D : Type u} [Category.{u} D] (I : GrothendieckTopology D)
  (S : Sheaf I CommRingCat.{u})
  [HasDerivedCategory.{w} (CategoryTheory.RingedDerivedNative.Modules.{u, u, u} I S)]
  (e : RingedTensorEdge (corner I S) (corner J R))

/-- Additivity of the module direct image, supplied by its ordinary adjunction.
Source: Stacks 03D7 and 0FPK (blueprint: lem-sf-ringed-cup-naive-compatibility). -/
instance pushforwardAdditive : e.pushforward.Additive :=
  letI := e.moduleAdjunction.rightAdjoint_preservesLimits
  e.pushforward.additive_of_preserves_binary_products

/-- The ordinary naive cup, constructed by the cochain adjunction.
The inverse total pullback comparison followed by the tensor of ordinary counits has
on each (p,q) summand the ordinary pullback comparison, the two counits, and the
summand inclusion. Its adjoint is therefore the summandwise naive pairing, even when
the direct image does not preserve coproducts.
Source: Stacks 0FPK (blueprint: lem-sf-ringed-cup-naive-compatibility). -/
def naive (K M : CochainComplex (corner J R).mateModules ℤ) :
    ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj K ⊗
      (e.pushforward.mapHomologicalComplex (.up ℤ)).obj M) ⟶
        (e.pushforward.mapHomologicalComplex (.up ℤ)).obj (K ⊗ M) :=
  letI := e.additive
  (e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _
    ((e.ordinaryTensor.totalIso S R e.inverseRing e.inverse e.algebraic e.ringMap
      e.pullback e.object_eq e.pushforward e.moduleAdjunction
      ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj K)
      ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj M)).inv ≫
        ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit.app K ⊗ₘ
          (e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit.app M))

private theorem pullback_naturality
    {A B : CochainComplex (corner I S).mateModules ℤ} (f : A ⟶ B) :
    e.left.map (DerivedCategory.Q.map f) ≫
      derivedPullbackComplexComparison e.pullback e.left e.epsilon B =
    derivedPullbackComplexComparison e.pullback e.left e.epsilon A ≫
      DerivedCategory.Q.map ((e.pullback.mapHomologicalComplex (.up ℤ)).map f) := by
  let t : DerivedCategory.Q ⋙ e.left ⟶
      e.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv e.left ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) e.epsilon ≫
        Functor.whiskerRight (e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
          DerivedCategory.Qh ≫
        Functor.whiskerLeft (e.pullback.mapHomologicalComplex (.up ℤ))
          (DerivedCategory.quotientCompQhIso _).hom
  exact t.naturality f

variable
  (eta : e.pushforward.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ e.right)
  [e.right.IsRightDerivedFunctor eta
    (HomotopyCategory.quasiIso (corner J R).mateModules (.up ℤ))]
  [(e.left ⋙ e.right).IsLeftDerivedFunctor
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight e.epsilon e.right)
    (HomotopyCategory.quasiIso (corner I S).mateModules (.up ℤ))]
  [(e.right ⋙ e.left).IsRightDerivedFunctor
    (Functor.whiskerRight eta e.left ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (corner J R).mateModules (.up ℤ))]

/-- The canonical derived adjunction, using the universal derived comparisons.
The two composition instances express absoluteness of the total derived functors;
K-flat and K-injective resolutions supply them. They impose no exactness on f_*.
The unnormalized adjunction field of the presentation is not used.
Source: Stacks 0FPI and 0FPK (blueprint: lem-sf-ringed-cup-naive-compatibility). -/
def adjunction : e.left ⊣ e.right :=
  letI := e.isLeftDerived
  (e.moduleAdjunction.mapHomotopyCategory (.up ℤ)).derived
    (HomotopyCategory.quasiIso (corner I S).mateModules (.up ℤ))
    (HomotopyCategory.quasiIso (corner J R).mateModules (.up ℤ)) e.epsilon eta

/-- The cup product is the adjoint of the pullback comparison and tensor of counits.
Both comparisons use the native representative model, so there is no arbitrary map.
Source: Stacks `remark-cup-product` and 0FPK
(blueprint: lem-sf-ringed-cup-naive-compatibility). -/
def cup (U V : (corner J R).mateDerived) :
    (corner I S).tensor.obj (e.right.obj U, e.right.obj V) ⟶
      e.right.obj ((corner J R).tensor.obj (U, V)) :=
  (adjunction J R I S e eta).homEquiv _ _
    ((e.tensorComparison (model I S) (model J R)).hom.app
      (e.right.obj U, e.right.obj V) ≫
      (corner J R).tensor.map (Prod.mkHom
        ((adjunction J R I S e eta).counit.app U)
        ((adjunction J R I S e eta).counit.app V)))

set_option maxHeartbeats 1000000 in
-- Transport between the localization presentations compares large sheaf functors.
private theorem counit_cochain (N : CochainComplex (corner J R).mateModules ℤ) :
    e.left.map (derivedPushforwardComplexComparison e.pushforward e.right eta N) ≫
      (adjunction J R I S e eta).counit.app (DerivedCategory.Q.obj N) =
    derivedPullbackComplexComparison e.pullback e.left e.epsilon
      ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj N) ≫
      DerivedCategory.Q.map ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit.app N) := by
  let := e.isLeftDerived
  have h := (e.moduleAdjunction.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso (corner J R).mateModules (.up ℤ)) e.epsilon eta
    ((HomotopyCategory.quotient _ (.up ℤ)).obj N)
  let F := e.pullback.mapHomotopyCategory (.up ℤ)
  let G := e.pushforward.mapHomotopyCategory (.up ℤ)
  let q := HomotopyCategory.quotient (corner J R).mateModules (.up ℤ)
  let ε := (e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit
  let f := e.pullback.mapHomotopyCategoryFactors (.up ℤ)
  let g := e.pushforward.mapHomotopyCategoryFactors (.up ℤ)
  have hε : F.map (g.inv.app N) ≫
        (e.moduleAdjunction.mapHomotopyCategory (.up ℤ)).counit.app (q.obj N) =
      f.hom.app ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj N) ≫
        q.map (ε.app N) := by
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    simp only [f, g, Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      Quotient.lift.isLift_hom]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change e.left.map (eta.app (q.obj N)) ≫
      (adjunction J R I S e eta).counit.app (DerivedCategory.Qh.obj (q.obj N)) =
    e.epsilon.app (G.obj (q.obj N)) ≫
      DerivedCategory.Qh.map
        ((e.moduleAdjunction.mapHomotopyCategory (.up ℤ)).counit.app (q.obj N)) at h
  have hc := (adjunction J R I S e eta).counit.naturality
    ((DerivedCategory.quotientCompQhIso (corner J R).mateModules).hom.app N)
  simp only [Functor.comp_map, Functor.id_map] at hc
  have hn := e.epsilon.naturality (g.inv.app N)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [derivedPushforwardComplexComparison, derivedPullbackComplexComparison,
    Functor.map_comp, Category.assoc]
  rw [hc]
  simp only [Functor.comp_obj]
  rw [reassoc_of% h, reassoc_of% hn]
  rw [← DerivedCategory.Qh.map_comp_assoc, hε, DerivedCategory.Qh.map_comp]
  simp only [Category.assoc]
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality (ε.app N)
  simp only [Functor.id_obj] at hq
  rw [hq]
  simp only [f, ε, Functor.comp_obj]

set_option maxHeartbeats 8000000 in
-- The native localization and signed total tensor structures are large.
/-- The derived cup agrees with the naive pairing on arbitrary unbounded complexes.
Source: Stacks, Cohomology on Sites, Tag 0FPK, `lemma-cup-compatible-with-naive`
(blueprint: lem-sf-ringed-cup-naive-compatibility).

Proof plan:
1. Put A=f_*K, B=f_*M and T=Tot(K tensor M). On each (p,q) summand the ordinary
   counit after pullback of the naive map is the tensor of counits after the
   ordinary pullback comparison. The two signed differential terms agree. Use
   lem-weil-pbc-ringed-topoi-module-adjunction,
   lem-weil-pbc-ringed-topoi-module-pullback-tensor and def-pc-tensor-complex-sheaves.
2. Transport Mathlib's derived counit factorization through the localization
   comparison isomorphisms (lem-sc-derived-adjunction-from-underived, Stacks 0FPI).
   The canonical counit after L(eta_N) is Q of the ordinary counit after the
   left-derived comparison, for N=K,M,T, without flatness or injectivity.
3. Transpose the clockwise path. The definition of cup and naturality of the
   canonical pullback tensor comparison give tau_R after the tensor of the
   two counits and the pullback tensor comparison. Substitute step 2 separately
   at K and M (lem-weil-pbc-ringed-projection-mate-exact).
4. Move the ordinary counits through tau_R by tensorator naturality. Apply
   lem-sf-ringed-pullback-tensor-localization (Stacks 0FPH) at A,B to obtain
   Q(tensor of ordinary counits after the ordinary comparison), followed by
   the left-derived comparison at t_S(A,B) and L(tau_S). Use
   lem-sf-ringed-derived-native-tensor and the canonical derived pullback.
5. Transpose the anticlockwise path. Step 2 at T and naturality of the
   left-derived comparison identify it with Q(ordinary counit after f^*(naive)),
   followed by the same two maps. Step 1 identifies the adjuncts. Injectivity of
   the adjunction Hom equivalence gives the equality. Nothing is inverted in
   these arbitrary-complex comparisons; only the specified pullback comparison
   is an isomorphism. No boundedness or exactness of f_* is assumed.
-/
theorem cup_naive_compatibility (K M : CochainComplex (corner J R).mateModules ℤ) :
    (corner I S).tensor.map (Prod.mkHom
      (CategoryTheory.derivedPushforwardComplexComparison e.pushforward e.right eta K)
      (CategoryTheory.derivedPushforwardComplexComparison e.pushforward e.right eta M)) ≫
        cup J R I S e eta (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) ≫
          e.right.map (tau J R K M) =
      tau I S ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj K)
        ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj M) ≫
      DerivedCategory.Q.map (naive J R I S e K M) ≫
      CategoryTheory.derivedPushforwardComplexComparison e.pushforward e.right eta (K ⊗ M) := by
  let := e.additive
  let A := (e.pushforward.mapHomologicalComplex (.up ℤ)).obj K
  let B := (e.pushforward.mapHomologicalComplex (.up ℤ)).obj M
  let F := e.pullback.mapHomologicalComplex (.up ℤ)
  let ad := adjunction J R I S e eta
  let δ := e.tensorComparison (model I S) (model J R)
  let η (N : CochainComplex (corner J R).mateModules ℤ) :=
    derivedPushforwardComplexComparison e.pushforward e.right eta N
  let κ (N : CochainComplex (corner I S).mateModules ℤ) :=
    derivedPullbackComplexComparison e.pullback e.left e.epsilon N
  let ε := (e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit
  let θ := (e.ordinaryTensor.totalIso S R e.inverseRing e.inverse e.algebraic e.ringMap
    e.pullback e.object_eq e.pushforward e.moduleAdjunction A B).inv
  have hloc := ringed_pullback_tensor_localization I J S R e A B
  change δ.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
      (corner J R).tensor.map (Prod.mkHom (κ A) (κ B)) ≫
        tau J R (F.obj A) (F.obj B) =
    e.left.map (tau I S A B) ≫ κ (A ⊗ B) ≫ DerivedCategory.Q.map θ at hloc
  have hn := δ.hom.naturality (Prod.mkHom (η K) (η M))
  change e.left.map ((corner I S).tensor.map (Prod.mkHom (η K) (η M))) ≫
      δ.hom.app (e.right.obj (DerivedCategory.Q.obj K), e.right.obj (DerivedCategory.Q.obj M)) =
    δ.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
      (corner J R).tensor.map (Prod.mkHom (e.left.map (η K)) (e.left.map (η M))) at hn
  apply (ad.homEquiv
    ((corner I S).tensor.obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B))
    (DerivedCategory.Q.obj (K ⊗ M))).symm.injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm, cup, Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← (corner J R).tensor.map_comp_assoc]
  change δ.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
      (corner J R).tensor.map (Prod.mkHom
        (e.left.map (η K) ≫ ad.counit.app (DerivedCategory.Q.obj K))
        (e.left.map (η M) ≫ ad.counit.app (DerivedCategory.Q.obj M))) ≫ tau J R K M = _
  rw [counit_cochain J R I S e eta K, counit_cochain J R I S e eta M]
  rw [counit_cochain J R I S e eta (K ⊗ M)]
  have ht : (corner J R).tensor.map
      (Prod.mkHom (κ A ≫ DerivedCategory.Q.map (ε.app K))
        (κ B ≫ DerivedCategory.Q.map (ε.app M))) =
      (corner J R).tensor.map (Prod.mkHom (κ A) (κ B)) ≫
        (corner J R).tensor.map (Prod.mkHom
          (DerivedCategory.Q.map (ε.app K)) (DerivedCategory.Q.map (ε.app M))) :=
    (corner J R).tensor.map_comp (Prod.mkHom (κ A) (κ B))
      (Prod.mkHom (DerivedCategory.Q.map (ε.app K)) (DerivedCategory.Q.map (ε.app M)))
  have hτ := tau_naturality J R (ε.app K) (ε.app M)
  simp only [Functor.id_obj, Functor.comp_obj] at hτ
  rw [ht, Category.assoc, hτ]
  rw [reassoc_of% hloc]
  rw [reassoc_of% (pullback_naturality J R I S e (naive J R I S e K M))]
  have hn0 : F.map (naive J R I S e K M) ≫ ε.app (K ⊗ M) =
      θ ≫ (ε.app K ⊗ₘ ε.app M) := by
    change ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
      (naive J R I S e K M) = _
    exact Equiv.symm_apply_apply _ _
  simp only [← Functor.map_comp, ← Category.assoc]
  rw [hn0]

end SheafOfModules.RingedCup
