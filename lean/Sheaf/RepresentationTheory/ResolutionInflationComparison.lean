/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q39
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy

/-!
# Projective resolution maps compute inflation

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-base-field-cd,
sk-lem-base-field-cd-inflation.proof.md, paragraph 3, "It computes inflation";
Stacks Project, Tag 00LS, comparison homotopy construction
(blueprint: lem-sfb-resolution-inflation-comparison).

The integer ring is lifted to the common ambient universe. A representation over this
ring is precisely an abelian group with a group action. The cochain map is specified on
every equivariant homomorphism, so the assertion includes the actual precomposition map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

set_option backward.isDefEq.respectTransparency false in
private noncomputable def precomp
    {k G G' : Type u} [CommRing k] [Group G] [Group G']
    (π : G' →* G) (M : Rep k G) (K : ChainComplex (Rep k G) ℕ)
    (L : ChainComplex (Rep k G') ℕ)
    (f : L ⟶ ((Rep.resFunctor (k := k) π).mapHomologicalComplex (.down ℕ)).obj K) :
    K.linearYonedaObj k M ⟶ L.linearYonedaObj k (Rep.res π M) where
  f n := ModuleCat.ofHom
    { toFun := fun h ↦ f.f n ≫ (Rep.resFunctor π).map h
      map_add' := by
        intro a b
        rw [Functor.map_add, Preadditive.comp_add]
      map_smul' := by
        intro r a
        rw [Functor.map_smul, Linear.comp_smul]
        rfl }
  comm' i j hij := by
    ext h
    change K.X i ⟶ M at h
    change L.d j i ≫ (f.f i ≫ (Rep.resFunctor π).map h) =
      f.f j ≫ (Rep.resFunctor π).map (K.d j i ≫ h)
    have hc : f.f j ≫ (Rep.resFunctor π).map (K.d j i) = L.d j i ≫ f.f i :=
      f.comm j i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ (Rep.resFunctor π).map h) hc.symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t ↦ f.f j ≫ t) ((Rep.resFunctor π).map_comp _ _).symm)))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def barMapComponent
    {k G G' : Type u} [CommRing k] [Group G] [Group G']
    (π : G' →* G) (n : ℕ) :
    Rep.free k G' (Fin n → G') ⟶ Rep.res π (Rep.free k G (Fin n → G)) :=
  Rep.freeLift k G' _ fun x ↦ Finsupp.single (π ∘ x) (.single 1 1)

private theorem barMapComponent_single
    {k G G' : Type u} [CommRing k] [Group G] [Group G']
    (π : G' →* G) (n : ℕ) (x : Fin n → G') (g : G') (r : k) :
    (barMapComponent (k := k) π n).hom (Finsupp.single x (.single g r)) =
      Finsupp.single (π ∘ x) (.single (π g) r) := by
  simp [barMapComponent, Rep.freeLift, Representation.freeLift_single_single,
    Rep.res_obj_ρ]

set_option backward.isDefEq.respectTransparency false in
@[irreducible]
private noncomputable def barMap
    {k G G' : Type u} [CommRing k] [Group G] [Group G']
    (π : G' →* G) :
    Rep.barComplex k G' ⟶
      ((Rep.resFunctor (k := k) π).mapHomologicalComplex (.down ℕ)).obj
        (Rep.barComplex k G) where
  f n := barMapComponent π n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    change barMapComponent π (j + 1) ≫
        (Rep.resFunctor π).map ((Rep.barComplex k G).d (j + 1) j) =
      (Rep.barComplex k G').d (j + 1) j ≫ barMapComponent π j
    rw [Rep.barComplex.d_def, Rep.barComplex.d_def]
    apply Rep.free_ext
    intro x
    simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
    change (Rep.barComplex.d k G j).hom
        ((barMapComponent π (j + 1)).hom (Finsupp.single x (.single 1 1))) =
      (barMapComponent π j).hom
        ((Rep.barComplex.d k G' j).hom (Finsupp.single x (.single 1 1)))
    rw [barMapComponent_single, map_one]
    rw [Rep.barComplex.d_single, Rep.barComplex.d_single, map_add, map_sum]
    congr 1
    · exact (barMapComponent_single π j (fun i ↦ x i.succ) (x 0) 1).symm
    · apply Finset.sum_congr rfl
      intro a _
      calc
        _ = Finsupp.single (π ∘ a.contractNth (· * ·) x)
            (.single 1 ((-1 : k) ^ (a.val + 1))) := by
          rw [Fin.comp_contractNth (· * ·) (· * ·) π.map_mul]
        _ = _ := by
          have h := barMapComponent_single (k := k) π j (a.contractNth (· * ·) x) 1
            ((-1 : k) ^ (a.val + 1))
          rw [map_one] at h
          exact h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem barMap_f
    {k G G' : Type u} [CommRing k] [Group G] [Group G']
    (π : G' →* G) (n : ℕ) : (barMap (k := k) π).f n = barMapComponent π n := by
  unfold barMap
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def yonedaMap
    {k G : Type u} [CommRing k] [Group G] (M : Rep k G)
    {K L : ChainComplex (Rep k G) ℕ} (f : K ⟶ L) :
    L.linearYonedaObj k M ⟶ K.linearYonedaObj k M :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda k (Rep k G)).obj M).rightOp.mapHomologicalComplex _).map f).op

set_option backward.isDefEq.respectTransparency false in
private theorem isoExt_naturality
    {k G : Type u} [CommRing k] [Group G] (M : Rep k G)
    {X : Rep k G} (P Q : ProjectiveResolution X) (f : P.complex ⟶ Q.complex)
    (hf : f.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    (Q.isoExt n M).hom ≫ HomologicalComplex.homologyMap (yonedaMap M f) n =
      (P.isoExt n M).hom := by
  let Y := ((linearYoneda k (Rep k G)).obj M).rightOp
  let φ := (Y.mapHomologicalComplex (.down ℕ)).map f
  have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality (𝟙 X) P Q f
    (hf.trans (Category.comp_id
      (show P.complex.X 0 ⟶ X from P.π.f 0)).symm) Y n
  have hu := HomologicalComplex.homologyOp_hom_naturality (yonedaMap M f) n
  have h0 : (P.isoLeftDerivedObj Y n).inv =
      HomologicalComplex.homologyMap φ n ≫ (Q.isoLeftDerivedObj Y n).inv := by
    calc
      _ = (P.isoLeftDerivedObj Y n).inv ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = (P.isoLeftDerivedObj Y n).inv ≫ (Y.leftDerived n).map (𝟙 X) :=
        congrArg (fun t ↦ (P.isoLeftDerivedObj Y n).inv ≫ t)
          ((Y.leftDerived n).map_id X).symm
      _ = _ := h
  have h' := (congrArg Quiver.Hom.unop h0).symm
  have hu' : (HomologicalComplex.homologyUnop
        ((Y.mapHomologicalComplex (.down ℕ)).obj Q.complex) n).hom ≫
      (HomologicalComplex.homologyMap φ n).unop =
    HomologicalComplex.homologyMap (yonedaMap M f) n ≫
      (HomologicalComplex.homologyUnop
        ((Y.mapHomologicalComplex (.down ℕ)).obj P.complex) n).hom :=
    congrArg Quiver.Hom.unop hu
  have hn : (HomologicalComplex.homologyUnop
        ((Y.mapHomologicalComplex (.down ℕ)).obj Q.complex) n).inv ≫
      HomologicalComplex.homologyMap (yonedaMap M f) n =
    (HomologicalComplex.homologyMap φ n).unop ≫
      (HomologicalComplex.homologyUnop
        ((Y.mapHomologicalComplex (.down ℕ)).obj P.complex) n).inv := by
    apply (cancel_mono (HomologicalComplex.homologyUnop
      ((Y.mapHomologicalComplex (.down ℕ)).obj P.complex) n).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hu']
    exact (Iso.inv_hom_id_assoc _ _)
  change (Q.isoLeftDerivedObj Y n).inv.unop ≫
      (HomologicalComplex.homologyUnop _ n).inv ≫
        HomologicalComplex.homologyMap (yonedaMap M f) n =
    (P.isoLeftDerivedObj Y n).inv.unop ≫ (HomologicalComplex.homologyUnop _ n).inv
  rw [hn, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ _) h'

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_comparison
    {k G : Type u} [CommRing k] [Group G] (M : Rep k G)
    (P : ProjectiveResolution (Rep.trivial k G k)) (n : ℕ) :
    (groupCohomologyIso M n P).hom =
      HomologicalComplex.homologyMap (inhomogeneousCochainsIso M).hom n ≫
        HomologicalComplex.homologyMap
          (yonedaMap M (ProjectiveResolution.lift (𝟙 _) P (Rep.barResolution k G))) n := by
  have h := isoExt_naturality M P (Rep.barResolution k G)
    (ProjectiveResolution.lift (𝟙 _) P (Rep.barResolution k G))
    ((ProjectiveResolution.lift_commutes_zero (𝟙 _) P (Rep.barResolution k G)).trans
      (Category.comp_id (show P.complex.X 0 ⟶ Rep.trivial k G k from P.π.f 0))) n
  change (HomologicalComplex.homologyMap (inhomogeneousCochainsIso M).hom n ≫
      ((Rep.barResolution k G).isoExt n M).inv) ≫ (P.isoExt n M).hom = _
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem barMap_cochains
    {k G G' : Type u} [CommRing k] [Group G] [Group G']
    (π : G' →* G) (M : Rep k G) :
    (inhomogeneousCochainsIso M).hom ≫
        precomp π M (Rep.barComplex k G) (Rep.barComplex k G') (barMap (k := k) π) =
      cochainsMap π (𝟙 (Rep.res π M)) ≫ (inhomogeneousCochainsIso (Rep.res π M)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change ((Fin n → G) → M) at h
  change (barMap π).f n ≫ (Rep.resFunctor π).map
      ((Rep.freeLiftLEquiv k G (Fin n → G) M).symm h) =
    (Rep.freeLiftLEquiv k G' (Fin n → G') (Rep.res π M)).symm
      (fun x ↦ h (π ∘ x))
  rw [barMap_f (k := k) π n]
  apply Rep.free_ext
  intro x
  change ((barMapComponent π n ≫ (Rep.resFunctor π).map
      ((Rep.freeLiftLEquiv k G (Fin n → G) M).symm h)).hom)
      (Finsupp.single x (.single 1 1)) =
    ((Rep.freeLiftLEquiv k G' (Fin n → G') (Rep.res π M)).symm
      (fun x ↦ h (π ∘ x))).hom (Finsupp.single x (.single 1 1))
  change ((Rep.freeLiftLEquiv k G (Fin n → G) M).symm h).hom
    ((barMapComponent π n).hom (Finsupp.single x (.single 1 1))) = _
  erw [barMapComponent_single (k := k) π n x 1 1, map_one]
  change (Representation.freeLift M.ρ h) (Finsupp.single (π ∘ x) (.single 1 1)) =
    (Representation.freeLift (Rep.res π M).ρ (fun x ↦ h (π ∘ x)))
      (Finsupp.single x (.single 1 1))
  simp only [Representation.freeLift_single_single, map_one, Module.End.one_apply, one_smul]

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_inv_single
    {k G : Type u} [CommRing k] [Group G]
    (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom (Finsupp.single x (.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (Finsupp.single x (.single g r)) = .single g 1 ⊗ₜ[k] .single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  simp only [Rep.mkIso_inv, Representation.linearizeOfMulActionIso,
    Representation.Equiv.mk_symm, LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom,
    Action.tensorObj_V, Functor.mapIso_inv, Rep.tensor_V,
    Rep.tensor_ρ,
    MonoidalCategory.tensorIso_inv,
    Representation.linearizeTrivialIso, Rep.hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply,
    Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.mk_apply,
    LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z ↦ (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      simp only [one_mul]
      congr 1
      change (Action.diagonalSuccIsoTensorTrivial G n).inv.hom (g, x) = _
      exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x)

set_option backward.isDefEq.respectTransparency false in
private theorem bar_augmentation_single
    {k G : Type u} [CommRing k] [Group G] (x : Fin 0 → G) :
    ((Rep.barResolution k G).π.f 0).hom (Finsupp.single x (.single 1 1)) =
      (show ((ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k)).X 0 from (1 : k)) := by
  change ((Rep.diagonalSuccIsoFree k G 0).inv ≫ Rep.standardComplex.ε k G).hom _ = 1
  change (Rep.standardComplex.ε k G).hom
    ((Rep.diagonalSuccIsoFree k G 0).inv.hom (Finsupp.single x (.single 1 1))) = (1 : k)
  erw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

set_option backward.isDefEq.respectTransparency false in
private theorem barMap_augmentation
    {k G G' : Type u} [CommRing k] [Group G] [Group G'] (π : G' →* G) :
    (barMap (k := k) π).f 0 ≫ (Rep.resFunctor π).map
        ((Rep.barResolution k G).π.f 0) = (Rep.barResolution k G').π.f 0 := by
  rw [barMap_f (k := k) π 0]
  apply Rep.free_ext
  intro x
  change ((barMapComponent π 0) ≫ (Rep.resFunctor π).map
    ((Rep.barResolution k G).π.f 0)).hom _ = _
  change ((Rep.barResolution k G).π.f 0).hom
    ((barMapComponent π 0).hom (Finsupp.single x (.single 1 1))) = _
  erw [barMapComponent_single (k := k) π 0 x 1 1, map_one,
    bar_augmentation_single, bar_augmentation_single]

set_option backward.isDefEq.respectTransparency false in
private theorem precomp_homotopy
    {k G G' : Type u} [CommRing k] [Group G] [Group G']
    (π : G' →* G) (M : Rep k G) (K : ChainComplex (Rep k G) ℕ)
    (L : ChainComplex (Rep k G') ℕ)
    (a b : L ⟶ ((Rep.resFunctor (k := k) π).mapHomologicalComplex (.down ℕ)).obj K)
    (H : Homotopy a b) (n : ℕ) :
    HomologicalComplex.homologyMap (precomp π M K L a) n =
      HomologicalComplex.homologyMap (precomp π M K L b) n := by
  let Y := ((linearYoneda k (Rep k G')).obj (Rep.res π M)).rightOp
  let R := precomp π M K _ (𝟙 _)
  have h := ((Y.mapHomotopy H).unop.compLeft R).homologyMap_eq n
  exact h

-- The comparison works without surjectivity; retain the original statement.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- A quotient-equivariant chain map of projective resolutions lifting the identity
computes inflation in every nonnegative degree.

Source: blueprint main-20261015, sk-lem-base-field-cd-inflation.proof.md, paragraph 3;
Stacks Project, Tag 00LS, part (2)
(blueprint: lem-sfb-resolution-inflation-comparison).

Proof:
1. Apply `lem-sfb-bar-resolution-cochains` to both groups. It gives projective bar
resolutions B, B' and evaluation isomorphisms from their Hom complexes to the displayed
inhomogeneous cochain complexes.
2. Map the free basis of B' to that of B by applying π to the coefficients and every
entry of a tuple. Multiplicativity of π makes this map b commute with each differential;
it preserves augmentation. Evaluation identifies precomposition by b with cochain
pullback along π in every coordinate.
3. Use `lem-sfb-projective-resolution-homotopy-equivalence` separately over the two
group rings to choose augmentation-preserving homotopy inverse comparisons u : P → B,
v : B → P and u' : P' → B', v' : B' → P'. No restricted resolution is asserted projective.
4. If a - a' = d h + h d and z is a Hom cocycle, then z(a - a') = (z h)d is a
coboundary. In degree zero it is zero since h in degree -1 is zero. Thus u and v,
and likewise u' and v', induce inverse isomorphisms on Hom cohomology.
5. By `new-t4-augmented-resolution-lift-homotopy`, any two augmentation-preserving
comparisons are homotopic, so these identifications are canonical. The module categories
are abelian: kernels and cokernels carry induced actions and coimage maps isomorphically
to image. Epimorphisms are surjections, so the stated lifting property is categorical
projectivity. These are the canonical identifications `groupCohomologyIso`.
6. Compare A = (Res u) f and A' = b u' from P' to Res B. They have the same
augmentation. Restriction changes no underlying groups, kernels or images, so Res B
remains augmented exact. Apply `new-t4-augmented-resolution-lift-homotopy` to obtain a
homotopy between A and A'; only the source P' must have projective terms.
7. For a cocycle z : B_s → M, the homotopy gives
z u_s f_s - z b_s u'_s = (z h_{s-1})d, with zero difference for s = 0. Hence
f* u* = (u')* b* on cohomology. Step 2 identifies b* with inflation, and Steps 4–5
identify u* and (u')* with the canonical resolution isomorphisms. This is the displayed
square for every natural degree. The cochain map F itself is restriction followed by
precomposition; the chain-map equation for f verifies commutation with differentials. -/
theorem resolution_inflation_comparison
    {G G' : Type u} [Group G] [Group G']
    (π : G' →* G) (hπ : Function.Surjective π)
    (M : Rep.{u} (ULift.{u} ℤ) G)
    (P : ProjectiveResolution (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)))
    (P' : ProjectiveResolution (Rep.trivial (ULift.{u} ℤ) G' (ULift.{u} ℤ)))
    (f : P'.complex ⟶
      ((Rep.resFunctor (k := ULift.{u} ℤ) π).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex)
    (hf : f.f 0 ≫ (Rep.resFunctor π).map (P.π.f 0) = P'.π.f 0) :
    ∃ F : P.complex.linearYonedaObj (ULift.{u} ℤ) M ⟶
        P'.complex.linearYonedaObj (ULift.{u} ℤ) (Rep.res π M),
      (∀ (n : ℕ) (h : P.complex.X n ⟶ M),
        (F.f n) h = f.f n ≫ (Rep.resFunctor π).map h) ∧
      ∀ s : ℕ,
        (groupCohomologyIso M s P).hom ≫ HomologicalComplex.homologyMap F s =
          groupCohomology.map π (𝟙 (Rep.res π M)) s ≫
            (groupCohomologyIso (Rep.res π M) s P').hom := by
  let R := Rep.resFunctor (k := ULift.{u} ℤ) π
  let B := Rep.barResolution (ULift.{u} ℤ) G
  let B' := Rep.barResolution (ULift.{u} ℤ) G'
  let u := ProjectiveResolution.lift (𝟙 _) P B
  let u' := ProjectiveResolution.lift (𝟙 _) P' B'
  let a := f ≫ (R.mapHomologicalComplex (.down ℕ)).map u
  let a' : P'.complex ⟶ (R.mapHomologicalComplex (.down ℕ)).obj B.complex :=
    u' ≫ barMap π
  have hu : u.f 0 ≫ B.π.f 0 = P.π.f 0 := by
    simp [u, ProjectiveResolution.lift_commutes_zero]
  have hu' : u'.f 0 ≫ B'.π.f 0 = P'.π.f 0 := by
    simp [u', ProjectiveResolution.lift_commutes_zero]
  let K := (R.mapHomologicalComplex (.down ℕ)).obj B.complex
  have hz : K.d 1 0 ≫ R.map (B.π.f 0) = 0 := by
    change R.map (B.complex.d 1 0) ≫ R.map (B.π.f 0) = 0
    rw [← R.map_comp, B.complex_d_comp_π_f_zero, R.map_zero]
  have hzero : (ShortComplex.mk (K.d 1 0) (R.map (B.π.f 0)) hz).Exact :=
    B.exact₀.map R
  have hsucc (n : ℕ) :
      (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
        (K.d_comp_d _ _ _)).Exact := (B.exact_succ n).map R
  have ha : a.f 0 ≫ R.map (B.π.f 0) = a'.f 0 ≫ R.map (B.π.f 0) := by
    change (f.f 0 ≫ R.map (u.f 0)) ≫ R.map (B.π.f 0) =
      (u'.f 0 ≫ (barMap π).f 0) ≫ R.map (B.π.f 0)
    rw [Category.assoc, ← R.map_comp, hu, hf, Category.assoc,
      barMap_augmentation, hu']
  obtain ⟨H⟩ := ModuleCat.augmented_lift_homotopy P' K _ hz hzero hsucc a a' ha
  refine ⟨precomp π M _ _ f, fun _ _ ↦ rfl, ?_⟩
  intro s
  have hcomp : yonedaMap M u ≫ precomp π M _ _ f = precomp π M _ _ a := by
    ext n h
    change f.f n ≫ R.map (u.f n ≫ h) = (f.f n ≫ R.map (u.f n)) ≫ R.map h
    rw [Functor.map_comp, Category.assoc]
  have hcomp' : precomp π M B.complex B'.complex (barMap π) ≫ yonedaMap (Rep.res π M) u' =
      precomp π M B.complex P'.complex a' := by
    ext n h
    change u'.f n ≫ ((barMap π).f n ≫ R.map h) =
      (u'.f n ≫ (barMap π).f n) ≫ R.map h
    rw [Category.assoc]
  erw [canonical_comparison M P s]
  erw [Category.assoc]
  erw [← HomologicalComplex.homologyMap_comp]
  erw [hcomp]
  erw [precomp_homotopy π M _ _ a a' H s]
  erw [← hcomp']
  erw [HomologicalComplex.homologyMap_comp
    (precomp π M B.complex B'.complex (barMap π)) (yonedaMap (Rep.res π M) u') s]
  erw [← Category.assoc]
  erw [← HomologicalComplex.homologyMap_comp]
  erw [(show (inhomogeneousCochainsIso M).hom ≫
      precomp π M B.complex B'.complex (barMap π) = _ from barMap_cochains π M)]
  erw [HomologicalComplex.homologyMap_comp
    (cochainsMap π (𝟙 (Rep.res π M))) (inhomogeneousCochainsIso (Rep.res π M)).hom s]
  erw [Category.assoc]
  erw [← canonical_comparison (Rep.res π M) P' s]

end groupCohomology
