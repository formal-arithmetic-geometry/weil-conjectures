/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2, SHEAF group T2
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Data.Int.Interval
import Sheaf.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-! # Invertibility of normalized evaluation

Source: Stacks Project, More on Algebra, Tags 0A6A and 0ATK.
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-isiso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private noncomputable def pointPreimage {A : Type u} [CommRing A]
    {M N : RingSiteModules A} (f : M.val.obj point ⟶ N.val.obj point) :
    M.val ⟶ N.val where
  app X := by
    obtain rfl : X = point := Subsingleton.elim _ _
    exact f
  naturality {X Y} g := by
    obtain rfl : X = point := Subsingleton.elim _ _
    obtain rfl : Y = point := Subsingleton.elim _ _
    obtain rfl : g = 𝟙 point := Subsingleton.elim _ _
    ext x
    simp

private noncomputable def homPointEquiv {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj
      (op ⟨PUnit.unit⟩) ≃ₗ[A]
        (M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) where
  toFun f := (f.app (op (Over.mk (𝟙 _)))).hom
  invFun f :=
    { app := fun W ↦ by
        have hW : W = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
          rcases W with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
          rfl
        subst W
        exact ModuleCat.ofHom f
      naturality := by
        intro U V i
        have hU : U = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
          rcases U with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
          rfl
        subst U
        have hV : V = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
          rcases V with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
          rfl
        subst V
        have hi : i = 𝟙 _ := by
          apply Quiver.Hom.unop_inj
          ext
          apply Subsingleton.elim
        subst i
        ext x
        simp
        rfl }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro W
    have hW : W = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
      rcases W with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
      rfl
    subst W
    rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' a f := by
    ext x
    rfl

private theorem single_projection_isIso {C : Type*} [Category C] [HasZeroMorphisms C]
    {I : Type*} {M : I → C} {T : C} (π : ∀ i, T ⟶ M i)
    (hπ : IsLimit (Fan.mk T π)) (i : I) (hz : ∀ j, j ≠ i → IsZero (M j)) :
    IsIso (π i) := by
  classical
  let ι : M i ⟶ T := Fan.IsLimit.lift hπ
    (fun j ↦ if h : j = i then eqToHom (congrArg M h.symm) else 0)
  have hι (j : I) : ι ≫ π j =
      if h : j = i then eqToHom (congrArg M h.symm) else 0 := Fan.IsLimit.fac hπ _ j
  refine ⟨⟨ι, ?_, ?_⟩⟩
  · apply Fan.IsLimit.hom_ext hπ
    intro j
    change (π i ≫ ι) ≫ π j = 𝟙 _ ≫ π j
    rw [Category.assoc, hι]
    by_cases h : j = i
    · subst j
      simp
    · exact (hz j h).eq_of_tgt _ _
  · rw [hι]
    simp

set_option backward.isDefEq.respectTransparency true in
private theorem dualProjection_isIso {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    IsIso (ringHomComplexProjection P
      ((CochainComplex.singleFunctor (RingSiteModules A) 0).obj
        (SheafOfModules.unit ((sheafCompose ⊥
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A)))) n (-n)) := by
  let O := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let L := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj O
  apply single_projection_isIso (ringHomComplexProjection P L n)
    ((homComplex_projections_exists
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.1 P L n).some (-n)
  intro p hp
  let F := (SheafOfModules.homFunctor (CochainComplex.onePointRingSheaf A)).obj
    (op (P.X p))
  have : F.PreservesZeroMorphisms := by
    constructor
    intro M N
    apply SheafOfModules.hom_ext
    ext U φ : 3
    rfl
  exact F.map_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 O (p + n) (by omega))

set_option backward.isDefEq.respectTransparency true in
private noncomputable def dualTermIso {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    (perfectRingDual P).X n ≅
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) (P.X (-n))
        (SheafOfModules.unit ((sheafCompose ⊥
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) := by
  let O := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let L := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj O
  let π := ringHomComplexProjection P L n (-n)
  have hπ : IsIso π := dualProjection_isIso P n
  let eO : L.X (-n + n) ≅ O :=
    HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 O (-n + n) (by omega)
  exact (@asIso _ _ _ _ π hπ) ≪≫
    ((SheafOfModules.homFunctor (CochainComplex.onePointRingSheaf A)).obj
      (op (P.X (-n)))).mapIso eO

private theorem point_isIso {A : Type u} [CommRing A]
    {M N : RingSiteModules A} (f : M ⟶ N)
    (hf : Function.Bijective (f.val.app point)) : IsIso f := by
  let e := LinearEquiv.ofBijective (f.val.app point).hom hf
  let g : N ⟶ M := ⟨pointPreimage (ModuleCat.ofHom e.symm.toLinearMap)⟩
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    obtain rfl : U = point := Subsingleton.elim _ _
    ext x
    exact e.symm_apply_apply x
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    obtain rfl : U = point := Subsingleton.elim _ _
    ext x
    exact e.apply_symm_apply x

set_option backward.isDefEq.respectTransparency false in
private noncomputable def dualPointEquiv {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (r : ℤ) :
    ((perfectRingDual P).X r).val.obj point ≃ₗ[A]
      Module.Dual A ((P.X (-r)).val.obj point) := by
  let e := dualTermIso P r
  let e₀ : ((perfectRingDual P).X r).val.obj point ≃ₗ[A]
      (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
        (P.X (-r)) _).val.obj point :=
    LinearEquiv.ofBijective (e.hom.val.app point).hom
    (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ point).map e.hom))
  exact e₀.trans (homPointEquiv _ _)

private lemma dualPointEquiv_apply {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (r : ℤ)
    (lam : ((perfectRingDual P).X r).val.obj point) (x : (P.X (-r)).val.obj point) :
    dualPointEquiv P r lam x = perfectRingDualEvaluate P r point lam x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorPointEquiv {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    TensorProduct A (M.val.obj point) (N.val.obj point) ≃ₗ[A] (M ⊗ N).val.obj point := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let T := M.val ⊗ N.val
  let η := toSheafify ⊥ T.presheaf
  have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
  let e₀ : TensorProduct A (M.val.obj point) (N.val.obj point) ≃ₗ[A]
      ((PresheafOfModules.sheafification (𝟙 _)).obj T).val.obj point :=
    LinearEquiv.ofBijective
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app T).app point).hom
      (ConcreteCategory.bijective_of_isIso (η.app point))
  let e := (SheafOfModules.tensorObjIsoSheafification
    (R := CochainComplex.onePointRingSheaf A) M N).symm
  let e₁ := LinearEquiv.ofBijective (e.hom.val.app point).hom
    (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ point).map e.hom))
  exact e₀.trans e₁

private lemma tensorPointEquiv_apply {A : Type u} [CommRing A]
    (M N : RingSiteModules A) (z : TensorProduct A (M.val.obj point) (N.val.obj point)) :
    tensorPointEquiv M N z = (perfectRingTensorSectionMap M N).app point z := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_isIso {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hp : ∀ p : ℤ, Module.Projective A ((P.X p).val.obj point))
    (hf : ∀ p : ℤ, Module.Finite A ((P.X p).val.obj point)) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ (f : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n),
      PerfectRingHomTensorDegreeCondition P Q n f → ∀ r s (h : r + s = n),
        IsIso (CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
          r s n h ≫ f ≫ ringHomComplexProjection P Q n (-r)) := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro f hc r s h
  let M := (P.X (-r)).val.obj point
  let N := (Q.X s).val.obj point
  let N' := (Q.X (-r + n)).val.obj point
  have : Module.Projective A M := hp (-r)
  have : Module.Finite A M := hf (-r)
  let b := CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
    r s n h ≫ f ≫ ringHomComplexProjection P Q n (-r)
  let eT := tensorPointEquiv ((perfectRingDual P).X r) (Q.X s)
  let eD := TensorProduct.congr (dualPointEquiv P r) (LinearEquiv.refl A N)
  let eH := dualTensorHomEquiv A M N
  let q : Q.X s ≅ Q.X (-r + n) := eqToIso (congrArg Q.X (by omega : s = -r + n))
  let eQ : N ≃ₗ[A] N' := LinearEquiv.ofBijective (q.hom.val.app point).hom
    (ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation _ point).map q.hom))
  let eC : (M →ₗ[A] N) ≃ₗ[A] (M →ₗ[A] N') := LinearEquiv.arrowCongr (LinearEquiv.refl A M) eQ
  let eS := DistribMulAction.toLinearEquiv A (M →ₗ[A] N) (r * s).negOnePow
  let eB := (eD.trans eH).trans (eS.trans eC)
  let eF := homPointEquiv (P.X (-r)) (Q.X (-r + n))
  have he : eF.toLinearMap.comp ((b.val.app point).hom.comp eT.toLinearMap) =
      eB.toLinearMap := by
    apply TensorProduct.ext'
    intro lam y
    apply LinearMap.ext
    intro x
    change ringHomEvaluate P Q n (-r) point
      (f.val.app point ((CochainComplex.ιMapBifunctor (perfectRingDual P) Q
        (curriedTensor _) r s n h).val.app point
          (eT (lam ⊗ₜ[A] y)))) x = _
    rw [tensorPointEquiv_apply]
    rw [hc.2 r s h point lam y x]
    change q.hom.val.app point
        ((r * s).negOnePow • (perfectRingDualEvaluate P r point lam x • y)) =
      eQ ((r * s).negOnePow • (dualPointEquiv P r lam x • y))
    rw [dualPointEquiv_apply]
    rfl
  apply point_isIso b
  have he' (z) : (b.val.app point) z =
      eF.symm (eB (eT.symm z)) := by
    apply eF.injective
    have hh := LinearMap.congr_fun he (eT.symm z)
    change eF ((b.val.app point) (eT (eT.symm z))) = eB (eT.symm z) at hh
    rw [eT.apply_symm_apply] at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh
  have hb : (fun z ↦ (b.val.app point) z) = fun z ↦ eF.symm (eB (eT.symm z)) :=
    funext he'
  change Function.Bijective (fun z ↦ (b.val.app point) z)
  rw [hb]
  exact eF.symm.bijective.comp (eB.bijective.comp eT.symm.bijective)

private theorem finite_diagonal_isIso {C : Type*} [Category C] [Preadditive C]
    {T H : C} {X Y : ℤ → C} (ι : ∀ p, X p ⟶ T) (π : ∀ p, H ⟶ Y p)
    (hι : ∀ {Z : C} (f g : T ⟶ Z), (∀ p, ι p ≫ f = ι p ≫ g) → f = g)
    (hπ : ∀ {Z : C} (f g : Z ⟶ H), (∀ p, f ≫ π p = g ≫ π p) → f = g)
    (s : Finset ℤ) (hz : ∀ p, p ∉ s → IsZero (Y p)) (f : T ⟶ H)
    (hoff : ∀ p q, p ≠ q → ι p ≫ f ≫ π q = 0)
    (hd : ∀ p, IsIso (ι p ≫ f ≫ π p)) : IsIso f := by
  classical
  let d (p : ℤ) := ι p ≫ f ≫ π p
  let (p : ℤ) : IsIso (d p) := hd p
  let g : H ⟶ T := ∑ p ∈ s, π p ≫ inv (d p) ≫ ι p
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply hι
    intro p
    by_cases hp : p ∈ s
    · simp only [g, Preadditive.comp_sum, ← Category.assoc]
      rw [Finset.sum_eq_single p]
      · simp [d, Category.assoc]
      · intro q hq hqp
        have h := hoff p q (Ne.symm hqp)
        simpa only [Category.assoc, zero_comp] using
          congrArg (fun k ↦ k ≫ inv (d q) ≫ ι q) h
      · exact fun h ↦ (h hp).elim
    · exact ((hz p hp).of_iso (asIso (d p))).eq_of_src _ _
  · apply hπ
    intro p
    by_cases hp : p ∈ s
    · simp only [g, Preadditive.sum_comp, Category.assoc]
      rw [Finset.sum_eq_single p]
      · simp [d]
      · intro q hq hqp
        rw [hoff q p hqp, comp_zero, comp_zero]
      · exact fun h ↦ (h hp).elim
    · exact (hz p hp).eq_of_tgt _ _

/-- A normalized evaluation map is invertible for a bounded finite-projective source.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1).
(blueprint: lem-pc-perfect-ring-hom-tensor-degree-isiso)

Proof: evaluation at the unique object identifies sheaves on the bottom-topology
one-object site with A-modules, identifies sheafification with the identity, and
reflects isomorphisms. Project the dual degree r to Hom(P^(-r),A[0]^0), then identify
A[0]^0 with A. All other product factors are zero, so this projection is invertible.
For each r+s=n, the diagonal block in the normalization is therefore the map
from the dual of P^(-r) tensor Q^s to Hom(P^(-r),Q^s), multiplied by (-1)^(r*s).
The first map is invertible by Mathlib dualTensorHomEquiv for the finite projective
module P^(-r); the scalar is a unit, since its square is one. The normalization
identifies this block on pure tensors, which generate the module tensor; all other
blocks vanish by its first clause. The bound on P restricts the nonzero Hom factors
to a finite interval, and also restricts the nonzero dual factors to its negative.
Remove the zero factors, reindex r+s=n by p=-r, and identify the resulting finite
coproduct and product with the same finite biproduct. The map is then diagonal with
invertible blocks; assemble their inverses to obtain a two-sided inverse. Empty
support yields zero objects and the same inverse equations. No bound on Q is used,
and rank-zero modules and the zero ring are covered by the same argument. -/
theorem perfectRingHom_tensorDual_degree_isIso {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ f : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n,
      PerfectRingHomTensorDegreeCondition P Q n f → IsIso f := by
  classical
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro f hc
  obtain ⟨a, b, hz⟩ := hb
  let ι (r : ℤ) := CochainComplex.ιMapBifunctor (perfectRingDual P) Q
    (curriedTensor _) r (n - r) n (by omega)
  let π (r : ℤ) := ringHomComplexProjection P Q n (-r)
  apply finite_diagonal_isIso ι π ?_ ?_ (Finset.Icc (-b) (-a)) ?_ f ?_ ?_
  · intro Z g g' hg
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro r s h
    change r + s = n at h
    obtain rfl : s = n - r := by omega
    exact hg r
  · intro Z g g' hg
    apply ((homComplex_projections_exists
      (R := CochainComplex.onePointRingSheaf A)).choose_spec.1 P Q n).some.hom_ext
    intro p
    have hh := hg (-p.as)
    dsimp only [π] at hh
    rw [neg_neg] at hh
    exact hh
  · intro r hr
    let F := (SheafOfModules.homFunctor (CochainComplex.onePointRingSheaf A)).flip.obj
      (Q.X (-r + n))
    have : F.PreservesZeroMorphisms := by
      constructor
      intro M N
      exact SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left (𝟙 _))
    apply F.map_isZero
    apply IsZero.op
    apply hz (-r)
    simp only [Finset.mem_Icc, not_and_or, not_le] at hr
    omega
  · intro r t hrt
    exact hc.1 r (n - r) (by omega) (-t) (by omega)
  · intro r
    exact diagonal_isIso P Q hp hf n f hc r (n - r) (by omega)

end CategoryTheory
