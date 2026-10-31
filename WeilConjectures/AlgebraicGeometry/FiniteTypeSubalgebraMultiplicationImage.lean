/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteTypeQuasiCoherentSubalgebras
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Ring.Subring.Basic
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule

/-! # Multiplication images of finite type quasi-coherent subalgebras

Source: Stacks Project, Properties, Tag 05JT, first paragraph of the proof of
lemma-algebra-directed-colimit-finite-type, including its omitted details
(blueprint: lem-weil-pbc-finite-type-subalgebra-multiplication-image).

The section ranges use the canonical arrows of algebra-sheaf subobjects.
Subring closure of a set containing the scalar image expresses algebra generation
without choosing additional algebra structures on the section rings.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.CommAlgebraSheaf

noncomputable section

/-- Sections of an algebra subsheaf, viewed inside its ambient section ring.
Source: Stacks Project, Properties, Tag 05JT, multiplication-image paragraph
(blueprint: lem-weil-pbc-finite-type-subalgebra-multiplication-image). -/
noncomputable def subalgebraSectionRange {X : Scheme.{u}} {A : X.CommAlgebraSheaf}
    (B : Subobject A) (U : X.Opens) : Set (A.right.obj.obj (op U)) :=
  Set.range ((Subobject.arrow B).right.hom.app (op U))

/-- The pure-tensor formula characterizing the multiplication map on every open.
Source: Stacks Project, Properties, Tag 05JT, multiplication-image paragraph;
Modules, Section 01CA, presheaf tensor followed by sheafification
(blueprint: lem-weil-pbc-finite-type-subalgebra-multiplication-image). -/
def IsSubalgebraTensorMultiplication {X : Scheme.{u}} {A : X.CommAlgebraSheaf}
    (B₁ B₂ : Subobject A)
    (μ : (B₁ : X.CommAlgebraSheaf).toModule ⊗ (B₂ : X.CommAlgebraSheaf).toModule ⟶
      A.toModule) : Prop :=
  ∀ (W : X.Opens)
    (b₁ : (B₁ : X.CommAlgebraSheaf).right.obj.obj (op W))
    (b₂ : (B₂ : X.CommAlgebraSheaf).right.obj.obj (op W)),
    (μ.val.app (op W))
      (Modules.tensorSectionsMap (B₁ : X.CommAlgebraSheaf).toModule
        (B₂ : X.CommAlgebraSheaf).toModule W (b₁ ⊗ₜ[Γ(X, W)] b₂)) =
      ((Subobject.arrow B₁).right.hom.app (op W)) b₁ *
        ((Subobject.arrow B₂).right.hom.app (op W)) b₂

private def multiplicationRange {R S T D : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing D] [Module R S] [Module R T] [Module R D]
    (f : S →+* D) (g : T →+* D) (ν : S ⊗[R] T →ₗ[R] D)
    (hν : ∀ s t, ν (s ⊗ₜ[R] t) = f s * g t) : Subring D where
  carrier := Set.range ν
  zero_mem' := ⟨0, map_zero ν⟩
  add_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, map_add ν s t⟩
  neg_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨-s, map_neg ν s⟩
  one_mem' := ⟨1 ⊗ₜ[R] 1, by rw [hν, map_one, map_one, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    induction s using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp only [map_zero, zero_mul]⟩
    | tmul a b =>
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp only [map_zero, mul_zero]⟩
      | tmul c d =>
        refine ⟨(a * c) ⊗ₜ[R] (b * d), ?_⟩
        rw [hν, hν, hν, map_mul, map_mul]
        ring
      | add t t' ht ht' =>
        obtain ⟨x, hx⟩ := ht
        obtain ⟨y, hy⟩ := ht'
        exact ⟨x + y, by rw [map_add, hx, hy, map_add, mul_add]⟩
    | add s s' hs hs' =>
      obtain ⟨x, hx⟩ := hs
      obtain ⟨y, hy⟩ := hs'
      exact ⟨x + y, by rw [map_add, hx, hy, map_add, add_mul]⟩

private theorem multiplicationRange_eq_closure {R S T D : Type u} [CommRing R]
    [CommRing S] [CommRing T] [CommRing D] [Module R S] [Module R T] [Module R D]
    (f : S →+* D) (g : T →+* D) (ν : S ⊗[R] T →ₗ[R] D)
    (hν : ∀ s t, ν (s ⊗ₜ[R] t) = f s * g t) :
    multiplicationRange f g ν hν = Subring.closure (Set.range f ∪ Set.range g) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (Subring.closure _).zero_mem
    | tmul s t =>
      rw [hν]
      exact (Subring.closure _).mul_mem
        (Subring.subset_closure (Or.inl ⟨s, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨t, rfl⟩))
    | add z z' hz hz' => simpa only [map_add] using (Subring.closure _).add_mem hz hz'
  · apply Subring.closure_le.mpr
    rintro _ (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨s ⊗ₜ[R] 1, by rw [hν, map_one, mul_one]⟩
    · exact ⟨1 ⊗ₜ[R] t, by rw [hν, map_one, one_mul]⟩

private theorem closure_generators {R S T D : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing D] (a : R →+* S) (b : R →+* T) (c : R →+* D)
    (f : S →+* D) (g : T →+* D) (hf : f.comp a = c) (hg : g.comp b = c)
    {m n : ℕ} (x : Fin m → S) (y : Fin n → T)
    (hx : Subring.closure (Set.range a ∪ Set.range x) = ⊤)
    (hy : Subring.closure (Set.range b ∪ Set.range y) = ⊤) :
    Subring.closure (Set.range f ∪ Set.range g) =
      Subring.closure (Set.range c ∪ (Set.range (f ∘ x) ∪ Set.range (g ∘ y))) := by
  let K := Subring.closure (Set.range c ∪ (Set.range (f ∘ x) ∪ Set.range (g ∘ y)))
  have hmap {S : Type u} [CommRing S] (a : R →+* S) (f : S →+* D)
      (hf : f.comp a = c) {m : ℕ} (x : Fin m → S)
      (hx : Subring.closure (Set.range a ∪ Set.range x) = ⊤)
      (h : Set.range (f ∘ x) ⊆ K) : ∀ s, f s ∈ K := by
    intro s
    have hs : s ∈ Subring.closure (Set.range a ∪ Set.range x) := hx ▸ Subring.mem_top s
    induction hs using Subring.closure_induction with
    | mem z hz =>
      rcases hz with ⟨r, rfl⟩ | ⟨j, rfl⟩
      · have he := RingHom.congr_fun hf r
        change f (a r) = c r at he
        rw [he]
        exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
      · exact h ⟨j, rfl⟩
    | zero => simpa only [map_zero] using K.zero_mem
    | one => simpa only [map_one] using K.one_mem
    | add z w _ _ hz hw => simpa only [map_add] using K.add_mem hz hw
    | neg z _ hz => simpa only [map_neg] using K.neg_mem hz
    | mul z w _ _ hz hw => simpa only [map_mul] using K.mul_mem hz hw
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro _ (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · exact hmap a f hf x hx (fun _ hj ↦ Subring.subset_closure (Or.inr (Or.inl hj))) s
    · exact hmap b g hg y hy (fun _ hj ↦ Subring.subset_closure (Or.inr (Or.inr hj))) t
  · apply Subring.closure_le.mpr
    rintro _ (⟨r, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩)
    · have he := RingHom.congr_fun hf r
      change f (a r) = c r at he
      rw [← he]
      exact Subring.subset_closure (Or.inl ⟨a r, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨x j, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨y j, rfl⟩)

private theorem finiteType_of_range_closure {R S T D : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing D] (a : R →+* S) (b : R →+* T) (c : R →+* D)
    (f : S →+* D) (g : T →+* D) (hf : f.comp a = c) (hg : g.comp b = c)
    (ha : a.FiniteType) (hb : b.FiniteType)
    (hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤) : c.FiniteType := by
  classical
  let := a.toAlgebra
  let := b.toAlgebra
  let := c.toAlgebra
  obtain ⟨sx, hx⟩ := ha.out
  obtain ⟨sy, hy⟩ := hb.out
  let x : Fin sx.card → S := fun j ↦ sx.equivFin.symm j
  let y : Fin sy.card → T := fun j ↦ sy.equivFin.symm j
  have hrx : Set.range x = (sx : Set S) := by
    ext s
    constructor
    · rintro ⟨j, rfl⟩; exact (sx.equivFin.symm j).property
    · intro hs; exact ⟨sx.equivFin ⟨s, hs⟩, congrArg Subtype.val (sx.equivFin.symm_apply_apply _)⟩
  have hry : Set.range y = (sy : Set T) := by
    ext s
    constructor
    · rintro ⟨j, rfl⟩; exact (sy.equivFin.symm j).property
    · intro hs; exact ⟨sy.equivFin ⟨s, hs⟩, congrArg Subtype.val (sy.equivFin.symm_apply_apply _)⟩
  have hx' : Subring.closure (Set.range a ∪ Set.range x) = ⊤ := by
    rw [hrx]
    exact (Algebra.adjoin_eq_ring_closure (R := R) (sx : Set S)).symm.trans
      (congrArg Subalgebra.toSubring hx)
  have hy' : Subring.closure (Set.range b ∪ Set.range y) = ⊤ := by
    rw [hry]
    exact (Algebra.adjoin_eq_ring_closure (R := R) (sy : Set T)).symm.trans
      (congrArg Subalgebra.toSubring hy)
  have h := (closure_generators a b c f g hf hg x y hx' hy').symm.trans hgen
  let s : Finset D := sx.image f ∪ sy.image g
  refine ⟨s, ?_⟩
  apply Subalgebra.toSubring_injective
  rw [Algebra.adjoin_eq_ring_closure]
  change Subring.closure (Set.range c ∪ (s : Set D)) = ⊤
  convert h using 2
  dsimp [s]
  rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, Set.range_comp, Set.range_comp,
    hrx, hry]

set_option backward.isDefEq.respectTransparency false in
private theorem algebra_of_module_range {X : Scheme.{u}} (A : X.CommAlgebraSheaf)
    (M : X.Modules) [M.IsQuasicoherent] (i : M ⟶ A.toModule)
    (hi : ∀ U, Function.Injective (i.val.app U))
    (S : ∀ U : X.Opensᵒᵖ, Subring (A.right.obj.obj U))
    (hS : ∀ U, Set.range (i.val.app U) = (S U : Set (A.right.obj.obj U)))
    (hscalar : ∀ U r, (A.hom.hom.app U) r ∈ S U) :
    ∃ (D : X.CommAlgebraSheaf) (k : D ⟶ A), D.toModule.IsQuasicoherent ∧
      (∀ U, Function.Injective (k.right.hom.app U)) ∧
      ∀ U, Set.range (k.right.hom.app U) = Set.range (i.val.app U) := by
  classical
  have hsmap {U V : X.Opensᵒᵖ} (f : U ⟶ V) (s : S U) :
      (A.right.obj.map f) s.val ∈ S V := by
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp (hS U) s.val).mpr s.property
    rw [← ht]
    exact (Set.ext_iff.mp (hS V) _).mp
      ⟨M.val.map f t, PresheafOfModules.naturality_apply i.val f t⟩
  let P : X.Opensᵒᵖ ⥤ CommRingCat.{u} :=
    { obj U := CommRingCat.of (S U)
      map f := CommRingCat.ofHom
        { toFun := fun s ↦ ⟨(A.right.obj.map f) s.val, hsmap f s⟩
          map_zero' := Subtype.ext (map_zero _)
          map_one' := Subtype.ext (map_one _)
          map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
          map_mul' := fun _ _ ↦ Subtype.ext (map_mul _ _ _) }
      map_id U := by ext s; exact congrArg (fun f ↦ f s.val) (A.right.obj.map_id U)
      map_comp f g := by ext s; exact congrArg (fun f ↦ f s.val) (A.right.obj.map_comp f g) }
  let e (U : X.Opensᵒᵖ) : M.val.obj U ≃ S U :=
    Equiv.ofBijective (fun t ↦ ⟨i.val.app U t, (Set.ext_iff.mp (hS U) _).mp (Set.mem_range_self t)⟩)
      ⟨fun _ _ h ↦ hi U (congrArg Subtype.val h), by
        rintro ⟨s, hs⟩
        obtain ⟨t, ht⟩ := (Set.ext_iff.mp (hS U) s).mpr hs
        exact ⟨t, Subtype.ext ht⟩⟩
  let eP : (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) ≅
      P ⋙ CategoryTheory.forget CommRingCat :=
    NatIso.ofComponents (fun U ↦ (e U).toIso) (by
      intro U V f
      ext t
      apply Subtype.ext
      exact PresheafOfModules.naturality_apply i.val f t)
  have hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget CommRingCat)).mpr
    exact (Presheaf.isSheaf_of_iso_iff eP).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat)).mp M.isSheaf)
  let d : X.sheaf ⟶ (⟨P, hP⟩ : Sheaf (Opens.grothendieckTopology X) CommRingCat) :=
    ⟨{ app U := CommRingCat.ofHom
          { toFun := fun r ↦ ⟨(A.hom.hom.app U) r, hscalar U r⟩
            map_zero' := Subtype.ext (map_zero _)
            map_one' := Subtype.ext (map_one _)
            map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
            map_mul' := fun _ _ ↦ Subtype.ext (map_mul _ _ _) }
       naturality := by
          intro U V f
          ext r
          exact congrArg (fun k ↦ k r) (A.hom.hom.naturality f) }⟩
  let D : X.CommAlgebraSheaf := Under.mk d
  let k : D ⟶ A := Under.homMk
    (show D.right ⟶ A.right from
      ⟨{ app U := CommRingCat.ofHom (S U).subtype
         naturality := by intros; rfl }⟩) (by rfl)
  let q : M ⟶ D.toModule :=
    { val :=
        { app U := ModuleCat.ofHom (X := M.val.obj U) (Y := D.toModule.val.obj U)
            { toFun := e U
              map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
              map_smul' := fun _ _ ↦ Subtype.ext ((i.val.app U).hom.map_smul _ _) }
          naturality := by
            intro U V f
            ext t
            exact Subtype.ext (PresheafOfModules.naturality_apply i.val f t) } }
  have hq (U : X.Opensᵒᵖ) : IsIso (q.val.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (e U).bijective
  have : IsIso q := Modules.Hom.isIso_iff_isIso_app.mpr (fun U ↦ by
    have := hq (op U)
    exact Functor.map_isIso (forget₂ (ModuleCat _) AddCommGrpCat) _)
  refine ⟨D, k, (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (asIso q) inferInstance, fun U ↦ Subtype.val_injective, ?_⟩
  intro U
  change Set.range (Subtype.val : S U → A.right.obj.obj U) = _
  exact (Subtype.range_coe_subtype).trans (hS U).symm

set_option backward.isDefEq.respectTransparency false in
private theorem multiplication_exists {X : Scheme.{u}} {A : X.CommAlgebraSheaf}
    (B₁ B₂ : Subobject A) :
    ∃ μ : (B₁ : X.CommAlgebraSheaf).toModule ⊗ (B₂ : X.CommAlgebraSheaf).toModule ⟶
        A.toModule,
      IsSubalgebraTensorMultiplication B₁ B₂ μ ∧
      ∀ μ', IsSubalgebraTensorMultiplication B₁ B₂ μ' → μ' = μ := by
  let f : (B₁ : X.CommAlgebraSheaf).toModule ⟶ A.toModule :=
    (commAlgebraSheafModuleFunctor X.sheaf).map (Subobject.arrow B₁)
  let g : (B₂ : X.CommAlgebraSheaf).toModule ⟶ A.toModule :=
    (commAlgebraSheafModuleFunctor X.sheaf).map (Subobject.arrow B₂)
  let β := fun U : X.Opensᵒᵖ ↦
    LinearMap.mk₂ (X.presheaf.obj U)
      (M := (B₁ : X.CommAlgebraSheaf).toModule.val.obj U)
      (Nₗ := (B₂ : X.CommAlgebraSheaf).toModule.val.obj U)
      (Pₗ := A.toModule.val.obj U)
      (fun x y ↦ (show A.right.obj.obj U from f.val.app U x) *
        (show A.right.obj.obj U from g.val.app U y))
      (by intros; rw [map_add, add_mul])
      (by
        intro r x y
        rw [map_smul]
        change (((A.hom.hom.app U) r * (show A.right.obj.obj U from f.val.app U x)) *
          (show A.right.obj.obj U from g.val.app U y)) = _
        exact mul_assoc _ _ _)
      (by intros; rw [map_add, mul_add])
      (by
        intro r x y
        rw [map_smul]
        change (show A.right.obj.obj U from f.val.app U x) *
          ((A.hom.hom.app U) r * (show A.right.obj.obj U from g.val.app U y)) =
          (A.hom.hom.app U) r * ((show A.right.obj.obj U from f.val.app U x) *
            (show A.right.obj.obj U from g.val.app U y))
        exact mul_left_comm _ _ _)
  have hn : ∀ {U V : X.Opensᵒᵖ} (i : U ⟶ V) x y,
      β V ((B₁ : X.CommAlgebraSheaf).toModule.val.map i x)
        ((B₂ : X.CommAlgebraSheaf).toModule.val.map i y) =
      A.toModule.val.map i (β U x y) := by
    intro U V i x y
    change (show A.right.obj.obj V from f.val.app V
        ((B₁ : X.CommAlgebraSheaf).toModule.val.map i x)) *
      (show A.right.obj.obj V from g.val.app V
        ((B₂ : X.CommAlgebraSheaf).toModule.val.map i y)) =
      (A.right.obj.map i) ((show A.right.obj.obj U from f.val.app U x) *
        (show A.right.obj.obj U from g.val.app U y))
    exact (congrArg₂ (fun a b : A.right.obj.obj V ↦ a * b)
      (PresheafOfModules.naturality_apply f.val i x)
      (PresheafOfModules.naturality_apply g.val i y)).trans
      ((A.right.obj.map i).hom.map_mul _ _).symm
  obtain ⟨μ, hμ, hu⟩ := SheafOfModules.tensor_bilinear_universal X.sheaf
    (B₁ : X.CommAlgebraSheaf).toModule (B₂ : X.CommAlgebraSheaf).toModule A.toModule β hn
  refine ⟨μ, ?_, ?_⟩
  · intro W x y
    rw [Modules.tensorSectionsMap_tmul]
    convert hμ (op W) x y using 1 <;> rfl
  · intro μ' hμ'
    apply hu
    intro W x y
    have hh := hμ' W.unop x y
    rw [Modules.tensorSectionsMap_tmul] at hh
    convert hh using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem factor_of_range {X : Scheme.{u}} {B D A : X.CommAlgebraSheaf}
    (f : B ⟶ A) (k : D ⟶ A) (hk : ∀ U, Function.Injective (k.right.hom.app U))
    (h : ∀ U, Set.range (f.right.hom.app U) ⊆ Set.range (k.right.hom.app U)) :
    ∃ l : B ⟶ D, l ≫ k = f := by
  classical
  have hh (U : X.Opensᵒᵖ) (b : B.right.obj.obj U) :
      ∃ d, (k.right.hom.app U) d = (f.right.hom.app U) b := h U (Set.mem_range_self b)
  choose q hq using hh
  let l : B ⟶ D := Under.homMk
    (show B.right ⟶ D.right from
      ⟨{ app U := CommRingCat.ofHom
          { toFun := q U
            map_one' := hk U (by rw [hq, map_one, map_one])
            map_zero' := hk U (by rw [hq, map_zero, map_zero])
            map_add' := fun b c ↦ hk U (by
              rw [hq, map_add, map_add, hq, hq])
            map_mul' := fun b c ↦ hk U (by
              rw [hq, map_mul, map_mul, hq, hq]) }
         naturality := by
          intro U V i
          ext b
          apply hk V
          change (k.right.hom.app V) ((q V) ((B.right.obj.map i) b)) =
            (k.right.hom.app V) ((D.right.obj.map i) (q U b))
          rw [hq]
          have hn := congrArg (fun t ↦ t (q U b)) (k.right.hom.naturality i)
          change (k.right.hom.app V) ((D.right.obj.map i) (q U b)) =
            (A.right.obj.map i) ((k.right.hom.app U) (q U b)) at hn
          rw [hn, hq]
          exact congrArg (fun t ↦ t b) (f.right.hom.naturality i) }⟩)
    (by
      apply ObjectProperty.hom_ext
      ext U r
      apply hk U
      change (k.right.hom.app U) (q U ((B.hom.hom.app U) r)) =
        (k.right.hom.app U) ((D.hom.hom.app U) r)
      rw [hq]
      exact (congrArg (fun t ↦ t.hom.app U r) f.w).trans
        (congrArg (fun t ↦ t.hom.app U r) k.w).symm)
  refine ⟨l, ?_⟩
  apply StructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  ext U b
  exact hq U b

private theorem mk_section_range {X : Scheme.{u}} {D A : X.CommAlgebraSheaf}
    (k : D ⟶ A) [Mono k] (U : X.Opensᵒᵖ) :
    subalgebraSectionRange (Subobject.mk k) U.unop = Set.range (k.right.hom.app U) := by
  let e := Subobject.underlyingIso k
  have hh (b : (Subobject.mk k : X.CommAlgebraSheaf).right.obj.obj U) :
      (Subobject.arrow (Subobject.mk k)).right.hom.app U b =
        k.right.hom.app U (e.hom.right.hom.app U b) :=
    congrArg (fun f ↦ f.right.hom.app U b) (Subobject.underlyingIso_hom_comp_eq_mk k).symm
  ext s
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨e.hom.right.hom.app U b, (hh b).symm⟩
  · rintro ⟨d, rfl⟩
    refine ⟨e.inv.right.hom.app U d, ?_⟩
    rw [hh]
    exact congrArg (fun f ↦ k.right.hom.app U (f.right.hom.app U d)) e.inv_hom_id

set_option backward.isDefEq.respectTransparency false in
private theorem section_range_closure {X : Scheme.{u}} {A : X.CommAlgebraSheaf}
    (B₁ B₂ : Subobject A)
    (μ : (B₁ : X.CommAlgebraSheaf).toModule ⊗
      (B₂ : X.CommAlgebraSheaf).toModule ⟶ A.toModule)
    (hμ : IsSubalgebraTensorMultiplication B₁ B₂ μ) (U : X.Opens) :
    Set.range (fun z ↦ μ.val.app (op U)
      (Modules.tensorSectionsMap (B₁ : X.CommAlgebraSheaf).toModule
        (B₂ : X.CommAlgebraSheaf).toModule U z)) =
      (Subring.closure (subalgebraSectionRange B₁ U ∪ subalgebraSectionRange B₂ U) :
        Set (A.right.obj.obj (op U))) := by
  let : CommRing ((B₁ : X.CommAlgebraSheaf).toModule.val.obj (op U)) :=
    inferInstanceAs (CommRing ((B₁ : X.CommAlgebraSheaf).right.obj.obj (op U)))
  let : CommRing ((B₂ : X.CommAlgebraSheaf).toModule.val.obj (op U)) :=
    inferInstanceAs (CommRing ((B₂ : X.CommAlgebraSheaf).right.obj.obj (op U)))
  let : CommRing (A.toModule.val.obj (op U)) :=
    inferInstanceAs (CommRing (A.right.obj.obj (op U)))
  let f : (B₁ : X.CommAlgebraSheaf).toModule.val.obj (op U) →+*
      A.toModule.val.obj (op U) := ((Subobject.arrow B₁).right.hom.app (op U)).hom
  let g : (B₂ : X.CommAlgebraSheaf).toModule.val.obj (op U) →+*
      A.toModule.val.obj (op U) := ((Subobject.arrow B₂).right.hom.app (op U)).hom
  let ν := (μ.val.app (op U)).hom.comp
    (Modules.tensorSectionsMap (B₁ : X.CommAlgebraSheaf).toModule
      (B₂ : X.CommAlgebraSheaf).toModule U)
  exact congrArg (fun S : Subring (A.toModule.val.obj (op U)) ↦
    (S : Set (A.toModule.val.obj (op U))))
    (multiplicationRange_eq_closure f g ν (hμ U))

private theorem closure_top_of_injective {S T D E : Type u} [CommRing S] [CommRing T]
    [CommRing D] [CommRing E] (f : S →+* D) (g : T →+* D) (k : D →+* E)
    (hk : Function.Injective k)
    (h : (Subring.closure (Set.range (k.comp f) ∪ Set.range (k.comp g)) : Set E) =
      Set.range k) : Subring.closure (Set.range f ∪ Set.range g) = ⊤ := by
  let K := Subring.closure (Set.range f ∪ Set.range g)
  have hle : Subring.closure (Set.range (k.comp f) ∪ Set.range (k.comp g)) ≤ K.map k := by
    apply Subring.closure_le.mpr
    rintro _ (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨f s, Subring.subset_closure (Or.inl ⟨s, rfl⟩), rfl⟩
    · exact ⟨g t, Subring.subset_closure (Or.inr ⟨t, rfl⟩), rfl⟩
  apply eq_top_iff.mpr
  intro d _
  have hd := hle ((Set.ext_iff.mp h (k d)).mpr ⟨d, rfl⟩)
  obtain ⟨d', hd', he⟩ := hd
  exact hk he ▸ hd'

set_option maxHeartbeats 800000 in
-- Transport between algebra sections and underlying modules needs extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
private theorem image_subring {X : Scheme.{u}} {A : X.CommAlgebraSheaf}
    (B₁ B₂ : A.finiteTypeQuasiCoherentSubalgebras)
    (μ : (B₁.val : X.CommAlgebraSheaf).toModule ⊗
      (B₂.val : X.CommAlgebraSheaf).toModule ⟶ A.toModule)
    (hμ : IsSubalgebraTensorMultiplication B₁.val B₂.val μ)
    [A.toModule.IsQuasicoherent] :
    ∃ S : ∀ U : X.Opensᵒᵖ, Subring (A.right.obj.obj U),
      (∀ U, Set.range ((Abelian.image.ι μ).val.app U) = (S U : Set (A.right.obj.obj U))) ∧
      (∀ U r, (A.hom.hom.app U) r ∈ S U) ∧
      ∀ (U : X.Opens) (_hU : IsAffineOpen U),
        (S (op U) : Set (A.right.obj.obj (op U))) = Set.range (fun z ↦ μ.val.app (op U)
          (Modules.tensorSectionsMap (B₁.val : X.CommAlgebraSheaf).toModule
            (B₂.val : X.CommAlgebraSheaf).toModule U z)) := by
  have := B₁.property.1
  have := B₂.property.1
  obtain ⟨hq, ht⟩ := Modules.quasiCoherent_tensor_product_affine_sections
    (B₁.val : X.CommAlgebraSheaf).toModule (B₂.val : X.CommAlgebraSheaf).toModule
  have := hq
  obtain ⟨_, _, hloc, _, _, _, _, hqi, haff⟩ := Modules.quasiCoherent_cokernel_image μ
  let I (U : X.Opensᵒᵖ) := LinearMap.range ((Abelian.image.ι μ).val.app U).hom
  let ν (U : X.Opens) := (μ.val.app (op U)).hom.comp
    (Modules.tensorSectionsMap (B₁.val : X.CommAlgebraSheaf).toModule
      (B₂.val : X.CommAlgebraSheaf).toModule U)
  let inst₁ (U : X.Opens) : Module Γ(X, U)
      ((B₁.val : X.CommAlgebraSheaf).right.obj.obj (op U)) :=
    inferInstanceAs (Module Γ(X, U) ((B₁.val : X.CommAlgebraSheaf).toModule.val.obj (op U)))
  let inst₂ (U : X.Opens) : Module Γ(X, U)
      ((B₂.val : X.CommAlgebraSheaf).right.obj.obj (op U)) :=
    inferInstanceAs (Module Γ(X, U) ((B₂.val : X.CommAlgebraSheaf).toModule.val.obj (op U)))
  let instA (U : X.Opens) : Module Γ(X, U) (A.right.obj.obj (op U)) :=
    inferInstanceAs (Module Γ(X, U) (A.toModule.val.obj (op U)))
  let T (U : X.Opens) : Subring (A.right.obj.obj (op U)) := multiplicationRange
    ((Subobject.arrow B₁.val).right.hom.app (op U)).hom
    ((Subobject.arrow B₂.val).right.hom.app (op U)).hom
    (show ((B₁.val : X.CommAlgebraSheaf).right.obj.obj (op U)) ⊗[Γ(X, U)]
      ((B₂.val : X.CommAlgebraSheaf).right.obj.obj (op U)) →ₗ[Γ(X, U)]
        A.right.obj.obj (op U) from ν U) (hμ U)
  have hT (U : X.Opens) (hU : IsAffineOpen U) :
      (show Set (A.right.obj.obj (op U)) from
        (I (op U) : Set (A.toModule.val.obj (op U)))) = (T U : Set _) := by
    change Set.range (Modules.Hom.app (Abelian.image.ι μ) U) = Set.range (ν U)
    rw [(haff ⟨U, hU⟩).1]
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨z, rfl⟩ := (ht U hU).2 t
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨_, rfl⟩
  have hlocal (W : X.Opens) (s : A.right.obj.obj (op W))
      (hs : ∀ (V : X.Opens) (h : V ≤ W), IsAffineOpen V →
        (A.right.obj.map (homOfLE h).op) s ∈ I (op V)) : s ∈ I (op W) := by
    apply (hloc W s).mpr
    intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    have hv := hs V hVW hV
    have hv' := (Set.ext_iff.mp (hT V hV) _).mp hv
    obtain ⟨z, hz⟩ := hv'
    exact ⟨V, hVW, hxV, _, hz⟩
  let S (U : X.Opensᵒᵖ) : Subring (A.right.obj.obj U) :=
    { carrier := (show Set (A.right.obj.obj U) from (I U : Set (A.toModule.val.obj U)))
      zero_mem' := (I U).zero_mem
      add_mem' := (I U).add_mem
      neg_mem' := (I U).neg_mem
      one_mem' := by
        apply hlocal U.unop 1
        intro V hVU hV
        rw [map_one]
        exact (Set.ext_iff.mp (hT V hV) 1).mpr (T V).one_mem
      mul_mem' := by
        intro s t hs ht'
        apply hlocal U.unop (s * t)
        intro V hVU hV
        have hr (s : A.right.obj.obj U) (hs : s ∈ I U) :
            (A.right.obj.map (homOfLE hVU).op) s ∈ I (op V) := by
          obtain ⟨z, rfl⟩ := hs
          exact ⟨(Abelian.image μ).val.map (homOfLE hVU).op z,
            PresheafOfModules.naturality_apply (Abelian.image.ι μ).val _ z⟩
        rw [map_mul]
        exact (Set.ext_iff.mp (hT V hV) _).mpr ((T V).mul_mem
          ((Set.ext_iff.mp (hT V hV) _).mp (hr s hs))
          ((Set.ext_iff.mp (hT V hV) _).mp (hr t ht'))) }
  refine ⟨S, fun _ ↦ rfl, ?_, fun U hU ↦ hT U hU⟩
  intro U r
  apply hlocal U.unop ((A.hom.hom.app U) r)
  intro V hVU hV
  have hn := congrArg (fun k ↦ k r) (A.hom.hom.naturality (homOfLE hVU).op)
  change (A.right.obj.map (homOfLE hVU).op) ((A.hom.hom.app U) r) ∈ I (op V)
  change (A.hom.hom.app (op V)) (X.presheaf.map (homOfLE hVU).op r) =
    (A.right.obj.map (homOfLE hVU).op) ((A.hom.hom.app U) r) at hn
  rw [← hn]
  apply (Set.ext_iff.mp (hT V hV) _).mpr
  let b := ((B₁.val : X.CommAlgebraSheaf).hom.hom.app (op V))
    (X.presheaf.map (homOfLE hVU).op r)
  refine ⟨b ⊗ₜ[Γ(X, V)] 1, ?_⟩
  change μ.val.app (op V) (Modules.tensorSectionsMap
    (B₁.val : X.CommAlgebraSheaf).toModule
    (B₂.val : X.CommAlgebraSheaf).toModule V
    (b ⊗ₜ[Γ(X, V)] (show (B₂.val : X.CommAlgebraSheaf).toModule.val.obj (op V) from
      (1 : (B₂.val : X.CommAlgebraSheaf).right.obj.obj (op V))))) = _
  rw [hμ V, map_one, mul_one]
  exact congrArg (fun k ↦ k.hom.app (op V) (X.presheaf.map (homOfLE hVU).op r))
    (Subobject.arrow B₁.val).w

set_option maxHeartbeats 800000 in
-- Transport between algebra sections and underlying modules needs extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
/-- The unique tensor multiplication map has a finite type quasi-coherent algebra
sheaf image containing both factors, with the asserted affine image and generator formulas.
Source: Stacks Project, Properties, Tag 05JT, proof, first paragraph, lines 3358-3362
(blueprint: lem-weil-pbc-finite-type-subalgebra-multiplication-image).

Proof:
1. Multiplication of sections is bilinear by distributivity and the scalar identities.
   The module tensor universal property (def-weil-pbc-module-tensor-product) gives
   the sectionwise maps. They commute with restriction, as checked on pure tensors.
   The proved sheaf tensor bilinear universal property
   (lem-pc-sites-sheaf-tensor-bilinear-universal) packages the sheafification
   extension to the tensor sheaf (def-pur-sheaf-tensor-product) and its uniqueness.
2. Apply lem-weil-pbc-quasi-coherent-tensor-product-affine-sections to the two
   quasi-coherent underlying modules. Apply lem-weil-pbc-quasi-coherent-module-cokernel-image
   to the resulting multiplication map and its quasi-coherent target. Its local
   image is quasi-coherent, and on every affine open its sections are the range
   of multiplication on the section tensor product.
3. That range consists of finite sums of products b*c. It contains both factors
   and the scalars, using 1. Products remain in it by the double-sum formula
   (sum b_i*c_i)*(sum b'_j*c'_j) = sum (b_i*b'_j)*(c_i*c'_j).
   It is therefore precisely the subalgebra generated by the two factors.
   The affine basis (lem-weil-pbc-affine-opens-basis) and the sheaf property show
   on arbitrary opens that the local image is closed under products and 1,
   and contains both algebra subsheaves.
4. On an affine open, the algebra generated by the combined finite generator lists
   contains both factors and is contained in their generated algebra. Hence it
   equals the image algebra. Such lists exist by the finite type hypotheses
   (def-weil-pbc-finite-type-quasi-coherent-subalgebras), proving finite type.
-/
theorem finiteType_subalgebra_multiplication_image {X : Scheme.{u}}
    (A : X.CommAlgebraSheaf) [A.toModule.IsQuasicoherent]
    (B₁ B₂ : A.finiteTypeQuasiCoherentSubalgebras) :
    ∃ μ : (B₁.val : X.CommAlgebraSheaf).toModule ⊗
        (B₂.val : X.CommAlgebraSheaf).toModule ⟶ A.toModule,
      IsSubalgebraTensorMultiplication B₁.val B₂.val μ ∧
      (∀ μ' : (B₁.val : X.CommAlgebraSheaf).toModule ⊗
          (B₂.val : X.CommAlgebraSheaf).toModule ⟶ A.toModule,
        IsSubalgebraTensorMultiplication B₁.val B₂.val μ' → μ' = μ) ∧
      ∃ C : A.finiteTypeQuasiCoherentSubalgebras,
        (∀ (W : X.Opens) (s : A.right.obj.obj (op W)),
          s ∈ subalgebraSectionRange C.val W ↔
            ∀ x : X, x ∈ W → ∃ (V : X.Opens) (h : V ≤ W),
              x ∈ V ∧ ∃ t : Γ((B₁.val : X.CommAlgebraSheaf).toModule ⊗
                  (B₂.val : X.CommAlgebraSheaf).toModule, V),
                (μ.val.app (op V)) t = A.right.obj.map (homOfLE h).op s) ∧
        B₁.val ≤ C.val ∧ B₂.val ≤ C.val ∧
        (∀ (U : X.Opens), IsAffineOpen U →
          subalgebraSectionRange C.val U =
            Set.range (fun z ↦ (μ.val.app (op U))
              (Modules.tensorSectionsMap (B₁.val : X.CommAlgebraSheaf).toModule
                (B₂.val : X.CommAlgebraSheaf).toModule U z)) ∧
          subalgebraSectionRange C.val U =
            (Subring.closure (subalgebraSectionRange B₁.val U ∪
              subalgebraSectionRange B₂.val U) : Set (A.right.obj.obj (op U))) ∧
          ∀ (m n : ℕ)
            (x : Fin m → (B₁.val : X.CommAlgebraSheaf).right.obj.obj (op U))
            (y : Fin n → (B₂.val : X.CommAlgebraSheaf).right.obj.obj (op U)),
            Subring.closure
                (Set.range ((B₁.val : X.CommAlgebraSheaf).hom.hom.app (op U)) ∪
                  Set.range x) = ⊤ →
            Subring.closure
                (Set.range ((B₂.val : X.CommAlgebraSheaf).hom.hom.app (op U)) ∪
                  Set.range y) = ⊤ →
            subalgebraSectionRange C.val U =
              (Subring.closure (Set.range (A.hom.hom.app (op U)) ∪
                (Set.range (fun i ↦ ((Subobject.arrow B₁.val).right.hom.app (op U)) (x i)) ∪
                  Set.range (fun j ↦ ((Subobject.arrow B₂.val).right.hom.app (op U)) (y j)))) :
                    Set (A.right.obj.obj (op U)))) := by
  classical
  obtain ⟨μ, hμ, hu⟩ := multiplication_exists B₁.val B₂.val
  refine ⟨μ, hμ, hu, ?_⟩
  have := B₁.property.1
  have := B₂.property.1
  obtain ⟨hq, ht⟩ := Modules.quasiCoherent_tensor_product_affine_sections
    (B₁.val : X.CommAlgebraSheaf).toModule (B₂.val : X.CommAlgebraSheaf).toModule
  have := hq
  obtain ⟨_, _, hloc, _, _, _, _, hqi, haff⟩ := Modules.quasiCoherent_cokernel_image μ
  have := hqi
  obtain ⟨S, hS, hscalar, hAffine⟩ := image_subring B₁ B₂ μ hμ
  have hi (U : X.Opensᵒᵖ) : Function.Injective ((Abelian.image.ι μ).val.app U) := by
    have : Mono ((Abelian.image.ι μ).val.app U) :=
      inferInstanceAs (Mono ((SheafOfModules.evaluation X.ringCatSheaf U).map
        (Abelian.image.ι μ)))
    exact (ModuleCat.mono_iff_injective _).mp this
  obtain ⟨D, k, hD, hk, hrange⟩ :=
    algebra_of_module_range A (Abelian.image μ) (Abelian.image.ι μ) hi S hS hscalar
  have hcontains (B : Subobject A)
      (hb : ∀ W b, (Subobject.arrow B).right.hom.app (op W) b ∈
        Set.range ((Abelian.image.ι μ).val.app (op W))) :
      ∃ l : (B : X.CommAlgebraSheaf) ⟶ D, l ≫ k = Subobject.arrow B := by
    apply factor_of_range (Subobject.arrow B) k hk
    intro U s hs
    obtain ⟨b, rfl⟩ := hs
    exact (hrange U).symm ▸ hb U.unop b
  obtain ⟨l₁, hl₁⟩ := hcontains B₁.val (by
    intro W b
    apply (hloc W _).mpr
    intro x hx
    refine ⟨W, le_refl W, hx, Modules.tensorSectionsMap
      (B₁.val : X.CommAlgebraSheaf).toModule (B₂.val : X.CommAlgebraSheaf).toModule W
      (b ⊗ₜ[Γ(X, W)]
        (show (B₂.val : X.CommAlgebraSheaf).toModule.val.obj (op W) from
          (1 : (B₂.val : X.CommAlgebraSheaf).right.obj.obj (op W)))), ?_⟩
    change μ.val.app (op W) (Modules.tensorSectionsMap
      (B₁.val : X.CommAlgebraSheaf).toModule
      (B₂.val : X.CommAlgebraSheaf).toModule W _) =
      (A.right.obj.map (𝟙 (op W))) _
    rw [hμ, map_one, mul_one]
    exact (congrArg (fun f : A.right.obj.obj (op W) ⟶ A.right.obj.obj (op W) ↦
      f ((Subobject.arrow B₁.val).right.hom.app (op W) b))
      (A.right.obj.map_id (op W))).symm)
  obtain ⟨l₂, hl₂⟩ := hcontains B₂.val (by
    intro W b
    apply (hloc W _).mpr
    intro x hx
    refine ⟨W, le_refl W, hx, Modules.tensorSectionsMap
      (B₁.val : X.CommAlgebraSheaf).toModule (B₂.val : X.CommAlgebraSheaf).toModule W
      ((show (B₁.val : X.CommAlgebraSheaf).toModule.val.obj (op W) from
        (1 : (B₁.val : X.CommAlgebraSheaf).right.obj.obj (op W))) ⊗ₜ[Γ(X, W)] b), ?_⟩
    change μ.val.app (op W) (Modules.tensorSectionsMap
      (B₁.val : X.CommAlgebraSheaf).toModule
      (B₂.val : X.CommAlgebraSheaf).toModule W _) =
      (A.right.obj.map (𝟙 (op W))) _
    rw [hμ, map_one, one_mul]
    exact (congrArg (fun f : A.right.obj.obj (op W) ⟶ A.right.obj.obj (op W) ↦
      f ((Subobject.arrow B₂.val).right.hom.app (op W) b))
      (A.right.obj.map_id (op W))).symm)
  have hclosure (U : X.Opens) (hU : IsAffineOpen U) :
      Set.range (k.right.hom.app (op U)) =
      (Subring.closure (subalgebraSectionRange B₁.val U ∪
        subalgebraSectionRange B₂.val U) : Set (A.right.obj.obj (op U))) :=
    (hrange (op U)).trans ((hS (op U)).trans
      ((hAffine U hU).trans (section_range_closure B₁.val B₂.val μ hμ U)))
  have hfinite (U : X.Opens) (hU : IsAffineOpen U) :
      ((D.hom.hom.app (op U)).hom).FiniteType := by
    apply finiteType_of_range_closure
      ((B₁.val : X.CommAlgebraSheaf).hom.hom.app (op U)).hom
      ((B₂.val : X.CommAlgebraSheaf).hom.hom.app (op U)).hom
      ((D.hom.hom.app (op U)).hom)
      (l₁.right.hom.app (op U)).hom (l₂.right.hom.app (op U)).hom
    · exact congrArg (fun f ↦ (f.hom.app (op U)).hom) l₁.w
    · exact congrArg (fun f ↦ (f.hom.app (op U)).hom) l₂.w
    · exact B₁.property.2 U hU
    · exact B₂.property.2 U hU
    · apply closure_top_of_injective _ _ (k.right.hom.app (op U)).hom (hk (op U))
      have he₁ := congrArg (fun f : (B₁.val : X.CommAlgebraSheaf) ⟶ A ↦
        (f.right.hom.app (op U)).hom) hl₁
      have he₂ := congrArg (fun f : (B₂.val : X.CommAlgebraSheaf) ⟶ A ↦
        (f.right.hom.app (op U)).hom) hl₂
      change (k.right.hom.app (op U)).hom.comp (l₁.right.hom.app (op U)).hom = _ at he₁
      change (k.right.hom.app (op U)).hom.comp (l₂.right.hom.app (op U)).hom = _ at he₂
      rw [he₁, he₂]
      exact (hclosure U hU).symm
  have hmono : Mono k := by
    constructor
    intro Z f g hfg
    apply StructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    ext U z
    apply hk U
    exact congrArg (fun t ↦ t.right.hom.app U z) hfg
  let C : Subobject A := Subobject.mk k
  let e : (C : X.CommAlgebraSheaf) ≅ D := Subobject.underlyingIso k
  have hqc : (C : X.CommAlgebraSheaf).toModule.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((commAlgebraSheafModuleFunctor X.sheaf).mapIso e.symm) hD
  have hfin (U : X.Opens) (hU : IsAffineOpen U) :
      (((C : X.CommAlgebraSheaf).hom.hom.app (op U)).hom).FiniteType := by
    have he := congrArg (fun f ↦ (f.hom.app (op U)).hom) e.inv.w
    have hs : Function.Surjective (e.inv.right.hom.app (op U)) :=
      (ConcreteCategory.bijective_of_isIso _).2
    exact he ▸ (hfinite U hU).comp_surjective hs
  refine ⟨⟨C, hqc, hfin⟩, ?_, Subobject.le_mk_of_comm l₁ hl₁,
    Subobject.le_mk_of_comm l₂ hl₂, ?_⟩
  · intro W s
    rw [mk_section_range k, hrange]
    exact hloc W s
  · intro U hU
    have hr := (mk_section_range k (op U)).trans (hrange (op U))
    have hc := (mk_section_range k (op U)).trans (hclosure U hU)
    refine ⟨hr.trans ((hS (op U)).trans (hAffine U hU)), hc, ?_⟩
    intro m n x y hx hy
    rw [hc]
    exact congrArg (fun S : Subring (A.right.obj.obj (op U)) ↦ (S : Set (A.right.obj.obj (op U))))
      (closure_generators
        ((B₁.val : X.CommAlgebraSheaf).hom.hom.app (op U)).hom
        ((B₂.val : X.CommAlgebraSheaf).hom.hom.app (op U)).hom
        (A.hom.hom.app (op U)).hom
        ((Subobject.arrow B₁.val).right.hom.app (op U)).hom
        ((Subobject.arrow B₂.val).right.hom.app (op U)).hom
        (congrArg (fun f ↦ (f.hom.app (op U)).hom) (Subobject.arrow B₁.val).w)
        (congrArg (fun f ↦ (f.hom.app (op U)).hom) (Subobject.arrow B₂.val).w)
        x y hx hy)

end

end AlgebraicGeometry.Scheme.CommAlgebraSheaf
