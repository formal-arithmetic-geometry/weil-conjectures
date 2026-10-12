/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechCriterion
public import WeilConjectures.CategoryTheory.Sites.Hypercover.FreeResolution
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sheaf cohomology through hypercovers

Let `(C, J)` be a site with a terminal object `T`, and `F` an abelian sheaf. For a hypercover
`U` of `T` and `q ≥ 0`, we construct a map `cechToH` from the `q`-cocycles of `C^•(U, F)` to the
sheaf cohomology `H^q(F)`, by dimension shifting along the canonical short exact sequence
`0 → F → I(F) → Q(F) → 0`, `I(F)` injective: a `(q + 1)`-cocycle `c` of `F` is the coboundary
of a cochain `b` of `I(F)` (`C^•(U, I(F))` is exact in positive degrees, blueprint
`lem-weil-pbc-hypercover-free-resolution`), the image of `b` in `Q(F)` is a `q`-cocycle, and we
apply the connecting map `H^q(Q(F)) → H^{q+1}(F)`.

The map is additive, kills coboundaries, and is compatible with refinements of hypercovers.
For a class of hypercovers in which local lifting requirements can always be met after
refinement (blueprint `lem-weil-pbc-hypercover-refinement`), every cohomology class is
represented by a cocycle on some hypercover of the class, and a cocycle representing `0`
becomes a coboundary after refinement. Together with the existence of common refinements, this
says that `H^q(F)` is the colimit of the cohomology groups `H^q(C^•(U, F))` over the class
(blueprint `thm-weil-pbc-hypercover-cohomology`).

## Main definitions

- `CategoryTheory.SimplicialObject.cechToH`: the comparison map.

## Main statements

- `CategoryTheory.SimplicialObject.cechToH_add`, `cechToH_cechD`, `cechToH_pull`: additivity,
  vanishing on coboundaries, compatibility with refinements.
- `CategoryTheory.SimplicialObject.exists_cechToH_eq`: surjectivity.
- `CategoryTheory.SimplicialObject.exists_cechD_eq_pull_of_cechToH_eq_zero`: injectivity after
  refinement.
-/

@[expose] public section

universe w' w v s

open CategoryTheory Limits Opposite Simplicial

namespace CategoryTheory

namespace SimplicialObject

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {T : C} (hT : IsTerminal T)

section Cochains

variable (U : SimplicialObject C) (F : Sheaf J AddCommGrpCat.{max w v})

/-- The differential `C^q(U, F) → C^{q+1}(U, F)`, as a morphism of abelian groups. -/
noncomputable abbrev cechD (q : ℕ) :
    F.obj.obj (op (U _⦋q⦌)) →+ F.obj.obj (op (U _⦋q + 1⦌)) :=
  ConcreteCategory.hom ((cechComplex U F.obj).d q (q + 1))

/-- Restriction of sections along `U_0 → T`. -/
noncomputable abbrev restr : F.obj.obj (op T) →+ F.obj.obj (op (U _⦋0⦌)) :=
  ConcreteCategory.hom (F.obj.map (hT.from (U _⦋0⦌)).op)

variable {U} in
/-- Pullback of cochains along a morphism of simplicial objects. -/
noncomputable abbrev pull {V : SimplicialObject C} (f : V ⟶ U) (q : ℕ) :
    F.obj.obj (op (U _⦋q⦌)) →+ F.obj.obj (op (V _⦋q⦌)) :=
  ConcreteCategory.hom (F.obj.map (f.app (op ⦋q⦌)).op)

lemma cechD_cechD (q : ℕ) (a : F.obj.obj (op (U _⦋q⦌))) :
    cechD U F (q + 1) (cechD U F q a) = 0 :=
  ConcreteCategory.congr_hom ((cechComplex U F.obj).d_comp_d q (q + 1) (q + 2)) a

set_option backward.isDefEq.respectTransparency false in
lemma cechD_app {G : Sheaf J AddCommGrpCat.{max w v}} (α : F ⟶ G) (q : ℕ)
    (x : F.obj.obj (op (U _⦋q⦌))) :
    cechD U G q (α.hom.app _ x) = α.hom.app _ (cechD U F q x) := by
  have h := ConcreteCategory.congr_hom ((cechComplexMapRight U α.hom).comm q (q + 1)) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [cechComplexMapRight_f, cechComplexMapRight_f] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
variable {U} in
lemma cechD_pull {V : SimplicialObject C} (f : V ⟶ U) (q : ℕ) (x : F.obj.obj (op (U _⦋q⦌))) :
    cechD V F q (pull F f q x) = pull F f (q + 1) (cechD U F q x) := by
  have h := ConcreteCategory.congr_hom ((cechComplexMap f F.obj).comm q (q + 1)) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [cechComplexMap_f, cechComplexMap_f] at h
  exact h

variable {U} in
lemma pull_app {V : SimplicialObject C} (f : V ⟶ U) {G : Sheaf J AddCommGrpCat.{max w v}}
    (α : F ⟶ G) (q : ℕ) (x : F.obj.obj (op (U _⦋q⦌))) :
    pull G f q (α.hom.app _ x) = α.hom.app _ (pull F f q x) :=
  (NatTrans.naturality_apply α.hom _ x).symm

variable {U} in
lemma pull_comp {V V' : SimplicialObject C} (f : V ⟶ U) (g : V' ⟶ V) (q : ℕ)
    (x : F.obj.obj (op (U _⦋q⦌))) : pull F g q (pull F f q x) = pull F (g ≫ f) q x := by
  change _ = ConcreteCategory.hom (F.obj.map ((g ≫ f).app _).op) x
  rw [NatTrans.comp_app, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

variable {U} in
lemma pull_restr {V : SimplicialObject C} (f : V ⟶ U) (t : F.obj.obj (op T)) :
    pull F f 0 (restr hT U F t) = restr hT V F t := by
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rw [hT.hom_ext (f.app (op ⦋0⦌) ≫ hT.from (U _⦋0⦌)) (hT.from (V _⦋0⦌))]

lemma restr_app {G : Sheaf J AddCommGrpCat.{max w v}} (α : F ⟶ G) (t : F.obj.obj (op T)) :
    restr hT U G (α.hom.app _ t) = α.hom.app _ (restr hT U F t) :=
  (NatTrans.naturality_apply α.hom _ t).symm

private lemma sum_apply {M N : AddCommGrpCat.{s}} {κ : Type*} (f : κ → (M ⟶ N))
    (s : Finset κ) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv f s) x)

set_option backward.isDefEq.respectTransparency false in
lemma cechD_restr (t : F.obj.obj (op T)) : cechD U F 0 (restr hT U F t) = 0 := by
  have h : F.obj.map (hT.from (U _⦋0⦌)).op ≫ (cechComplex U F.obj).d 0 1 = 0 := by
    rw [cechComplex_d_eq, Preadditive.comp_sum]
    simp only [Preadditive.comp_zsmul, ← Functor.map_comp, ← op_comp]
    rw [Fin.sum_univ_two, hT.hom_ext (U.δ 0 ≫ _) (hT.from _),
      hT.hom_ext (U.δ 1 ≫ _) (hT.from _)]
    simp
  have h' := ConcreteCategory.congr_hom h t
  rw [ConcreteCategory.comp_apply] at h'
  exact h'.trans rfl

end Cochains

section Comparison

variable [HasSheafify J AddCommGrpCat.{max w v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})]

/-- The canonical short exact sequence `0 → F → I(F) → Q(F) → 0` with `I(F)` injective. -/
noncomputable abbrev injSES (F : Sheaf J AddCommGrpCat.{max w v}) :
    ShortComplex (Sheaf J AddCommGrpCat.{max w v}) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

lemma injSES_shortExact (F : Sheaf J AddCommGrpCat.{max w v}) : (injSES F).ShortExact :=
  .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

instance (F : Sheaf J AddCommGrpCat.{max w v}) : Injective (injSES F).X₂ := by
  dsimp [injSES]
  infer_instance

open scoped Classical in
/-- The comparison map from the cochains of `C^•(U, F)` to the sheaf cohomology `H^q(F)`, for a
simplicial object `U` of a site with terminal object `T`. In degree `0`, a cocycle is the
restriction of a unique section over `T`. In degree `q + 1`, a cocycle `c` is the coboundary of a
cochain `b` of the injective sheaf `I(F)`, and `cechToH c` is the image of `cechToH b̄` under the
connecting map `H^q(Q(F)) → H^{q+1}(F)`. It is meaningful on cocycles of hypercovers. -/
noncomputable def cechToH : (q : ℕ) → (F : Sheaf J AddCommGrpCat.{max w v}) →
    (U : SimplicialObject C) → F.obj.obj (op (U _⦋q⦌)) → Sheaf.H.{w'} F q
  | 0, F, U, c => (Sheaf.H.equiv₀ F hT).symm
      (if h : ∃ t, restr hT U F t = c then h.choose else 0)
  | q + 1, F, U, c => Sheaf.H.δSucc (injSES_shortExact F) q
      (cechToH q (injSES F).X₃ U ((injSES F).g.hom.app _
        (if h : ∃ b, cechD U (injSES F).X₂ q b = (injSES F).f.hom.app _ c then h.choose
          else 0)))

variable {hT} {U : SimplicialObject C}

/-- Every `0`-cocycle of a hypercover is the restriction of a section over `T`. -/
lemma exists_restr_eq (hU : (U.augmentOfIsTerminal hT).IsHypercover J)
    (F : Sheaf J AddCommGrpCat.{max w v}) (c : F.obj.obj (op (U _⦋0⦌)))
    (hc : cechD U F 0 c = 0) : ∃ t, restr hT U F t = c := by
  have hS := injSES_shortExact F
  obtain ⟨t, ht⟩ := hU.exists_eq_of_cechComplex_d_zero_of_injective (injSES F).X₂
    ((injSES F).f.hom.app _ c) (by
      change cechD U _ 0 _ = 0
      rw [cechD_app, hc, map_zero])
  have h1 : (injSES F).g.hom.app _ t = 0 := by
    refine hU.map_injective (injSES F).X₃ ?_
    change restr hT U _ _ = restr hT U _ 0
    rw [restr_app, map_zero]
    erw [ht]
    exact Sheaf.app_g_app_f _ _
  obtain ⟨s, rfl⟩ := Sheaf.exists_app_f_eq hS _ t h1
  refine ⟨s, Sheaf.injective_app_f hS _ ?_⟩
  rw [← restr_app]
  exact ht

lemma cechToH_zero_eq (hU : (U.augmentOfIsTerminal hT).IsHypercover J)
    (F : Sheaf J AddCommGrpCat.{max w v}) (t : F.obj.obj (op T)) :
    cechToH.{w'} hT 0 F U (restr hT U F t) = (Sheaf.H.equiv₀ F hT).symm t := by
  have h : ∃ t', restr hT U F t' = restr hT U F t := ⟨t, rfl⟩
  simp only [cechToH, dif_pos h]
  congr 1
  exact hU.map_injective F h.choose_spec

variable (J hT) in
/-- Additivity of `cechToH` on cocycles, in a fixed degree. -/
def CechToHAdd (q : ℕ) : Prop :=
  ∀ (F : Sheaf J AddCommGrpCat.{max w v}) (U : SimplicialObject C),
    (U.augmentOfIsTerminal hT).IsHypercover J → ∀ c c' : F.obj.obj (op (U _⦋q⦌)),
      cechD U F q c = 0 → cechD U F q c' = 0 →
        cechToH.{w'} hT q F U (c + c') = cechToH hT q F U c + cechToH hT q F U c'

variable (J hT) in
/-- `cechToH` in degree `q + 1` may be computed with any primitive `b`. -/
def CechToHSucc (q : ℕ) : Prop :=
  ∀ (F : Sheaf J AddCommGrpCat.{max w v}) (U : SimplicialObject C),
    (U.augmentOfIsTerminal hT).IsHypercover J → ∀ (c : F.obj.obj (op (U _⦋q + 1⦌)))
      (b : (injSES F).X₂.obj.obj (op (U _⦋q⦌))),
      cechD U (injSES F).X₂ q b = (injSES F).f.hom.app _ c →
        cechToH.{w'} hT (q + 1) F U c = Sheaf.H.δSucc (injSES_shortExact F) q
          (cechToH hT q (injSES F).X₃ U ((injSES F).g.hom.app _ b))

variable (J hT) in
/-- `cechToH` kills coboundaries, in a fixed degree. -/
def CechToHCob (q : ℕ) : Prop :=
  ∀ (F : Sheaf J AddCommGrpCat.{max w v}) (U : SimplicialObject C),
    (U.augmentOfIsTerminal hT).IsHypercover J → ∀ a : F.obj.obj (op (U _⦋q⦌)),
      cechToH.{w'} hT (q + 1) F U (cechD U F q a) = 0

variable (hT) in
lemma cechToHAdd_zero : CechToHAdd.{w'} J hT 0 := by
  intro F U hU c c' hc hc'
  obtain ⟨t, rfl⟩ := exists_restr_eq hU F c hc
  obtain ⟨t', rfl⟩ := exists_restr_eq hU F c' hc'
  rw [← map_add, cechToH_zero_eq hU, cechToH_zero_eq hU, cechToH_zero_eq hU, map_add]

lemma cechToH_zero_of_add {q : ℕ} (hA : CechToHAdd.{w'} J hT q)
    (F : Sheaf J AddCommGrpCat.{max w v}) (hU : (U.augmentOfIsTerminal hT).IsHypercover J) :
    cechToH.{w'} hT q F U 0 = 0 := by
  have := hA F U hU 0 0 (map_zero _) (map_zero _)
  rw [add_zero] at this
  exact left_eq_add.mp this

/-- The common part of the proofs of `CechToHSucc`: two primitives `b₀, b` of the same cocycle
give the same value as soon as the difference of their images is killed. -/
lemma cechToH_succ_eq_aux {q : ℕ} (hA : CechToHAdd.{w'} J hT q) (F : Sheaf J AddCommGrpCat.{max w v})
    (hU : (U.augmentOfIsTerminal hT).IsHypercover J) (c : F.obj.obj (op (U _⦋q + 1⦌)))
    (b : (injSES F).X₂.obj.obj (op (U _⦋q⦌)))
    (hb : cechD U (injSES F).X₂ q b = (injSES F).f.hom.app _ c)
    (hdiff : ∀ b' : (injSES F).X₂.obj.obj (op (U _⦋q⦌)), cechD U (injSES F).X₂ q b' = 0 →
      Sheaf.H.δSucc (injSES_shortExact F) q
        (cechToH hT q (injSES F).X₃ U ((injSES F).g.hom.app _ b')) = 0) :
    cechToH.{w'} hT (q + 1) F U c = Sheaf.H.δSucc (injSES_shortExact F) q
      (cechToH hT q (injSES F).X₃ U ((injSES F).g.hom.app _ b)) := by
  classical
  have h : ∃ b, cechD U (injSES F).X₂ q b = (injSES F).f.hom.app _ c := ⟨b, hb⟩
  have hcoc (b' : (injSES F).X₂.obj.obj (op (U _⦋q⦌)))
      (hb' : cechD U (injSES F).X₂ q b' = (injSES F).f.hom.app _ c) :
      cechD U (injSES F).X₃ q ((injSES F).g.hom.app _ b') = 0 := by
    rw [cechD_app, hb']
    exact Sheaf.app_g_app_f _ _
  change Sheaf.H.δSucc (injSES_shortExact F) q
      (cechToH hT q (injSES F).X₃ U ((injSES F).g.hom.app _ (dite _ _ _))) = _
  rw [dif_pos h]
  have e : h.choose = b + (h.choose - b) := by abel
  have hd : cechD U (injSES F).X₂ q (h.choose - b) = 0 := by
    rw [map_sub, h.choose_spec, hb, sub_self]
  rw [e, map_add, hA _ U hU _ _ (hcoc b hb) (by rw [cechD_app, hd, map_zero]), map_add,
    hdiff _ hd, add_zero]

variable (hT) in
lemma cechToHSucc_zero : CechToHSucc.{w'} J hT 0 := by
  intro F U hU c b hb
  refine cechToH_succ_eq_aux (cechToHAdd_zero hT) F hU c b hb fun b' hb' ↦ ?_
  obtain ⟨t, rfl⟩ := hU.exists_eq_of_cechComplex_d_zero_of_injective (injSES F).X₂ b' hb'
  change Sheaf.H.δSucc _ 0 (cechToH hT 0 _ U ((injSES F).g.hom.app _ (restr hT U _ t))) = 0
  rw [← restr_app, cechToH_zero_eq hU, ← Sheaf.H.equiv₀_symm_naturality]
  exact (Sheaf.H.exact_map_δSucc (injSES_shortExact F) 0 _).2 ⟨_, rfl⟩

lemma cechToHSucc_succ {q : ℕ} (hA : CechToHAdd.{w'} J hT (q + 1)) (hB : CechToHCob.{w'} J hT q) :
    CechToHSucc.{w'} J hT (q + 1) := by
  intro F U hU c b hb
  refine cechToH_succ_eq_aux hA F hU c b hb fun b' hb' ↦ ?_
  obtain ⟨a, rfl⟩ := hU.exists_cechComplex_d_eq_of_injective (injSES F).X₂ q b' hb'
  change Sheaf.H.δSucc _ _ (cechToH hT _ _ U ((injSES F).g.hom.app _ (cechD U _ q a))) = 0
  rw [← cechD_app, hB _ U hU, map_zero]

lemma cechToHAdd_succ {q : ℕ} (hA : CechToHAdd.{w'} J hT q) (hW : CechToHSucc.{w'} J hT q) :
    CechToHAdd.{w'} J hT (q + 1) := by
  intro F U hU c c' hc hc'
  have hι (c : F.obj.obj (op (U _⦋q + 1⦌))) (hc : cechD U F (q + 1) c = 0) :
      ∃ b, cechD U (injSES F).X₂ q b = (injSES F).f.hom.app _ c :=
    hU.exists_cechComplex_d_eq_of_injective (injSES F).X₂ q _ (by
      change cechD U _ (q + 1) _ = 0
      rw [cechD_app, hc, map_zero])
  obtain ⟨b, hb⟩ := hι c hc
  obtain ⟨b', hb'⟩ := hι c' hc'
  have hcoc (b : (injSES F).X₂.obj.obj (op (U _⦋q⦌))) (c : F.obj.obj (op (U _⦋q + 1⦌)))
      (hb : cechD U (injSES F).X₂ q b = (injSES F).f.hom.app _ c) :
      cechD U (injSES F).X₃ q ((injSES F).g.hom.app _ b) = 0 := by
    rw [cechD_app, hb]
    exact Sheaf.app_g_app_f _ _
  rw [hW F U hU c b hb, hW F U hU c' b' hb', hW F U hU (c + c') (b + b')
    (by rw [map_add, hb, hb', map_add]), map_add,
    hA _ U hU _ _ (hcoc b c hb) (hcoc b' c' hb'), map_add]

lemma cechToHCob_of {q : ℕ} (hA : CechToHAdd.{w'} J hT q) (hW : CechToHSucc.{w'} J hT q) :
    CechToHCob.{w'} J hT q := by
  intro F U hU a
  rw [hW F U hU _ ((injSES F).f.hom.app _ a) (cechD_app _ _ _ _ _), Sheaf.app_g_app_f,
    cechToH_zero_of_add hA _ hU, map_zero]

variable (hT) in
lemma cechToHAdd_and_succ (q : ℕ) : CechToHAdd.{w'} J hT q ∧ CechToHSucc.{w'} J hT q := by
  induction q with
  | zero => exact ⟨cechToHAdd_zero hT, cechToHSucc_zero hT⟩
  | succ q ih =>
    have hA := cechToHAdd_succ ih.1 ih.2
    exact ⟨hA, cechToHSucc_succ hA (cechToHCob_of ih.1 ih.2)⟩

end Comparison

end SimplicialObject

end CategoryTheory
