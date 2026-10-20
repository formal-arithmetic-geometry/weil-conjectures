/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelFactorization

/-! # Vanishing of a completed formal graph discrepancy

Source: Stacks Project, Tag 0889(1), comparison argument, with equation 0880.
(blueprint: lem-weil-pbc-formal-graph-discrepancy-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem formal_zero_of_level {X : Scheme.{u}} [IsNoetherian X]
    (J : X.IdealSheafData) (T U : CoherentFormalModule X J) (n : ℕ)
    (hU : ∀ m : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2 (U.obj.obj (op m))))
    (f : T ⟶ U) (hf : f.hom.app (op n) = 0) : f = 0 := by
  have hs := (formalModule_annihilated_power_iff J U n).mp hU
  have hhigh (m : ℕ) (hm : n ≤ m) : f.hom.app (op m) = 0 := by
    have := hs m hm
    apply (cancel_mono (U.obj.map (homOfLE hm).op)).mp
    simpa only [hf, comp_zero, zero_comp] using (f.hom.naturality (homOfLE hm).op).symm
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext a
  obtain ⟨m⟩ := a
  change f.hom.app (op m) = 0
  by_cases hm : n ≤ m
  · exact hhigh m hm
  · have hmn : m ≤ n := by omega
    have := formalTransition_epi T hmn
    apply (cancel_epi (T.obj.map (homOfLE hmn).op)).mp
    simpa only [hf, comp_zero, zero_comp] using f.hom.naturality (homOfLE hmn).op

set_option backward.isDefEq.respectTransparency false in
/-- The completed discrepancy of a finite formal comparison graph vanishes.

Source: Stacks Project, Tag 0889(1), affine comparison argument.
Proof: Evaluate the completed discrepancy at level `n`.  Naturality identifies the
component with the difference of the second projection and the first projection
followed by the prescribed component of `θ`; the two compatibility hypotheses make
this difference zero.  The target quotient is annihilated by the `(n+1)`st ideal
power, so `formal_zero_of_level` propagates the vanishing to every level.  This
statement isolates the componentwise calculation used before lifting through the
completed kernel.
(blueprint: lem-weil-pbc-formal-graph-discrepancy-zero). -/
theorem formalGraph_discrepancy_zero
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {F F' : CoherentModules X} {P : CoherentModules X}
    (p : P ⟶ F) (q : P ⟶ F')
    (g : (completion X J).obj F ⟶ (completion X J).obj P)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hp : g ≫ (completion X J).map p = 𝟙 _)
    (hq : g ≫ (completion X J).map q = θ) (n : ℕ) :
    let Q : CoherentModules X := ⟨formalModuleQuotient J (n + 1) F'.obj,
      (formalCompletionSystem_coherent J F').1 n⟩
    let t : formalModuleQuotient J (n + 1) F.obj ⟶
        formalModuleQuotient J (n + 1) F'.obj := θ.hom.app (op n)
    let d : P ⟶ Q := ObjectProperty.homMk
      (q.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj -
        p.hom ≫ formalModuleQuotientπ J (n + 1) F.obj ≫ t)
    g ≫ (completion X J).map d = 0 := by
  dsimp only
  let Q : CoherentModules X := ⟨formalModuleQuotient J (n + 1) F'.obj,
    (formalCompletionSystem_coherent J F').1 n⟩
  let t : formalModuleQuotient J (n + 1) F.obj ⟶
      formalModuleQuotient J (n + 1) F'.obj := θ.hom.app (op n)
  let d : P ⟶ Q := ObjectProperty.homMk
    (q.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj -
      p.hom ≫ formalModuleQuotientπ J (n + 1) F.obj ≫ t)
  have hU (m : ℕ) : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2
        (((completion X J).obj Q).obj.obj (op m))) := by
    let j := (Scheme.idealSheafPower J.toModulesι (n + 1)).2
    let r := formalModuleQuotientπ J (m + 1) Q.obj
    have : Epi r := inferInstanceAs (Epi (cokernel.π _))
    have hi : Scheme.idealModuleProductι j Q.obj = 0 :=
      ((formalCompletionSystem_coherent J F').2.1 n).eq_zero_of_src _
    have hz : Scheme.idealModuleProductι j (formalModuleQuotient J (m + 1) Q.obj) = 0 := by
      have h := (idealModuleProduct_quotient_comp_zero_iff j r (𝟙 _)).mpr
        (by simp only [hi, zero_comp])
      simpa only [Category.comp_id] using h
    have := idealModuleProduct_mono j (formalModuleQuotient J (m + 1) Q.obj)
    exact IsZero.of_mono_eq_zero _ hz
  apply formal_zero_of_level J ((completion X J).obj F) ((completion X J).obj Q) n hU
  have hn := congrArg (fun z ↦ z.hom.app (op n)) hp
  have hn' := congrArg (fun z ↦ z.hom.app (op n)) hq
  change g.hom.app (op n) ≫ formalModuleQuotientMap J p.hom (Nat.le_refl (n + 1)) =
    𝟙 _ at hn
  change g.hom.app (op n) ≫ formalModuleQuotientMap J q.hom (Nat.le_refl (n + 1)) =
    t at hn'
  change g.hom.app (op n) ≫ formalModuleQuotientMap J d.hom (Nat.le_refl (n + 1)) = 0
  have hd : formalModuleQuotientMap J d.hom (Nat.le_refl (n + 1)) =
      formalModuleQuotientMap J q.hom (Nat.le_refl (n + 1)) ≫
        formalModuleQuotientπ J (n + 1) Q.obj -
      formalModuleQuotientMap J p.hom (Nat.le_refl (n + 1)) ≫ t ≫
        formalModuleQuotientπ J (n + 1) Q.obj := by
    have : Epi (formalModuleQuotientπ J (n + 1) P.obj) :=
      inferInstanceAs (Epi (cokernel.π _))
    apply (cancel_epi (formalModuleQuotientπ J (n + 1) P.obj)).mp
    simp [formalModuleQuotientMap, formalModuleQuotientπ, d,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
  rw [hd, Preadditive.comp_sub, ← Category.assoc, hn', ← Category.assoc, hn]
  simp

end AlgebraicGeometry
