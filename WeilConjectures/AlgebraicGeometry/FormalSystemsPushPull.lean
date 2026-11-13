/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.FormalSystemsPushPullCore
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Comparison of a formal system with a proper pushforward

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A formal system whose tensor pullback algebraizes to F maps to the completion of f_*F,
with formal kernel and cokernel uniformly annihilated by a positive power of K.
The hypothesis on beta is written in the ambient inverse-system category. The kernel and
cokernel in Coh(Y,J) are specified by kernel forks and cokernel coforks. The index `op n`
is positive level n+1 (Stacks, Lemma 088B and Remark 0888). -/
theorem exists_formalSystemsPushPull {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (_hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (_β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj) :
    ∃ h : RingedSpace.IsCoherent Y.toRingedSpace ((Scheme.Modules.pushforward f).obj F.obj),
      ∃ α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
        ∃ (t : ℕ) (k : KernelFork α) (c : CokernelCofork α),
          1 ≤ t ∧ Nonempty (IsLimit k) ∧ Nonempty (IsColimit c) ∧
          (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower K.toModulesι t).2 (k.pt.obj.obj (op n)))) ∧
          (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower K.toModulesι t).2 (c.pt.obj.obj (op n)))) := by
  obtain ⟨h, α, t, ht, hn⟩ :=
    exists_formalSystemsPushPull_core J K f _hV G F _β
  refine ⟨h, α, ?_⟩
  let H := (completion Y J).obj
    ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩
  have htf := coherentFormalModule_annihilated_iff Y J K G H α
  have hfirst : (∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) := ⟨t, ht, hn⟩
  have h04 := (List.TFAE.out htf 1 4).mp hfirst
  obtain ⟨k, c, hk, hc, t', ht', ha⟩ := h04
  refine ⟨t', k, c, ht', hk, hc, ?_, ?_⟩
  · intro n
    exact (ha n).1
  · intro n
    exact (ha n).2

end AlgebraicGeometry
