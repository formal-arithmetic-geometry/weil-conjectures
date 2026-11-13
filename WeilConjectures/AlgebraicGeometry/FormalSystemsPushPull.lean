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

Source: Stacks Project, Cohomology of Schemes, Lemma 088B and Remark 0888.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A formal system whose tensor pullback algebraizes to F maps to the completion of f_*F,
with formal kernel and cokernel uniformly annihilated by a positive power of K.
The hypothesis on beta is written in the ambient inverse-system category: the inclusion
of coherent formal systems is fully faithful, so this is the same isomorphism.
Kernel forks and cokernel coforks with their universal properties specify the kernel and
cokernel in Coh(Y,J), without choosing the Abelian instance supplied by
`coherentFormalModule_abelian`. The index `op n` is positive level n+1.

Source: Stacks, Lemma 088B and Remark 0888.

Proof (the eleven steps of the node):
1. Properness over Noetherian Y makes X Noetherian.
   The ideal is J.comap f. Ideal powers and quotients commute with tensor pullback. All hypotheses restrict to opens.
2. Proper coherent pushforward is coherent, so its completion exists.
3. Compose the adjunction unit with f_*beta_n to get gamma_n. The quotient projection
   F -> F/I^nF gives kappa_n: f_*F/J^n(f_*F) -> f_*(F/I^nF). These maps commute with
   transitions and restriction.
4. On an affine open, the theorem on formal functions identifies the limit of kappa_n
   with an isomorphism from the completion of Gamma(X,F). Compose its inverse with lim gamma_n.
   The affine equivalence yields the unique alpha with kappa_n alpha_n = gamma_n.
5. Uniqueness makes these maps agree on smaller affine opens, hence glue. Choose a finite
   affine cover; annihilation on it gives a uniform exponent.
6. Base change to the J-adic completion of the affine base. This is flat and Noetherian,
   and the quotients by powers of J agree.
7. Flat base change identifies the section modules and comparison maps. Annihilation can therefore be checked after completion.
8. Over the complete base, algebraize G using the affine equivalence. Full faithfulness
   algebraizes beta to an isomorphism b: f*G -> F.
9. Naturality of the unit shows that alpha is the completion of f_*b composed with the
   adjunction map c: G -> f_*f*G, by the uniqueness in steps 4--5.
10. Over V the map c is the unit of an equivalence and hence an isomorphism. Its coherent
    kernel and cokernel are supported on V(K), hence killed by K^s for some s >= 1.
11. Reduction modulo J^n has kernel and cokernel killed by K^(2s), uniformly in n.
    Remark 0888 converts this into annihilation of the formal kernel and cokernel. Descend to each affine base and
    take the maximum exponent on the finite cover, giving the asserted t >= 1.
-/
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
