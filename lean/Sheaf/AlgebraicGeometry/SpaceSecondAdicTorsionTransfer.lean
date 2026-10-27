module

public import Sheaf.AlgebraicGeometry.SpaceSupportedKilledAdicCompletion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Functor.Currying
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal

/-! # Uniform torsion transfer through a double adic quotient diagram

Source: Stacks Project, spaces-more-morphisms.tex, Tag 08BC, lemma-existence-tricky,
the two omitted torsion estimates, and Tag 08BA
(blueprint: lem-sfb-space-second-adic-torsion-transfer).

Indices `op e` and `op n` mean the positive levels e+1 and n+1. The quotient interchange
is characterized by its composites with the two quotient projections from H.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A uniform K^t bound for the ordinary component errors of a transfers to a K^(4t)
bound for the supplied second-adic map d, through the supplied double-diagram comparison.
Source: Stacks Project, spaces-more-morphisms.tex, Tag 08BC, lemma-existence-tricky,
the K^(2t) and K^(4t) estimates; Tag 08BA
(blueprint: lem-sfb-space-second-adic-torsion-transfer).

Proof:
1. On each affine etale chart, apply clause (c) of
lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal to a_n, with annihilating ideal K
and quotient ideal K^e. By lem-sfb-space-qcoh-affine-chart-calculus the ordinary sheaf
kernel and cokernel of a_n modulo K^e are killed by K^(2t), uniformly in e and n.
2. The compatibility square and its two isomorphisms identify these errors with the
ordinary errors of d_e modulo J^n, preserving the K-action.
3. Fix e. Put F=N_e, G=H/K^e H, P=ker d_e and Q=coker d_e. The adic transition identities
and nilpotence of K on F give Supp F=Supp N_1. Thus F and G have proper support.
The chart calculus, lem-sfb-space-noetherian-coherent-support,
lem-sfb-space-noetherian-coherent-acc, lem-sfb-space-proper-support-closed-operations,
and lem-sfb-space-module-proper-carrier-support give coherence and proper closed
carriers for P, Q, B=K^(2t)P, and D=K^(2t)Q. All are killed by K^e.
4. For every n, step 2 puts the image of B in J^n F. Thus the J-completion of the
inclusion B into F is zero, by the quotient projections defining completion.
5. On affine charts coker(d_e mod J^n)=Q/J^n Q. Step 2 therefore puts D in J^n Q,
so the J-completion of the inclusion D into Q is also zero.
6. The completion equivalence on the closed thickening, identified with the ambient
full subcategories as in lem-sfb-space-closed-adic-dictionary and Stacks 08BC, is faithful.
It forces the two inclusions to be zero, hence B=D=0. Thus K^(2t) already kills P,Q.
Finally K^(4t) is contained in K^(2t), giving the asserted bound, for every e.
No step identifies termwise kernels with kernels in the adic category. -/
theorem secondAdic_torsion_transfer
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (b : Spec (.of A) ⟶ S)
    (f : X ⟶ schemeSpace (Over.mk b)) (hsep : MapIsSeparated f) (hft : MapIsFiniteType f)
    (J K : QuasiCoherentIdeal X)
    (hcompletion : ∀ q : ℕ, 1 ≤ q → SupportedKilledAdicCompletionEquivalence f J K q)
    (M : CoherentAdicSystem X J hln hqc hqs) (N : CoherentAdicSystem X K hln hqc hqs)
    (H : X.Modules) (hHqc : H.IsQuasicoherent)
    (hHcoh : ∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
      ((X.schemeRestriction T).obj H))
    (hMproper : CoherentAdicHasProperSupportOver f M.obj)
    (hNproper : CoherentAdicHasProperSupportOver f N.obj)
    (hHproper : CoherentAdicHasProperSupportOver f ((Functor.const ℕᵒᵖ).obj H))
    (a : M.obj ⟶ (coherentAdicCompletionDiagram J).obj H)
    (d : N.obj ⟶ (coherentAdicCompletionDiagram K).obj H)
    (σ : (N.obj ⋙ coherentAdicCompletionDiagram J) ≅
      (M.obj ⋙ coherentAdicCompletionDiagram K).flip)
    (θ : ((coherentAdicCompletionDiagram K).obj H ⋙ coherentAdicCompletionDiagram J) ≅
      ((coherentAdicCompletionDiagram J).obj H ⋙ coherentAdicCompletionDiagram K).flip)
    (hθ : ∀ e n : ℕ,
      (adicQuotientModel K).projection H e ≫
        (adicQuotientModel J).projection
          (((coherentAdicCompletionDiagram K).obj H).obj (op e)) n ≫
        (θ.hom.app (op e)).app (op n) =
      (adicQuotientModel J).projection H n ≫
        (adicQuotientModel K).projection
          (((coherentAdicCompletionDiagram J).obj H).obj (op n)) e)
    (hcompat : ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
        ((coherentAdicCompletionDiagram K).map (a.app (op n))).app (op e) =
      ((coherentAdicCompletionDiagram J).map (d.app (op e))).app (op n) ≫
        (θ.hom.app (op e)).app (op n))
    (t : ℕ) (ht : 1 ≤ t)
    (ha : ∀ n : ℕ,
      (∀ k : KernelFork (a.app (op n)), IsLimit k → AdicPowerKills K t k.pt) ∧
      (∀ c : CokernelCofork (a.app (op n)), IsColimit c → AdicPowerKills K t c.pt)) :
    ∀ e : ℕ,
      (∀ k : KernelFork (d.app (op e)), IsLimit k → AdicPowerKills K (4 * t) k.pt) ∧
      (∀ c : CokernelCofork (d.app (op e)), IsColimit c → AdicPowerKills K (4 * t) c.pt) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
