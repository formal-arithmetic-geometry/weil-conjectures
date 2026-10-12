module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- One half of the quantitative torsion reflection for a fixed compatible
algebraization. Source: Stacks Project, Tags 088A and 0888.
Proof: use the scalar reverse maps from Remark 0888 on affine sections,
transport them through the comparison square, and pass to inverse limits;
then use the closed-immersion equivalence and completion reflection.
(blueprint: lem-weil-pbc-devissage-second-adic-system-torsion-kernel) -/
theorem grothendieckDevissage_secondAdicSystem_torsion_kernel
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip)
    (hsquare : ∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n))
    (t : ℕ) (ht : 1 ≤ t)
    (hα : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (4 * t)).2
        (kernel (δ.hom.app (op e)))) := by sorry

end AlgebraicGeometry
