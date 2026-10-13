module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.Modules.ExteriorTensorQuotient
import Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option linter.unusedVariables false in
/-- A chosen family of local wedge maps glues to a global morphism.
Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
Proof: Form the epimorphism from tensors of wedges of lifts to tensors of quotient
wedges. The concatenated wedge map kills its kernel, so `Abelian.epiDesc` gives a
morphism on the quotient. Evaluate its factorization on pure wedges to obtain the
displayed formula. This construction does not need the supplied family.
(blueprint: new-wedge-glue-family)
-/
theorem determinant_wedgeMorphism_glue_family {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (φU : ∀ U : X.Opens, exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂)
    (hformula : ∀ (U : X.Opens)
      (a : Fin r₁ → S.X₁.val.obj (op U))
      (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
      (∀ i, S.g.val.app (op U) (c i) = b i) →
      (φU U).val.app (op U)
        (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₃ r₃ U b)) =
        exteriorSheafSection S.X₂ r₂ U
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φ.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  clear φU hformula
  have : Epi S.g := hS.epi_g
  obtain ⟨q, hqepi, hq⟩ := exteriorTensor_quotient_exists S.X₁ S.X₂ S.X₃ S.g r₁ r₃
  have : Epi q := hqepi
  obtain ⟨w, hwzero, hw⟩ := determinant_liftWedge_kernel_exists S hS r₁ r₂ r₃ hr q hq
  let φ := Abelian.epiDesc q w hwzero
  have hcomp : q ≫ φ = w := Abelian.comp_epiDesc q w hwzero
  refine ⟨φ, ?_⟩
  intro U a b c hc
  have hb : (fun i ↦ S.g.val.app (op U) (c i)) = b := funext hc
  rw [← hb, ← hq U a c]
  have he := congrArg (fun k ↦ k.val.app (op U)
    (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
      (exteriorSheafSection S.X₂ r₃ U c))) hcomp
  exact he.trans (hw U a c)

end AlgebraicGeometry.Scheme.Modules
