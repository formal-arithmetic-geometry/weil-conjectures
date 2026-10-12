module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.BaseChangeConventions

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Core comparison and termwise annihilation needed for the formal push-pull theorem.
Source: Stacks Project, Cohomology of Schemes, Lemma 088B and Remark 0888.
(blueprint: lem-weil-pbc-formal-systems-push-pull-core)
The construction of the comparison morphism, coherence of the pushforward, and the
uniform termwise annihilation are the affine formal-functions and completion argument
of Lemma 088B. -/
theorem exists_formalSystemsPushPull_core {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (_hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (_β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj) :
    ∃ h : RingedSpace.IsCoherent Y.toRingedSpace
        ((Scheme.Modules.pushforward f).obj F.obj),
      ∃ α : G ⟶ (completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
        ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower K.toModulesι t).2
            (kernel (α.hom.app (op n)))) ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower K.toModulesι t).2
            (cokernel (α.hom.app (op n)))) := by
  sorry

end AlgebraicGeometry
