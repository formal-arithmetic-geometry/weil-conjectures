module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.CoherentSheafHom
import Sheaf.AlgebraicGeometry.CompletionInternalHom
import Sheaf.AlgebraicGeometry.FormalFunctionsCompleteBase
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry
/-- Auxiliary surjectivity part of formal completion full faithfulness.
Source: Stacks Project, Cohomology of Schemes, Lemma 0883 (lemma-fully-faithful).
Proof: Let H be the internal Hom sheaf. Given a morphism between completed modules,
invert the completion-internal-Hom bijection to obtain its compatible reductions and then
invert formal functions to obtain a global section of H. The corresponding coherent-module
morphism completes to the given morphism.
(blueprint: lem-weil-pbc-formal-completion-map-surjective-proper). -/
theorem formalCompletion_map_surjective_of_proper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (G F : CoherentModules X) :
    Function.Surjective
      (fun v : G ⟶ F ↦
        (@completion X (isNoetherian_of_locallyOfFiniteType f)
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)).map v) := by
  sorry
end AlgebraicGeometry
