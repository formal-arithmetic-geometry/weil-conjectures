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
/-- Auxiliary injectivity part of formal completion full faithfulness.
Source: Stacks Project, Cohomology of Schemes, Lemma 0883 (lemma-fully-faithful).
Proof: Let H be the internal Hom sheaf. Formal functions gives a bijection from global
sections of H to the inverse limit of the global sections of H modulo powers of the ideal
sheaf. The completion-internal-Hom comparison gives a bijection from that inverse limit to
morphisms between completed modules. Their composite is the completion map, so equality
after completion implies equality before completion.
(blueprint: lem-weil-pbc-formal-completion-map-injective-proper). -/
theorem formalCompletion_map_injective_of_proper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (G F : CoherentModules X) :
    Function.Injective
      (fun v : G ⟶ F ↦
        (@completion X (isNoetherian_of_locallyOfFiniteType f)
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)).map v) := by
  sorry
end AlgebraicGeometry
