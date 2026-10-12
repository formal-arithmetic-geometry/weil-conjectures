/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion
import Sheaf.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
import Sheaf.Paper.SchemeTheoreticSupport

/-!
# Short exact sequences for integral ideal patching

Source: Stacks Project, Cohomology of Schemes, Lemma 01YL.
(blueprint: lem-weil-pbc-coherent-ideal-patching-exact-sequence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The geometric part of generic-point patching, without extension closure or descent
from positive finite sums. Each ideal pushforward has a positive finite sum containing
an object isomorphic to a module already satisfying P, with a small-support quotient.

Source: Stacks Project, Cohomology of Schemes, Lemma 01YL, third proof paragraph and
its final intersection argument.
(blueprint: lem-weil-pbc-coherent-ideal-patching-exact-sequence)

Proof: The generic point of Z maps to ξ because both have closure i(Z) and X is sober.
Use the generic-point ideal-inclusion lemma on G to obtain a nonzero ideal A and a
positive rank r with an embedding (i_* A)^r into G, generically an isomorphism.
For a nonzero I, put B = I ∩ A. On an integral scheme B is nonzero: the product of
nonzero local sections of I and A is nonzero and belongs to B. The inclusion of B
into A and I is an isomorphism at the generic point. Thus (i_* B)^r embeds into G
and into (i_* I)^r, with the same generic stalk in both. Let Q₀ be its cokernel in G.
It is coherent, supported on i(Z), and has zero ξ-stalk. Its annihilator J is a
quasi-coherent ideal whose stalk at ξ is the unit ideal: Q₀ vanishes on the open
complement of its closed support. Since J kills Q₀, JG factors through (i_* B)^r.
Apply the hypothesis on G to J to get a coherent subobject G' of JG, generically
full and satisfying P. Pull it back through the embedding (i_* B)^r into G, and
then include it into (i_* I)^r. The resulting coherent submodule H is isomorphic
to G'. Its cokernel is coherent, supported on i(Z), and has zero ξ-stalk, by exactness
of stalks. Take the short exact sequence H → (i_* I)^r → coker, with its chosen middle
object literally the specified biproduct. All ideal modules are coherent on the
locally Noetherian source, and finite closed pushforward preserves coherence.
For I = 0 take r = 1, the zero submodule and zero quotient of its zero pushforward;
take G' = 0 and use P(0). This includes the degenerate case without using isomorphism
invariance of P. No arbitrary witness is used to define an object: the sequence is
asserted as a theorem and used only within the proof of the target theorem. -/
theorem coherent_ideal_patching_exact_sequence
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : P (0 : X.Modules))
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (hG :
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        ({x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base) ∧
        (∀ g : X.presheaf.stalk ξ, ∀ m : (RingedSpace.moduleStalkFunctor
          X.toRingedSpace ξ).obj G, g ∈ IsLocalRing.maximalIdeal _ → g • m = 0) ∧
        ∀ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
          [Mono ι] [J.IsQuasicoherent],
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom →
          ∃ G' : Subobject G,
            RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
            (∃ h : (G' : X.Modules) ⟶ idealModuleProduct ι G,
              G'.arrow = h ≫ idealModuleProductι ι G) ∧
            Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
              G'.arrow).hom ∧ P (G' : X.Modules)) :
    ∀ I : Z.IdealSheafData,
      ∃ (r : ℕ), 1 ≤ r ∧ ∃ (S : ShortComplex X.Modules),
        S.X₂ = @biproduct (Fin r) X.Modules _ _
          (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
          (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules)) ∧
        S.ShortExact ∧
        RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules) ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₁ ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₂ ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₃ ∧
        ∃ (G' : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G' ∧
          Nonempty (S.X₁ ≅ G') ∧ P G' ∧
          {x : X | ¬ Subsingleton (S.X₃.presheaf.stalk x)} ⊆ Set.range i.base ∧
          Subsingleton (S.X₃.presheaf.stalk ξ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
