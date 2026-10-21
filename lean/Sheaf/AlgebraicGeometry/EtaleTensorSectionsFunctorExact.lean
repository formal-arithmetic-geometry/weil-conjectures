/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact
public import Mathlib.CategoryTheory.Abelian.Exact
import Sheaf.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Exactness of sheafified tensor sections

Source: Stacks Project, Tag 03FH(1), and Tag 070S.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensor_section_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {F G : Y.Modules} (φ : F ⟶ G) [Mono φ] :
    Mono (((tensorPullback f).map φ).app ⊤) := by
  let : PreservesFiniteLimits (tensorPullback f) :=
    (AlgebraicGeometry.flat_module_pullback_exact_pushforward_injective f).1.1
  have : Mono ((tensorPullback f).map φ) := inferInstance
  have : Mono ((toPresheaf X).map ((tensorPullback f).map φ)) := inferInstance
  change Mono (((toPresheaf X).map ((tensorPullback f).map φ)).app (op ⊤))
  infer_instance

/-- Sheafified tensor sections preserve finite limits and finite colimits on all
modules. No quasi-coherence hypothesis is needed for this exact functor.

Source: Stacks Project, Tag 03FH(1), and Tag 070S.
(blueprint: lem-weil-pbc-etale-tensor-sections-functor-exact)

Proof: A monomorphism of modules remains monic after pullback to each étale
object, since étale maps are flat. Taking sections preserves monomorphisms,
so the tensor-section presheaf functor preserves them objectwise. Coefficient
lift and sheafification preserve monomorphisms, hence so does their composite.
The sheafified construction already preserves cokernels: sections of a quotient
lift locally for the Zariski topology, hence for the étale topology. An additive
functor between abelian categories preserving monomorphisms and cokernels
preserves exactness and therefore finite limits and finite colimits. Zero
modules, empty schemes and arbitrary coefficient modules satisfy the same
objectwise argument. -/
theorem etaleTensorSectionsFunctor_exact (X : Scheme.{u}) :
    PreservesFiniteLimits (etaleTensorSectionsFunctor X) ∧
      PreservesFiniteColimits (etaleTensorSectionsFunctor X) := by
  let P := etaleTensorSectionsPresheafFunctor X
  let : P.PreservesMonomorphisms := ⟨fun {F G} φ _ ↦ by
    have h (U : X.Etaleᵒᵖ) : Mono ((P.map φ).app U) :=
      tensor_section_mono U.unop.hom φ
    let := h
    exact NatTrans.mono_of_mono_app _⟩
  let T := etaleTensorSectionsFunctor X
  let : T.Additive := by
    dsimp [T, etaleTensorSectionsFunctor]
    infer_instance
  let : T.PreservesMonomorphisms := by
    dsimp only [T, etaleTensorSectionsFunctor]
    infer_instance
  let := preservesCokernels_etaleTensorSectionsFunctor X
  let : T.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels T
  exact ⟨Functor.preservesFiniteLimits_of_preservesHomology T,
    Functor.preservesFiniteColimits_of_preservesHomology T⟩

end
end AlgebraicGeometry.Scheme.Modules
