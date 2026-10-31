/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Galois.StacksGaloisCategory
import WeilConjectures.CategoryTheory.Galois.StacksGaloisAxioms
import WeilConjectures.CategoryTheory.Galois.StacksMonoComplement
import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# Transitivity of natural automorphisms on a connected fibre

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN3 (`lemma-tame`);
Weil conjectures blueprint, `sec-curve-estimates`, lemma `lem-galois-transitive`
(blueprint: lem-galois-transitive).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- Source: Stacks Project, Lemma 0BN3 (`lemma-tame`)
(blueprint: lem-galois-transitive). For a Galois category in the Stacks sense,
natural automorphisms of the fibre functor act transitively on the fibre of a connected object.

Proof (the DAG's four-step Mathlib comparison route):
1. Bundle the finite values of `F` into a functor `F'` to `FintypeCat` using
`ObjectProperty.lift Finite F hCF.finite_obj`. The composite with `FintypeCat.incl` is `F`.
Reflect the preservation of finite limits and colimits and reflection of isomorphisms
along this fully faithful inclusion.
2. Construct `PreGaloisCategory C`: finite limits give a terminal object and pullbacks;
finite colimits give finite coproducts and finite-group quotients. Transfer finite-group
quotients across a `SingleObj` equivalence to handle group universes. The summand axiom is
`stacksGalois_mono_complement` (blueprint: lem-galois-stacks-mono-complement).
3. Construct `FiberFunctor F'`. Exactness gives preservation of the required limits and
colimits, and clause (2) of `stacksGaloisCategory_axioms` (blueprint: lem-galois-axioms)
gives preservation of epimorphisms via surjectivity. Reflection of isomorphisms is inherited.
Compose with `FintypeCat.uSwitch` to obtain a fibre functor in the hom universe, supplying
`GaloisCategory C`.
4. Apply `FiberFunctor.isPretransitive_of_isConnected` to `F'` and `X`. For `x,y`, choose
its natural automorphism and whisker it with `FintypeCat.incl`. This is an automorphism
of `F` whose component at `X` sends `x` to `y`. -/
theorem aut_fiber_transitive {C : Type u} [Category.{v} C] {F : C ⥤ Type w}
    (hCF : IsStacksGaloisCategory F) (X : C) [IsConnected X] :
    ∀ x y : F.obj X, ∃ g : Aut F, g.hom.app X x = y := by
  let F₀ : C ⥤ FintypeCat.{w} := ObjectProperty.lift Finite F hCF.finite_obj
  let : Limits.HasFiniteLimits C := hCF.hasFiniteLimits
  let : Limits.HasFiniteColimits C := hCF.hasFiniteColimits
  let : PreGaloisCategory C := {
    hasTerminal := inferInstance
    hasPullbacks := inferInstance
    hasFiniteCoproducts := inferInstance
    hasQuotientsByFiniteGroups := by
      intro G _ _
      obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
      exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm
    monoInducesIsoOnDirectSummand := by
      intro A B i _
      exact stacksGalois_mono_complement F hCF i
  }
  let : PreservesFiniteLimits (F₀ ⋙ FintypeCat.incl) := by
    change PreservesFiniteLimits F
    exact hCF.preservesFiniteLimits
  let : PreservesFiniteColimits (F₀ ⋙ FintypeCat.incl) := by
    change PreservesFiniteColimits F
    exact hCF.preservesFiniteColimits
  let : (F₀ ⋙ FintypeCat.incl).ReflectsIsomorphisms := hCF.reflectsIsomorphisms
  let : PreservesFiniteLimits F₀ :=
    preservesFiniteLimits_of_reflects_of_preserves F₀ FintypeCat.incl
  let : PreservesFiniteColimits F₀ :=
    preservesFiniteColimits_of_reflects_of_preserves F₀ FintypeCat.incl
  let : F₀.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp F₀ FintypeCat.incl
  let : F₀.PreservesEpimorphisms := ⟨fun f _ ↦ by
    apply ConcreteCategory.epi_of_surjective
    exact ((stacksGaloisCategory_axioms.{0, 0} F hCF).2.1 f).2.mp inferInstance⟩
  let : FiberFunctor F₀ := {
    preservesTerminalObjects := inferInstance
    preservesPullbacks := inferInstance
    preservesFiniteCoproducts := inferInstance
    preservesEpis := inferInstance
    preservesQuotientsByFiniteGroups := by
      intro G _ _
      obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
      let : PreservesColimitsOfShape (SingleObj G')
          (F₀ ⋙ FintypeCat.incl) := by
        exact hCF.preservesFiniteColimits.preservesFiniteColimits (SingleObj G')
      let : PreservesColimitsOfShape (SingleObj G') F₀ := by
        apply preservesColimitsOfShape_of_reflects_of_preserves F₀ FintypeCat.incl
      exact Limits.preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F₀
    reflectsIsos := inferInstance
  }
  let F' : C ⥤ FintypeCat.{v} := F₀ ⋙ FintypeCat.uSwitch
  let : FiberFunctor F' := FiberFunctor.comp_right _
  let : GaloisCategory C := {
    toPreGaloisCategory := inferInstance
    hasFiberFunctor := ⟨F', ⟨inferInstance⟩⟩
  }
  intro x y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F₀)
    (show F₀.obj X from x) (show F₀.obj X from y)
  exact ⟨Functor.isoWhiskerRight g FintypeCat.incl, hg⟩

end CategoryTheory
