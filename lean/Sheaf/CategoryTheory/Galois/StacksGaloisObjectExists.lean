/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.Galois.StacksGaloisAxioms
import Sheaf.CategoryTheory.Galois.StacksMonoComplement
import Mathlib.CategoryTheory.Galois.Decomposition

/-!
# Galois objects above connected objects

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN2
(blueprint: lem-galois-object-exists).
-/

@[expose] public section

universe w v u

open CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- (blueprint: lem-galois-object-exists) Stacks, Lemma 0BN2. In a Galois category,
every connected object receives a morphism from a Galois object.

For the proof, let `n` be the finite, nonzero cardinality of `F.obj X`. Decompose
the finite product `X^n` into connected components and choose one whose fibre
contains an enumeration of `F.obj X` with distinct entries. Every tuple in that
component has distinct entries: a repeated pair would make the component the
image of a connected component of `X^(n-1)` under a diagonal map. The resulting
map between connected objects is epi and surjective on fibres by
`stacksGaloisCategory_axioms`, contradicting the chosen enumeration. The
stabilizer of the component in the symmetric group then acts transitively on
its fibre. Its elements induce automorphisms of the component, so the
transitivity criterion of `stacksGaloisCategory_axioms` makes it a Galois
object. Compose the component inclusion with a product projection to obtain
its morphism to `X`. -/
theorem exists_stacksGaloisObject_hom_of_isConnected
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
    (hG : IsStacksGaloisCategory F) (X : C) [IsConnected X] :
    ∃ (Z : C) (_ : Z ⟶ X), IsStacksGaloisObject F Z := by
  let := hG.hasFiniteLimits
  let := hG.hasFiniteColimits
  let := hG.preservesFiniteLimits
  let := hG.preservesFiniteColimits
  let := hG.reflectsIsomorphisms
  let F' : C ⥤ FintypeCat.{w} := ObjectProperty.lift _ F hG.finite_obj
  let : Limits.PreservesFiniteLimits (F' ⋙ FintypeCat.incl) := hG.preservesFiniteLimits
  let : Limits.PreservesFiniteColimits (F' ⋙ FintypeCat.incl) := hG.preservesFiniteColimits
  let : (F' ⋙ FintypeCat.incl).ReflectsIsomorphisms := hG.reflectsIsomorphisms
  let : Limits.PreservesFiniteLimits F' :=
    Limits.preservesFiniteLimits_of_reflects_of_preserves F' FintypeCat.incl
  let : Limits.PreservesFiniteColimits F' :=
    Limits.preservesFiniteColimits_of_reflects_of_preserves F' FintypeCat.incl
  let : F'.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp F' FintypeCat.incl
  let : PreGaloisCategory C := {
    monoInducesIsoOnDirectSummand := fun i ↦ stacksGalois_mono_complement F hG i
    hasQuotientsByFiniteGroups := fun G _ _ ↦ by
      obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
      let := hgroup
      let := hfinite
      let := Fintype.ofFinite G'
      exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm }
  let : F'.PreservesEpimorphisms := {
    preserves := fun f _ ↦ by
      apply ConcreteCategory.epi_of_surjective
      exact ((stacksGaloisCategory_axioms.{0, 0, w, v, u} F hG).2.1 f).2.mp
        inferInstance }
  let : FiberFunctor F' := {
    preservesQuotientsByFiniteGroups := fun G _ _ ↦ by
      obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
      let := hgroup
      let := hfinite
      let := Fintype.ofFinite G'
      exact Limits.preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F' }
  let : GaloisCategory C := {
    hasFiberFunctor := ⟨F' ⋙ FintypeCat.uSwitch.{w, v}, ⟨inferInstance⟩⟩ }
  obtain ⟨Z, f, hZ⟩ := exists_hom_from_galois_of_connected F' X
  let := hZ
  obtain ⟨z⟩ := nonempty_fiber_of_isConnected F' Z
  refine ⟨Z, f, inferInstance, ?_⟩
  exact Nat.card_eq_of_bijective _ (evaluation_aut_bijective_of_isGalois F' Z z)

end CategoryTheory
