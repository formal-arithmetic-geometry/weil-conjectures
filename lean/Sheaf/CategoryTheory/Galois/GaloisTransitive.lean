/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import Sheaf.CategoryTheory.Galois.StacksGaloisAxioms
import Sheaf.CategoryTheory.Galois.StacksMonoComplement
import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# Transitivity of the automorphism action

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN3
(blueprint: lem-galois-transitive).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- The automorphism group of a fiber functor acts transitively on the fiber of a
connected object (Stacks Project, Lemma 0BN3).

(blueprint: lem-galois-transitive)

The proof constructs a cofiltered system of Galois objects and identifies its
automorphism inverse limit with `Aut F`; the resulting action is transitive on
each connected fiber and hence on the given fiber.

Proof steps (Stacks Project, Lemma 0BN3):
1. Index representatives of Galois objects by a directed system, normalizing
   transition maps using the chosen fiber points and the Galois axioms
   (`def-galois-category`, `lem-galois-axioms`, `lem-galois-object-exists`).
2. Identify `F` with the colimit of the representables of these objects, using
   the same axioms for injectivity and surjectivity.
3. Form the inverse system of finite automorphism groups. Its surjective
   transition maps give a transitive action of the inverse limit, hence of
   `Aut F`, on every Galois-object fiber (`lem-galois-inverse-limit-surjective`).
4. Cover the connected object by a Galois object and descend transitivity
   along the fiber-surjective cover, using naturality of the automorphism.
-/
theorem aut_fiber_transitive {C : Type u} [Category.{v} C]
    {F : C ⥤ Type w} (hCF : IsStacksGaloisCategory F) (X : C)
    [IsConnected X] : ∀ x y : F.obj X, ∃ g : Aut F, g.hom.app X x = y := by
  let := hCF.hasFiniteLimits
  let := hCF.hasFiniteColimits
  -- Bundle finite fibers, then derive the SGA1 axioms from the Stacks axioms.
  let F' : C ⥤ FintypeCat.{w} := ObjectProperty.lift Finite F hCF.finite_obj
  let : Limits.PreservesFiniteLimits (F' ⋙ FintypeCat.incl) := hCF.preservesFiniteLimits
  let : Limits.PreservesFiniteColimits (F' ⋙ FintypeCat.incl) := hCF.preservesFiniteColimits
  let : (F' ⋙ FintypeCat.incl).ReflectsIsomorphisms := hCF.reflectsIsomorphisms
  let : Limits.PreservesFiniteLimits F' :=
    Limits.preservesFiniteLimits_of_reflects_of_preserves F' FintypeCat.incl
  let : Limits.PreservesFiniteColimits F' :=
    Limits.preservesFiniteColimits_of_reflects_of_preserves F' FintypeCat.incl
  let : F'.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp F' FintypeCat.incl
  let : PreGaloisCategory C := {
    monoInducesIsoOnDirectSummand := fun i ↦ stacksGalois_mono_complement F hCF i
    hasQuotientsByFiniteGroups := fun G _ _ ↦ by
      obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
      let := hgroup
      let := hfinite
      let := Fintype.ofFinite G'
      exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm }
  let : F'.PreservesEpimorphisms := {
    preserves := fun f _ ↦ by
      apply ConcreteCategory.epi_of_surjective
      exact ((stacksGaloisCategory_axioms.{0, 0, w, v, u} F hCF).2.1 f).2.mp
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
  -- Mathlib implements the prorepresentability argument described above.
  intro x y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F')
    (show F'.obj X from x) (show F'.obj X from y)
  exact ⟨Functor.isoWhiskerRight g FintypeCat.incl, hg⟩

end CategoryTheory
