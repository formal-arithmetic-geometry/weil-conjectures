/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Unramified.Finite

/-!
# Module flatness over an etale base local ring

Source: Stacks Project, Flat Modules, Tag 05BA, lemma-etale-flat-up-down-local-ring
(blueprint: lem-trf-etale-local-ring-flatness).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- For an etale morphism, flatness of an arbitrary module over the target stalk is
 equivalent to flatness over the source stalk.  Source: Stacks Project, Flat Modules,
 Tag 05BA (blueprint: lem-trf-etale-local-ring-flatness).

The proof uses the diagonal open immersion and the relative flat base-change statement
[lem-pc-pullback-stalk-relative-flat-extension], then identifies the resulting tensor
module with the original module; the converse uses that etale morphisms are flat and
transitivity of flatness [lem-pc-module-flat-transitive]. -/
theorem etale_local_ring_flatness {T S : Scheme.{u}} (e : T ⟶ S) [Etale e]
    (t : T) (M : Type v) [AddCommMonoid M] [Module (T.presheaf.stalk t) M] :
    @Module.Flat (S.presheaf.stalk (e t)) M _ _
        (Module.compHom M (e.stalkMap t).hom) ↔ Module.Flat (T.presheaf.stalk t) M := by
  let R := S.presheaf.stalk (e t)
  let A := T.presheaf.stalk t
  let : Algebra R A := (e.stalkMap t).hom.toAlgebra
  let : Module R M := Module.compHom M (e.stalkMap t).hom
  let : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
  have : Algebra.EssFiniteType R A := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap e t
  have : Algebra.FormallyUnramified R A := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap e t
  have : Module.Flat R A := by
    rw [← RingHom.flat_algebraMap_iff, RingHom.algebraMap_toAlgebra]
    exact Flat.stalkMap e t
  constructor
  · intro h
    let : Module.Flat R M := h
    exact Algebra.FormallyUnramified.flat_of_restrictScalars R A M
  · intro h
    let : Module.Flat A M := h
    exact Module.Flat.trans R A M

end AlgebraicGeometry
