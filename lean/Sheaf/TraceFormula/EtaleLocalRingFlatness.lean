/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.PullbackStalkRelativeFlatExtension
import Sheaf.AlgebraicGeometry.UnramifiedMorphism

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
  sorry

end AlgebraicGeometry
