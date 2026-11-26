/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.IsStrictHenselization

/-!
# Strict henselization presentations in a universe containing the base ring

The diagram of pointed étale algebras used to present a strict henselization, with
independent base-ring and algebra universes. The algebra universe is at least the base-ring
universe.

## References

* [Stacks, Tag 04GW]
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- The forgetful diagram of pointed etale algebras in any universe containing the base. -/
def strictHenselizationPointedDiagramIn (A : Type u) (K : Type (max u v))
    [CommRing A] [CommRing K] [Algebra A K] :
    (ObjectProperty.FullSubcategory
      (fun S : Over (CommAlgCat.of A K) ↦ Etale A S.left)) ⥤
        CommAlgCat.{max u v} A :=
  ObjectProperty.ι (fun S : Over (CommAlgCat.of A K) ↦ Etale A S.left) ⋙
    Over.forget (CommAlgCat.of A K)

end Algebra
