/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardSetStalkAux
import WeilConjectures.AlgebraicGeometry.FinitePushforwardSetStalkFiberFinite

/-!
# Stalks of finite direct images of étale sheaves of sets

## References

* Stacks Project, Proposition 59.55.2, Tag 03QP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a finite morphism, the geometric lifts are finite and restriction of germs
identifies the stalk of the direct image of a set sheaf with the product of its stalks.
(Stacks, Tag 03QP) -/
theorem finite_pushforward_set_stalk_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (H : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y} ∧
      Function.Bijective
        (fun a : (Scheme.pointSmallEtale y).sheafFiber.obj
            ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
              Y.smallEtaleTopology X.smallEtaleTopology).obj H) ↦
          fun t : {x : Spec (.of Ω) ⟶ X // x ≫ f = y} ↦
            (colimit.pre
              ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙ H.obj)
              (Etale.baseChangeNbhd f y t).op) a) := by
  let hfin := finite_pushforward_set_stalk_fiber_finite f y
  exact ⟨hfin, finite_pushforward_set_stalk_map_bijective_of_finite f H y hfin⟩

end AlgebraicGeometry
