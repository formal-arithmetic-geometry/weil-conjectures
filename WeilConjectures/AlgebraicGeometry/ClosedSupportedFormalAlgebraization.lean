/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent

/-! # Transporting algebraization along a closed immersion

## References

* Stacks Project, Tags 088E and 087T
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Essential surjectivity on a closed subscheme algebraizes supported formal modules
(Stacks, Tags 088E, 087T and 088A). -/
theorem closedSupported_formal_algebraization
    {X Z : Scheme.{u}} [IsNoetherian X] (j : Z ⟶ X) [IsClosedImmersion j]
    (K : X.IdealSheafData)
    (he : (@completion Z (isNoetherian_of_locallyOfFiniteType j) (K.comap j)).IsEquivalence)
    (M : CoherentFormalModule X K) (hM : SupportedOn K M j) :
    ∃ (G : CoherentModules Z)
      (hG : RingedSpace.IsCoherent X.toRingedSpace ((Scheme.Modules.pushforward j).obj G.obj)),
      Nonempty ((completion X K).obj ⟨(Scheme.Modules.pushforward j).obj G.obj, hG⟩ ≅ M)
    := by
  classical
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType j
  obtain ⟨⟨E, ⟨β⟩⟩, θ, hθ⟩ := closedImmersion_coherentFormal_equivalence j K
  let N : CoherentFormalModule Z (K.comap j) := E.inverse.obj ⟨M, hM⟩
  let C := completion Z (K.comap j)
  let := he
  let G : CoherentModules Z := C.objPreimage N
  have hG := (Scheme.Modules.isCoherent_pushforward_of_isFinite j G.obj G.property).1
  refine ⟨G, hG, ⟨?_⟩⟩
  apply ObjectProperty.isoMk
  exact θ.app G ≪≫
    ((Functor.whiskeringRight _ Z.Modules X.Modules).obj
      (Scheme.Modules.pushforward j)).mapIso
        ((ObjectProperty.ι (IsCoherentFormalModule (K.comap j))).mapIso
          (C.objObjPreimageIso N)) ≪≫
    (β.app N).symm ≪≫
    (ObjectProperty.ι (fun M : CoherentFormalModule X K ↦ SupportedOn K M j) ⋙
      ObjectProperty.ι (IsCoherentFormalModule K)).mapIso (E.counitIso.app ⟨M, hM⟩)

end AlgebraicGeometry
