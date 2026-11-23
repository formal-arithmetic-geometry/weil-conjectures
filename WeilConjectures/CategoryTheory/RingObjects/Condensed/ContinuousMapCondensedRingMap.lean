/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement

/-!
# Functoriality of continuous-map condensed rings

Postcomposition on the recorded universe-polymorphic continuous-map sheaves.
The coefficient rings lie in an arbitrary common universe, independent of the
universe of the profinite sets. The underlying ring objects and their tensor are
exactly those of the continuous-map condensed ring objects.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace Profinite

variable {T T' : Type v} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
  [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']
  (φ : T →+* T') (hφ : Continuous φ)

/-- Postcomposition by a continuous ring homomorphism on the presheaves C(-,T). -/
noncomputable def continuousMapRingPresheafMapOfUniverse :
    continuousMapRingPresheafOfUniverse.{u, v} T ⟶
      continuousMapRingPresheafOfUniverse T' where
  app _ := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((φ.compLeftContinuous _ hφ).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- The canonical morphism of condensed rings induced by postcomposition. -/
noncomputable def continuousMapRingSheafMapOfUniverse :
    continuousMapRingSheafOfUniverse.{u, v} T ⟶ continuousMapRingSheafOfUniverse T' :=
  ⟨continuousMapRingPresheafMapOfUniverse φ hφ⟩

/-- The underlying morphism of abelian sheaves of the continuous-map ring morphism. -/
noncomputable def continuousMapRingObjMapOfUniverse :
    continuousMapRingObjOfUniverse.{u, v} T ⟶ continuousMapRingObjOfUniverse T' :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{max u v + 1} AddCommGrpCat.{max u v + 1})).map
      (continuousMapRingSheafMapOfUniverse φ hφ)

/-- Postcomposition is a morphism for the recorded canonical ring-object structures. -/
theorem isMonHom_continuousMapRingObjMapOfUniverse :
    letI := (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
      (coherentTopology Profinite.{u})).monoidal
    letI := continuousMapRingObjOfUniverseMonObj.{u, v} T
    letI := continuousMapRingObjOfUniverseMonObj.{u, v} T'
    IsMonHom (continuousMapRingObjMapOfUniverse.{u, v} φ hφ) := by
  let := (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
    (coherentTopology Profinite.{u})).monoidal
  let := continuousMapRingObjOfUniverseMonObj.{u, v} T
  let := continuousMapRingObjOfUniverseMonObj.{u, v} T'
  change IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{max u v + 1} AddCommGrpCat.{max u v + 1})).map
      (continuousMapRingSheafMapOfUniverse φ hφ))
  exact Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (continuousMapRingSheafMapOfUniverse φ hφ)

end Profinite
