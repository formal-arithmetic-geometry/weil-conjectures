/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Topology.ContinuousMapCondensedRing

/-!
# Continuous-map condensed rings with arbitrary coefficient universe

Source: blueprint `sec-proetale-coefficients/sk-def-sfb-condensed-ring/`
`def-sfb-continuous-map-condensed-ring.md`
(blueprint: def-sfb-continuous-map-condensed-ring).

The upstream continuous-map construction fixes the coefficient ring in `Type 0`.
These universe-polymorphic versions retain the same sections, restrictions and canonical
ring-object construction, allowing independent universes for the profinite sets and ring.
The common coefficient universe is `max u v + 1`, so sheafification is available.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite
open scoped CategoryTheory.MonoidalClosed

namespace Profinite

/-- The canonical ring object is commutative when the topological ring is commutative.
Source: blueprint `def-sfb-continuous-map-condensed-ring.md`, final clause
(blueprint: def-sfb-continuous-map-condensed-ring).

Proof: for sections a,b, evaluation at every point gives a(s)b(s)=b(s)a(s).
Their lifted section rings are therefore commutative. Apply the commutative case of
`sk-def-sfb-ring-object`, specifically `Sheaf.isCommMonObj_sheafCompose_obj`, to the
continuous-map sheaf. Its counit-transport construction is exactly the monoid structure
`continuousMapRingObjOfUniverseMonObj`; the tensor and braiding are the canonical
sheafified tensor over the integers supplied by `sk-def-sfb-sheaf-tensor`. -/
theorem isCommMonObj_continuousMapRingObjOfUniverse (T : Type v) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T] :
    @IsCommMonObj
      (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{max u v + 1}) _
      (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
        (coherentTopology Profinite.{u})).monoidal
      (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
        (coherentTopology Profinite.{u})).symmetric.toBraidedCategory
      (continuousMapRingObjOfUniverse T) (continuousMapRingObjOfUniverseMonObj T) := by
  let h := presheaf_enrichedHoms_exist
    (C := Profinite.{u}) (A := AddCommGrpCat.{max u v + 1})
  let : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{max u v + 1}),
    Enriched.FunctorCategory.HasEnrichedHom AddCommGrpCat.{max u v + 1} F G := h.1
  let : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{max u v + 1}),
    Enriched.FunctorCategory.HasFunctorEnrichedHom AddCommGrpCat.{max u v + 1} F G := h.2
  exact Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (continuousMapRingSheafOfUniverse T)
    fun S (a b : ULift.{max u v + 1} C(S.unop, T)) ↦ mul_comm a b

end Profinite
