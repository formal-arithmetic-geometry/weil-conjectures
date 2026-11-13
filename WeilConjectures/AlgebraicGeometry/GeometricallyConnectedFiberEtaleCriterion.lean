/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest

/-!
# Geometric connectedness of a fibre tested on étale neighbourhoods

## References

* Stacks Project, Tag 03GZ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A fibre is geometrically connected exactly when the fibre over every étale neighbourhood
of its base point is connected (Stacks, Tag 03GZ). -/
theorem Scheme.Hom.geometricallyConnected_fiber_iff_connectedSpace_etale_neighbourhood
    {X S : Scheme.{u}} (g : X ⟶ S) (s : S) :
    GeometricallyConnected (g.fiberToSpecResidueField s) ↔
      ∀ (U : Scheme.{u}) (e : U ⟶ S) [Etale e] (t : U), e t = s →
        ConnectedSpace ((pullback.snd g e).fiber t) := by
  constructor
  · intro h U e _ t ht
    subst s
    exact h.geometrically_connectedSpace _ _ _
      (isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_hasPullback g e) t)
  · intro h
    let := g.fiberOverSpecResidueField s
    apply (GeometricallyConnected.iff_connectedSpace_finite_separable
      (S.residueField s) (g.fiber s)).mpr
    intro K _ _ _ _
    obtain ⟨U, e, he, t, ht, ε, hε⟩ :=
      S.exists_etale_neighbourhood_prescribed_residueField s K
    let := he
    have hc := h U e t ht
    subst s
    let δ : Spec (U.residueField t) ≅ Spec (.of K) :=
      Scheme.Spec.mapIso ε.toCommRingCatIso.op
    have hp := isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback g e) t
    have hmap : Spec.map (e.residueFieldMap t) =
        δ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (e t)) K)) := by
      change Spec.map (e.residueFieldMap t) =
        Spec.map (CommRingCat.ofHom ε.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (e t)) K))
      rw [← Spec.map_comp]
      congr 1
      ext a
      simpa using (hε a).symm
    have hp' := hp.of_iso (fst' := _)
      (snd' := (pullback.snd g e).fiberToSpecResidueField t ≫ δ.hom)
      (f' := g.fiberToSpecResidueField (e t))
      (g' := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (e t)) K)))
      (Iso.refl _) (Iso.refl _) δ (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
      (by simp) (by simp) (by simpa using hmap)
    exact hp'.isoPullback.hom.homeomorph.connectedSpace_iff.mp hc

end AlgebraicGeometry
