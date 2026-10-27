/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Ideal.Cotangent
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Injectivity of the differential implies surjectivity on cotangent spaces

Source: Stacks Project, Tags 0B2E and 0B2F
(blueprint: lem-sc-point-tangent-cotangent-surjective).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- Rationality via the scheme residue-field map implies rationality via the structural map. -/
private theorem structural_residue_bijective
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X)
    (hκ : Function.Bijective (p.residueFieldMap x).hom) :
    Function.Bijective
      (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom := by
  have hs (a : Spec (.of k)) : Function.Surjective (StructureSheaf.toStalk k a).hom := by
    have ha : a = IsLocalRing.closedPoint (CommRingCat.of k) := Subsingleton.elim _ _
    subst a
    rw [← stalkClosedPointIso_inv (CommRingCat.of k)]
    exact (stalkClosedPointIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
  change Function.Bijective
    (StructureSheaf.toStalk k (p x) ≫ (p.stalkMap x ≫ X.residue x)).hom
  rw [← Scheme.residue_residueFieldMap]
  exact hκ.comp ⟨(StructureSheaf.toStalk k (p x) ≫
    (Spec (.of k)).residue (p x)).hom.injective,
    ((Spec (.of k)).residue_surjective (p x)).comp (hs (p x))⟩

set_option linter.unusedVariables false in
/-- For a locally finite type morphism over a field, at closed rational points, injectivity
of the differential implies surjectivity on cotangent spaces: the map
`IsLocalRing.CotangentSpace` of the stalk at `f x` to that of the stalk at `x` induced by the
local ring map `f.stalkMap x` (Mathlib's `Ideal.mapCotangent`) is surjective.
The existential in `hdf` supplies the residue-field identification needed by the canonical
`schemeTangentMap`; rationality already implies this identification exists.

Source: Stacks Project, Tags 0B2E and 0B2F
(blueprint: lem-sc-point-tangent-cotangent-surjective).
Proof: First apply `lem-sc-rational-tangent-cotangent-duality` at the two rational points.
Its canonical identifications identify the differential with the dual of the map on maximal
ideals modulo their squares induced by `f.stalkMap x`. Next apply
`lem-sc-dual-map-injective-iff-surjective` to this linear map: injectivity of its dual implies
its surjectivity, which is the claim. -/
theorem cotangent_surjective_of_tangent_injective
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ pY = pX) (x : X)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({f x} : Set Y))
    (hκx : Function.Bijective (pX.residueFieldMap x).hom)
    (hκy : Function.Bijective (pY.residueFieldMap (f x)).hom)
    (hdf : ∃ he : Function.Bijective (f.residueFieldMap x).hom,
      Function.Injective (schemeTangentMap k X Y pX pY f hf x he)) :
    Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (f.stalkMap x).hom.toIntAlgHom
        (Ideal.map_le_iff_le_comap.mp
          (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)) :
        IsLocalRing.CotangentSpace (Y.presheaf.stalk (f x)) →ₗ[ℤ]
          IsLocalRing.CotangentSpace (X.presheaf.stalk x)) := by
  let RX := X.presheaf.stalk x
  let RY := Y.presheaf.stalk (f x)
  let KX := X.residueField x
  let KY := Y.residueField (f x)
  let rX : k →+* KX :=
    (StructureSheaf.toStalk k (pX x) ≫ pX.stalkMap x ≫ X.residue x).hom
  let rY : k →+* KY :=
    (StructureSheaf.toStalk k (pY (f x)) ≫ pY.stalkMap (f x) ≫ Y.residue (f x)).hom
  let : Module k (schemeTangentSpace k X pX x) :=
    Module.compHom (schemeTangentSpace k X pX x) rX
  let : Module k (schemeTangentSpace k Y pY (f x)) :=
    Module.compHom (schemeTangentSpace k Y pY (f x)) rY
  let : Module KX (IsLocalRing.CotangentSpace RX) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField RX) (IsLocalRing.CotangentSpace RX))
  let : Module KY (IsLocalRing.CotangentSpace RY) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField RY) (IsLocalRing.CotangentSpace RY))
  let : Module k (IsLocalRing.CotangentSpace RX) :=
    Module.compHom (IsLocalRing.CotangentSpace RX) rX
  let : Module k (IsLocalRing.CotangentSpace RY) :=
    Module.compHom (IsLocalRing.CotangentSpace RY) rY
  obtain ⟨he, EX, EY, U, -, -, hU, hdual⟩ :=
    rational_tangent_cotangent_duality k X Y pX pY f hf x
      (structural_residue_bijective k X pX x hκx)
      (structural_residue_bijective k Y pY (f x) hκy)
  obtain ⟨he', hinj⟩ := hdf
  have hsurj : Function.Surjective U := by
    apply LinearMap.dualMap_injective_iff.mp
    intro a b hab
    obtain ⟨θ, rfl⟩ := EX.surjective a
    obtain ⟨η, rfl⟩ := EX.surjective b
    apply congrArg EX
    apply hinj
    apply EY.injective
    rw [hdual, hdual]
    exact hab
  intro z
  obtain ⟨v, hv⟩ := hsurj z
  obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal RY) v
  obtain ⟨hb, hUb⟩ := hU b
  exact ⟨(IsLocalRing.maximalIdeal RY).toCotangent b, hUb.symm.trans hv⟩

end AlgebraicGeometry
