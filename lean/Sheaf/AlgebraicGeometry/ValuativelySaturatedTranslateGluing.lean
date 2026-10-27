/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Gluing valuatively saturated generic translates

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §10.1, Example 5 and Proposition 7,
pp. 291--293; the valuative saturation abstraction in the DAG
(blueprint: lem-sfb-valuatively-saturated-translate-gluing).

The image of integral sections is a subgroup of generic sections. The auxiliary map
`translatedGenericInclusion` is the generic inclusion multiplied by a constant generic
section, using the original group object over the trait. The theorem specifies the glued
scheme by its covering charts and cartesian overlap squares, as in Stacks Tags 01JB/01JC.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace ValuativelySaturatedTranslateGluing

variable {D F : Type u} [CommRing D] [IsDomain D] [Field F]
  [Algebra D F] [IsFractionRing D F]

/-- The image of `B(D)` in `B(F)`, via the group-valued Yoneda restriction map.
Source: BLR §10.1, Proposition 7, pp. 292--293, generic points modulo integral sections
(blueprint: lem-sfb-valuatively-saturated-translate-gluing). -/
noncomputable def integralPointSubgroup (B : Over (Spec (.of D))) [GrpObj B] :
    Subgroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D F))) ⟶ B) :=
  ((yonedaGrpObj B).map
    (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap D F)))
      (Category.comp_id _) :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D F))) ⟶
        Over.mk (𝟙 (Spec (.of D)))).op).hom.range

/-- The generic inclusion translated by `a`: the morphism `b ↦ a b` into the model.
Its source has the structure map of the generic fibre followed by `Spec F → Spec D`.
This is formed directly from the two maps into the given group object, rather than
choosing any extension of a rational translation to the integral model.
Source: BLR §10.1, Example 5 and Proposition 7, pp. 291--293
(blueprint: lem-sfb-valuatively-saturated-translate-gluing). -/
noncomputable def translatedGenericInclusion (B : Over (Spec (.of D))) [GrpObj B]
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D F))) ⟶ B) :
    Over.mk (pullback.snd B.hom (Spec.map (CommRingCat.ofHom (algebraMap D F))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D F))) ⟶ B :=
  (Over.homMk (pullback.snd B.hom (Spec.map (CommRingCat.ofHom (algebraMap D F))))
    rfl ≫ a) *
  Over.homMk (pullback.fst B.hom (Spec.map (CommRingCat.ofHom (algebraMap D F))))
    pullback.condition

/-- Valuatively saturated generic translates glue to a smooth separated scheme locally
of finite type, with generic fibre the given group and exactly the prescribed overlaps.
Source: BLR §10.1, Example 5 and Proposition 7, pp. 291--293, abstracted to the explicit
saturation assumption in the DAG (blueprint: lem-sfb-valuatively-saturated-translate-gluing).

Proof plan:
1. A DVR has only its generic and closed points, so `Spec F → Spec D` is an open
immersion. Use the whole chart on equal indices and the generic fibre on unequal indices.
The translations by `a_eta⁻¹ * a_gamma` have inverse translations and satisfy the cocycle,
also when indices repeat. Apply lem-weil-pbc-glue-schemes (Stacks 01JB/01JC). The structure
maps agree and glue, with locality on stalks checked in a chart.
2. On each generic chart use `b ↦ a_gamma b`. These maps agree and have a common inverse,
since the quotient has an identity class. The cartesian overlaps are the full generic
fibre. The affine finite-type chart covers prove local finite type, and
lem-weil-pbc-smooth-local-on-source proves smoothness.
3. The DVR is Noetherian, and pqf-lem-locnoeth-lft makes both the model and the gluing
locally Noetherian. Apply lem-sfb-locnoeth-valuative-separatedness. Separatedness of B
also identifies integral sections with their generic restrictions.
4. For a valuation ring V with fraction field L, two maps Spec V → Z agreeing over L
each factor through a whole chart, by choosing a chart containing the closed point.
In the same chart separatedness of B gives equality. For distinct charts the common
generic restriction lies in their generic overlap, forcing D → V to be injective.
5. If a uniformizer is a unit in V, the map factors through F. Generic equality says
that the two B-valued points differ by precisely the gluing translation; separatedness
of B gives equality of the V-valued points and hence of their images in Z.
6. Otherwise D → V is local and injective. Generic equality makes
`a_eta⁻¹ * a_gamma` the restriction of a V-valued point. Saturation puts it in B(D),
contradicting distinct cosets. Valuative uniqueness therefore holds for every structural
map, including maps through the special point and field valuation rings. The locally
Noetherian valuative criterion (Stacks 01KZ/01L0) proves separatedness of Z. -/
theorem exists_gluing [IsDiscreteValuationRing D]
    (B : Over (Spec (.of D))) [CommGrpObj B]
    [Smooth B.hom] [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    (hsat : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
      (φ : D →+* V) (_hlocal : IsLocalHom φ) (hinj : Function.Injective φ)
      (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D F))) ⟶ B),
      (∃ x : Spec (.of V) ⟶ B.left,
        x ≫ B.hom = Spec.map (CommRingCat.ofHom φ) ∧
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ x =
          Spec.map (CommRingCat.ofHom
            (IsFractionRing.map (K := F) (L := FractionRing V) hinj)) ≫ a.left) ↔
      a ∈ integralPointSubgroup (F := F) B)
    (a : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D F))) ⟶ B) ⧸
      integralPointSubgroup (F := F) B →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D F))) ⟶ B))
    (ha : ∀ γ, QuotientGroup.mk (a γ) = γ) :
    ∃ (Z : Over (Spec (.of D)))
      (j : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D F))) ⟶ B) ⧸
        integralPointSubgroup (F := F) B → (B ⟶ Z)),
      Smooth Z.hom ∧ IsSeparated Z.hom ∧ LocallyOfFiniteType Z.hom ∧
      (∀ γ, IsOpenImmersion (j γ).left) ∧
      (∀ z : Z.left, ∃ γ, ∃ b : B.left, (j γ).left b = z) ∧
      (∀ γ δ, γ ≠ δ →
        IsPullback
          (pullback.fst B.hom (Spec.map (CommRingCat.ofHom (algebraMap D F))))
          (translatedGenericInclusion B ((a δ)⁻¹ * a γ)).left
          (j γ).left (j δ).left) ∧
      ∃ q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).obj Z ≅
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).obj B,
        ∀ γ,
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).map
            (j γ)).left ≫ q.hom.left ≫
              pullback.fst B.hom (Spec.map (CommRingCat.ofHom (algebraMap D F))) =
            (translatedGenericInclusion B (a γ)).left := by
  sorry

end ValuativelySaturatedTranslateGluing
end AlgebraicGeometry
