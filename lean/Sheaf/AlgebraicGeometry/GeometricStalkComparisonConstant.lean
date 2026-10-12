/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-! # Comparing geometric stalks over the same scheme point

Source: Stacks Project, Tag 04FN; the generic submodule paragraph of Tag 09BH (3).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Geometric stalk functors at two points with the same image admit an isomorphism
which acts as the identity on the value of every constant module sheaf.
Source: Stacks Project, Tag 04FN, and Tag 09BH (3), generic submodule paragraph.
(blueprint: lem-weil-pbc-geometric-stalk-comparison-constant).

Proof: Let x be the common image and choose a separable closure K of its residue field.
The residue-field embeddings defining s and t extend to embeddings of K into their
separably closed fields. Both geometric points therefore factor through Spec K over X.
Precomposition with either resulting morphism of geometric points is a bijection on
pointed etale lifts: the residue fields of etale neighbourhoods are finite separable
extensions of the residue field at their image, and their embeddings factor uniquely
through the separably closed subfield. These bijections form natural isomorphisms of
point fibre functors, hence equivalences of pointed neighbourhood categories compatible
with forgetting the lift. The induced colimit isomorphisms give isomorphisms of module
stalk functors, natural in the sheaf. Compose one with the inverse of the other.
A constant section is unchanged by precomposition with a point morphism; since every
constant-presheaf germ is represented by such a section, the comparison is the identity
under the constant-stalk isomorphisms. Sheafification preserves the stalk and its germ
map, so the displayed normalization also holds for constant sheaves. No genericity,
monomorphism, finiteness, or irreducibility is needed. -/
theorem exists_geometricStalkComparison_constant
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    [Limits.PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ))]
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω') ⟶ X)
    (h : s (IsLocalRing.closedPoint Ω) = t (IsLocalRing.closedPoint Ω')) :
    ∃ β : (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
        (pointSmallEtale t).sheafFiber,
      ∀ M : ModuleCat.{u + 1} Λ,
        β.hom.app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
          ((pointSmallEtale t).sheafFiberConstantSheafIso M).hom =
          ((pointSmallEtale s).sheafFiberConstantSheafIso M).hom := by sorry

end AlgebraicGeometry.Scheme
