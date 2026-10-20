/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NQ and NJ
-/
module

public import Sheaf.Paper.PbcAutomorphismTransport
public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Completed coefficient transport and Weil categories

Source: Weil conjectures blueprint, finite coefficient and Weil-category definitions
(blueprint: def-wf-weil-category).

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `WeilD`: fixed pairs for the geometric Frobenius pullback.
- `weilScalarExtension`: the coefficient transition with its Weil structure.
- `WeilDQbar`: the common-stage category of the finite Weil categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite




namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v z
variable {C : Type z} [Category.{v} C] [Preadditive C] (F : C ⥤ C) [F.Additive]

/-- The group laws on commuting Weil morphisms are inherited from the coefficient category.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def PreadditiveNormalized (P : Preadditive (IsoAlgebra F)) : Prop := by
  letI := P
  exact ∀ (K L : IsoAlgebra F) (f g : K ⟶ L),
    (f + g).hom.f = f.hom.f + g.hom.f ∧ (0 : K ⟶ L).hom.f = 0

/-- Commuting morphisms have the unique inherited preadditive structure.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: the commuting equation is closed under sums, negatives and zero because
F is additive. These operations make each commuting Hom set an additive
subgroup of the ambient Hom group. Bilinearity follows from ambient bilinearity.
Forgetting the structure is injective on each Hom set, so the displayed
equations determine the group operations and the preadditive structure uniquely. -/
theorem preadditive_exists :
    ∃! P : Preadditive (IsoAlgebra F), PreadditiveNormalized F P := by
  sorry

/-- The group structure with its specified faithful underlying morphisms.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
instance preadditive : Preadditive (IsoAlgebra F) := (preadditive_exists F).exists.choose

end CategoryTheory.Endofunctor.IsoAlgebra

namespace WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [hsep : IsSeparated X₀.hom] [hft : LocallyOfFiniteType X₀.hom]
  [hqc : QuasiCompact X₀.hom]

include hsep hft hqc

/-- The inherited base hypotheses needed by the PBC coefficient stages.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: finite type over a field is noetherian and finite-dimensional, also after
extension to the algebraic closure. The residue characteristic is D.p, and the
coefficient prime differs from it, so that prime is a unit in every local ring. -/
theorem weilGeometricFiber_coefficientHypotheses :
    IsNoetherian (D.geometricFiber X₀).left ∧
      (∃ m : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ m) ∧
      ∀ t : (D.geometricFiber X₀).left,
        IsUnit (c.l : (D.geometricFiber X₀).left.presheaf.stalk t) := by
  sorry

/-- The noetherian instance is a property of the specified geometric fiber.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: base change preserves finite type over the field; a finite-type scheme
over a noetherian field is noetherian. -/
@[instance] theorem weilGeometricFiber_isNoetherian :
    IsNoetherian (D.geometricFiber X₀).left := by
  sorry

/-- The geometric-Frobenius pullback on the exact PBC rational coefficient category.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilFrobeniusPullback (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    PbcRationalCategory (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E) ⥤
      PbcRationalCategory (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E) :=
  pbcRationalIsoPullback (D.geometricFrobenius X₀)
    (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Frobenius transport inherits additivity from scalar localization.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
instance weilFrobeniusPullback_additive (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    (weilFrobeniusPullback D c X₀ E).Additive :=
  ScalarLocalization.mapAdditive _ _ _ _

/-- Weil complexes are fixed pairs in the raw rationalized PBC coefficient category.
The existing IsoAlgebra category has exactly the pairs (K, phi:P(K)≅K) and all
maps u with phi_K ≫ u = P(u) ≫ phi_L. Its identities and composites are those
of the coefficient category; the strict version has these same objects and maps.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
abbrev WeilD (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  CategoryTheory.Endofunctor.IsoAlgebra (weilFrobeniusPullback D c X₀ E)


/-- The underlying coefficient extension, using the geometric fiber's inherited hypotheses.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilCoefficientExtension {E F : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) :
    PbcRationalCategory (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E) ⥤
      PbcRationalCategory (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar F) (pbcStageUniformizer.{u} c.l c.Qbar F) :=
  pbcScalarExtension c.l c.Qbar (D.geometricFiber X₀).left
    (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
    (weilGeometricFiber_coefficientHypotheses D c X₀).2.2 h

/-- The canonical Frobenius/scalar comparison on the raw coefficient stages.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilFrobeniusScalarComparison {E F : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) :
    weilCoefficientExtension D c X₀ h ⋙ weilFrobeniusPullback D c X₀ F ≅
      weilFrobeniusPullback D c X₀ E ⋙ weilCoefficientExtension D c X₀ h :=
  pbcIsoRationalScalarComparison c.l c.Qbar (D.geometricFrobenius X₀)
    (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
    (weilGeometricFiber_coefficientHypotheses D c X₀).2.2 h

/-- Extension sends (K,phi) to (T K,c_K followed by T(phi)), with the same action
T on the underlying commuting morphisms.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilScalarExtension {E F : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) : WeilD D c X₀ E ⥤ WeilD D c X₀ F :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (F := weilFrobeniusPullback D c X₀ E) (G := weilFrobeniusPullback D c X₀ F)
    (L := weilCoefficientExtension D c X₀ h) (weilFrobeniusScalarComparison D c X₀ h)

/-- The Weil transition preserves the inherited addition on morphisms.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: its underlying morphism map is the additive scalar-extension map.
Addition is determined by the faithful forgetful map, so the same identity holds
for commuting morphisms of fixed pairs. -/
@[instance] theorem weilScalarExtension_additive
    {E F : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ F) :
    (weilScalarExtension D c X₀ h).Additive := by
  sorry

/-- The tensor associator is Frobenius-equivariant and thus lifts uniquely to
Weil pairs. Its underlying map is specified, so it is not an arbitrary isomorphism.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: the scalar and Frobenius comparisons are mates of the sectionwise
identity restrictions. Composing these right-adjoint identities in either order
gives the same map. The corresponding left mates commute with tensor
associators, also on complexes and under rationalization. Hence each indicated
component is a commuting morphism of Weil pairs. Its inverse commutes as well;
faithfulness of forgetting the structure gives naturality and uniqueness. -/
theorem weilScalarAssociator_exists {E F G : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) (k : F ≤ G) :
    ∃! a : weilScalarExtension D c X₀ h ⋙ weilScalarExtension D c X₀ k ≅
        weilScalarExtension D c X₀ (h.trans k),
      ∀ K : WeilD D c X₀ E,
        (a.hom.app K).hom.f =
          (pbcScalarAssociator c.l c.Qbar (D.geometricFiber X₀).left
            (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
            (weilGeometricFiber_coefficientHypotheses D c X₀).2.2 h k).hom.app K.carrier := by
  sorry

/-- Tensor balancing induces the associator on the fixed-pair categories.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilScalarAssociator {E F G : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) (k : F ≤ G) :
    weilScalarExtension D c X₀ h ⋙ weilScalarExtension D c X₀ k ≅
        weilScalarExtension D c X₀ (h.trans k) :=
  (weilScalarAssociator_exists D c X₀ h k).exists.choose

/-- The induced associators satisfy the same cocycle equality as tensor balancing.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: forget to the coefficient category and use the defining component
equations and the tensor associator pentagon. The forgetful functor is
faithful, giving the equality of commuting morphisms of pairs. -/
theorem weilScalarAssociator_cocycle
    {E F G H : Padic.FiniteCoefficientFields c.l c.Qbar}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H) (K : WeilD D c X₀ E) :
    (weilScalarExtension D c X₀ j).map ((weilScalarAssociator D c X₀ h k).hom.app K) ≫
        (weilScalarAssociator D c X₀ (h.trans k) j).hom.app K =
      (weilScalarAssociator D c X₀ k j).hom.app ((weilScalarExtension D c X₀ h).obj K) ≫
        (weilScalarAssociator D c X₀ h (k.trans j)).hom.app K := by
  sorry

/-- The equal-field transition is the normalized identity functor.
Source: blueprint order 2106 (blueprint: def-wf-weil-category).
Proof: scalar extension is identity by definition. The sectionwise identity
right comparison has identity mate under the tensor units. The derived and
rational normalizations therefore make its Frobenius comparison identity.
Thus the carriers, structure isomorphisms and all morphisms remain identical. -/
theorem weilScalarExtension_refl (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    weilScalarExtension D c X₀ (le_refl E) = 𝟭 (WeilD D c X₀ E) := by
  sorry

/-- The concrete system of Weil categories with its induced tensor associators.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
def weilScalarSystem :
    StageSystem (fun E : Padic.FiniteCoefficientFields c.l c.Qbar ↦ WeilD D c X₀ E) where
  T h := weilScalarExtension D c X₀ h
  assoc h k := weilScalarAssociator D c X₀ h k
  cocycle h k j K := weilScalarAssociator_cocycle D c X₀ h k j K

/-- The algebraic-closure coefficient category is the common-stage pair category
of the finite Weil stages. Objects are (E,W). Morphisms are representatives
(M,u), modulo equality at a common larger coefficient field, transported by the
specified tensor associators. Composition is at a common stage. In particular
this is the filtered colimit of the Weil categories themselves.
Source: blueprint order 2106 (blueprint: def-wf-weil-category). -/
abbrev WeilDQbar := (weilScalarSystem D c X₀).PairCategory

end WeilConjectures
