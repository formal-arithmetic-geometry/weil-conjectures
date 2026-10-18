/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Open pro-etale pullback evaluation and its specified adjunction unit

Source: Stacks Project, Tags 09BN, 00VE, 00WH, 00WX, 00XZ and 03D3
(blueprint: lem-pur-proetale-open-unit-evaluation).

The pullback and unit are the published small-model module constructions.
The coefficient comparison below is normalized on constant sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Compose a pro-etale object's structure map with an open immersion, retaining its
underlying scheme and arrows. Source: Stacks Project, Tags 00XZ and 09BN
(blueprint: lem-pur-proetale-open-unit-evaluation). -/
def proEtaleOpenComposition {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

/-- The first projection from the base-changed object, viewed over the ambient scheme.
It is the counit of the existing composition/base-change adjunction.
Source: Stacks Project, Tags 00VE and 09BN
(blueprint: lem-pur-proetale-open-unit-evaluation). -/
noncomputable def proEtaleOpenSectionProjection {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (V : X.ProEt) :
    (proEtaleOpenComposition j).obj ((proEtaleBaseChange j).obj V) ⟶ V :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial).counit.app V

/-- Open inverse image is evaluation on the same scheme over the ambient base,
with both naturalities, coefficient linearity and the specified unit normalization.
The ring-presheaf isomorphism `d` is the constant-section-preserving restriction
identification of the localization lemma; its naturality is built into its type.

Source: Stacks Project, Tags 09BN, 00VE, 00WH, 00WX, 00XZ and 03D3
(blueprint: lem-pur-proetale-open-unit-evaluation).

Proof plan:
1. For W over U put v(W) = (W → U → X). The canonical map W → u(v(W))
   is invertible because j is a monomorphism. The pair (v(W), e_W) is initial
   in the actual inverse-image index: a map to (V, phi) must be pr_V phi,
   and the two pullback projections prove existence and uniqueness.
2. The restriction maps M(V) → M(v(W)) form a cocone. Its map from the
   colimit is inverse to the coprojection at this initial object. Check both
   composites on coprojections, using their colimit relations.
3. These maps commute with restrictions in W and morphisms in M. The target
   is already a sheaf by weakly-etale localization. Extend the comparison and
   its inverse through sheafification; its universal property proves the inverse
   laws and both naturalities.
4. Transport the indexing object to the specified compatible small models.
   Full faithfulness preserves its initiality. A change of representative cancels
   in the restriction formula, so the same comparison identifies the actual
   published inverse image and adjunction.
5. Apply the calculation to coefficients. The canonical coefficient map sends
   each constant to itself (the constant-ring-map and constant-exact nodes).
   Uniqueness of the constant-presheaf sheafification extension identifies it
   with the inverse of the localization restriction comparison d.
6. The module comparison respects scalar actions on the cocones and hence after
   sheafification. Extend over the sheaf tensor by r tensor m ↦ r • theta(m).
   The inverse is n ↦ 1 tensor theta⁻¹(n); balancing and step 5 prove the two
   inverse laws. These maps are natural in both variables.
7. The Kan adjunction unit is the coprojection indexed by (V, id), followed
   by sheafification and the tensor unit. Under the comparison at u(V), the
   unique indexing arrow is the first projection u(V) → V. Therefore this
   specified unit becomes exactly restriction along that projection. No
   quasi-compactness, support or constructibility condition is used. -/
theorem proEtaleOpenUnitEvaluation {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    ∃ d : (proEtaleConstantRing U A).obj ≅
        (proEtaleOpenComposition j).op ⋙ (proEtaleConstantRing X A).obj,
      (∀ (W : U.ProEt) (a : ULift.{u + 1, u} A),
        (d.hom.app (op W))
            ((toSheafify (ProEt.topology U)
              ((Functor.const U.ProEtᵒᵖ).obj
                (CommRingCat.of (ULift.{u + 1, u} A)))).app (op W) a) =
          (toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1, u} A)))).app
                (op ((proEtaleOpenComposition j).obj W)) a) ∧
      ∃ rho : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : U.ProEt),
          ((proEtaleConstantRingPullback A j).obj M).val.obj (op W) ≃+
            M.val.obj (op ((proEtaleOpenComposition j).obj W)),
        (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : U.ProEt)
          (r : (proEtaleConstantRing U A).obj.obj (op W))
          (m : ((proEtaleConstantRingPullback A j).obj M).val.obj (op W)),
          rho M W (r • m) = (d.hom.app (op W) r) • rho M W m) ∧
        (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
          (W W' : U.ProEt) (b : W' ⟶ W)
          (m : ((proEtaleConstantRingPullback A j).obj M).val.obj (op W)),
          rho M W' (((proEtaleConstantRingPullback A j).obj M).val.map b.op m) =
            M.val.map ((proEtaleOpenComposition j).map b).op (rho M W m)) ∧
        (∀ (M N : proEtaleRingModules X (proEtaleConstantRing X A)) (h : M ⟶ N)
          (W : U.ProEt) (m : ((proEtaleConstantRingPullback A j).obj M).val.obj (op W)),
          rho N W (((proEtaleConstantRingPullback A j).map h).val.app (op W) m) =
            h.val.app (op ((proEtaleOpenComposition j).obj W)) (rho M W m)) ∧
        (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
          (V : X.ProEt) (m : M.val.obj (op V)),
          rho M ((proEtaleBaseChange j).obj V)
              (((proEtaleConstantRingAdjunction A j).unit.app M).val.app (op V) m) =
            M.val.map (proEtaleOpenSectionProjection j V).op m) := by
  sorry

end AlgebraicGeometry.Scheme
