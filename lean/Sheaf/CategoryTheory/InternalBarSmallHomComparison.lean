/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.InternalBarOrderedCupCore
public import Sheaf.CategoryTheory.InternalBarEquivariantCharacterLifts

/-! # The bar roof comparison in the small-Hom derived category

Source: step 3 of the ordered-cup argument and the normalized roof-adjunction theorem.
This comparison applies to arbitrary homogeneous cocycles, independently of characters.
(blueprint: lem-sfb-internal-bar-small-hom-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar CategoryTheory.CondensedBarRoof
open CategoryTheory.CondensedDerivedRestriction
open Profinite.CondensedAction.InternalBar
namespace CategoryTheory.CondensedBar.OrderedCup

variable {A : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Every homogeneous bar cocycle with the given coordinate formula satisfies the
triangular-sign normalized comparison, in the same localization as the cup calculus.
The row-zero comparison works simultaneously for all degrees and cocycles. No cup
product or character normalization occurs in this assertion.
Source: ordered-cup argument, step 3; normalized roof adjunction, steps 6--11
(blueprint: lem-sfb-internal-bar-small-hom-comparison).

Proof:
1. Apply the internal derived invariant bar theorem to obtain a compatible model M
with its normalized computation. The evaluation isomorphisms of InternalFunctions
uniquely identify its internal-Hom functors with F: both represent the same natural
function families on every slice. Their parameter naturality identifies every bar
operator. The augmentation is uniquely the invariant inclusion and the total
augmentation has the specified bar-zero coprojections. Thus transport M's computation
to B, the supplied augmentation a and total augmentation t.
2. Apply normalized_roofs to M and R. Its augmentation has augmentationEquation.
The map e has the same sole degree-zero component, so single-target extensionality
identifies the augmentations. Its row equation gives the required row-zero map j
through the transported total. In degree n, cochains.map is B.diagram.map evaluated
at [n], so the formula is IsUnderivedComparison. Computation.normalization identifies
the augmentation isomorphism with augmentationArrow t I.
3. For Fq, compose with e[q] and the inverse shifted-single isomorphism to get a map
P to single(-q,A). Its sole component is augmentedRoofComponent. The chain-map equation
gives f boundary = 0. The homogeneousEquation of normalized_roofs identifies this map
with the normalized homogeneous map, by single-target extensionality.
4. The coordinate hypothesis identifies c with its normalized inhomogeneous cocycle.
To check uniqueness on every tuple (g1,...,gq), choose x0=1 and successively
x_(i+1)=x_i g_(i+1). Then x_i^-1 x_(i+1)=g_(i+1). The coordinate equations agree on
all slice evaluations. Naturality and linearity extend equality from the unit to
all sections; evaluation and single-source extensionality give equality of maps.
5. Substitute these identifications in comparisonEquation. Transport along the
canonical equivalence between the two ordinary localizations (Hom universes u+2
and u+1). The localization and shift comparison equations identify its left side
with cocycleArrow and its transpose with inflationPhi of characterRoof. The inverse
shifted-single maps cancel; no extra sign appears. The surviving scalar is exactly
(-1)^(q(q+1)/2). Faithfulness reflects the resulting equality of small-Hom arrows.
No inverse of j is used; only the normalized derived augmentation is inverted.
-/
theorem small_hom_bar_roof_comparison {F : InternalFunctions A}
    (B : BarDiagram (G := G) F) (a : Augmentation (invariants A G) B)
    (t : TotalAugmentation (invariants A G) B a)
    (I : InjectiveResolution (regularTrivial A G)) (R : Resolution A.toMon G)
    (e : RoofAugmentation R) [QuasiIso e] (he : augmentationEquation R e) :
    IsIso (augmentationArrow t I) ∧
      ∃ j : underived B ⟶ resolved B I, IsUnderivedComparison B I j ∧
        ∀ (q : ℕ) (Fq : complex R ⟶ (complex R)⟦(q : ℤ)⟧)
          (c : (HomologicalComplex.single (Modules A) (.up ℤ) (q : ℤ)).obj
            (Mod.regular A.X) ⟶ extend (underived B)),
          (∀ (S : Profinite.{u}) (x : Fin (q + 1) → C(S, G)),
            onSections A.toMon (augmentedRoofComponent R e q Fq).val S
                (basis A.toMon G (q + 1) (R.objects q) (R.freeIso q) S x) =
              (F.evaluate (power G q) S (Mod.regular A.X)
                (onSections A.toMon
                  (Profinite.CondensedAction.InternalBarCharacter.cocycleComponent B c) S
                    (regularOne A.toMon S))).val S (𝟙 S)
                      (tupleMap (fun i ↦ (x i.castSucc)⁻¹ * x i.succ))) →
          cocycleArrow j q c = (-1 : ℤ) ^ (q * (q + 1) / 2) •
            (inflationPhi A G q (characterRoof R e q Fq) ≫ augmentationArrow t I) := by sorry

end CategoryTheory.CondensedBar.OrderedCup
