/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.SetUnderivedExchangeSectionwise
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero

/-!
# Proper base change for arbitrary sheaves of sets on schemes

Source: Stacks Project, Étale Cohomology, Tag 0A3U, with Tag 0A3T
(blueprint: lem-sfb-scheme-proper-set-sheaf-base-change).

The existing set-valued exchange is used with its counit-transpose normalization,
as identified by `setUnderivedExchangeSectionwise`. Scheme properness is the scheme
specialization of properness in `AlgebraicSpaceMorphismProperties`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The chosen Cartesian square of the actual scheme fibre product, with its two
projections, transposed using the canonical pullback symmetry. Source: Stacks Project, Tag 0A3U
(blueprint: lem-sfb-scheme-proper-set-sheaf-base-change). -/
def Scheme.setSheafBaseChangeSquare {X Y Y₁ : Scheme.{u}}
    (p : X ⟶ Y) (v : Y₁ ⟶ Y) :
    ChosenCartesianSquare (pullback.snd p v) (pullback.fst p v) v p where
  w := pullback.condition.symm
  isoPullback := pullbackSymmetry p v
  hom_fst := pullbackSymmetry_hom_comp_fst p v
  hom_snd := pullbackSymmetry_hom_comp_snd p v

/-- Proper base change for every sheaf of sets, natural in that sheaf.
Source: Stacks Project, Étale Cohomology, Tags 0A3U and 0A3T
(blueprint: lem-sfb-scheme-proper-set-sheaf-base-change).

Proof:
1. Expand the existing exchange using `setUnderivedExchangeSectionwise`: its transpose
   is the inverse-image square comparison followed by the pulled-back counit. The
   unit-composition equations of lem-weil-pbc-sets-etale-inverse-image-composition-units
   and the adjunction triangle identity identify its other transpose with p_*(unit_w).
   Thus on a unit-pulled section the exchange is its pullback to the fibre product.
2. Properness is stable under base change (lem-weil-pbc-proper-base-change) and implies
   quasi-compactness and separatedness; lem-pc-separated-quasi-separated gives quasi-
   separatedness. Apply lem-weil-pbc-sets-pushforward-stalk-strict-henselization to p and
   its base change. Its comparison sends an affine represented germ to restriction
   along the pointed-neighbourhood projection.
3. Clause (1) of lem-weil-pbc-strict-henselization-functoriality identifies the strictly
   henselian ring, its separably closed residue field and the closed-lift factorizations.
   Apply lemma-weil-pbc-proper-strict-henselian-h0 in its residue-field-fibre form, then
   lem-weil-pbc-sections-base-field-extension to the geometric residue-field extension.
   Hence each proper direct-image stalk is canonically sections on its geometric fibre,
   with the restriction formula on represented germs.
4. Use lem-weil-pbc-sets-etale-inverse-image-stalk-germ on v. The two geometric fibres
   are canonically the same scheme, with the same map to X. On every represented germ,
   step 1 and the restriction formulas of steps 2-3 give the same section on this fibre.
   Therefore the actual exchange, rather than an arbitrary map of its endpoints, is
   bijective on geometric stalks.
5. Apply lem-weil-pbc-sets-etale-iso-on-geometric-stalks. Unit naturality followed by
   adjunction gives the displayed naturality equation. Empty schemes and empty fibres
   have singleton section sets; an empty target has an empty conservative point family.
   No algebraic structure on the sheaf or further geometric hypothesis was used. -/
theorem scheme_proper_setSheaf_baseChange (S : Scheme.{u})
    (X Y Y₁ : Over S) (p : X ⟶ Y) [IsProper p.left] (v : Y₁ ⟶ Y) :
    (∀ A : Sheaf X.left.smallEtaleTopology (Type (u + 1)),
      IsIso (Etale.setBaseChangeArrow
        (Scheme.setSheafBaseChangeSquare p.left v.left) A)) ∧
    (∀ (A B : Sheaf X.left.smallEtaleTopology (Type (u + 1))) (a : A ⟶ B),
      (Scheme.etaleSetPullback v.left).map ((Etale.lowerStar (Type (u + 1)) p.left).map a) ≫
          Etale.setBaseChangeArrow
            (Scheme.setSheafBaseChangeSquare p.left v.left) B =
        Etale.setBaseChangeArrow
            (Scheme.setSheafBaseChangeSquare p.left v.left) A ≫
          (Etale.lowerStar (Type (u + 1)) (pullback.snd p.left v.left)).map
            ((Scheme.etaleSetPullback (pullback.fst p.left v.left)).map a)) := by
  sorry

end AlgebraicGeometry
