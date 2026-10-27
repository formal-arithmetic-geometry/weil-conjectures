/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.AffineSquareMonomorphismAbsoluteSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.AffineGroupoidPointedQuasisplitting
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.FppfGroupoidRestrictionQuotient

/-!
# Etale replacement of an affine fppf equivalence relation

Source: Stacks Project, Bootstrap, Tag 04S6 (`theorem-final-bootstrap`),
the affine locally quasi-finite case, using Tags 04S0 and 04S4
(blueprint: lem-sfb-fppf-relation-etale-replacement).

The quotient presheaves are coequalizers of lifted Yoneda maps. For an
equivalence relation these are the sectionwise orbit quotients. Sheafification
is on the big fppf site over `S`, with values in `Type (u + 1)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry

/-- An affine flat, locally finitely presented, locally quasi-finite equivalence
relation has a finite affine etale covering on which its fppf quotient admits an
etale equivalence-relation presentation.

Source: Stacks Project, Tag 04S6, affine locally quasi-finite case, using Tags
04S0 and 04S4 (blueprint: lem-sfb-fppf-relation-etale-replacement).

Proof:
1. The relation determines unique identity, inverse and composition maps and hence
   a groupoid (def-a1-groupoid-scheme). By
   lem-trf-affine-square-monomorphism-absolute-separated, the arrow scheme is
   absolutely separated. Applying lem-weil-pbc-separated-cancellation to each
   endpoint projection makes both projections separated, without any condition on `S`.
2. Apply lem-sfb-affine-groupoid-pointed-quasisplitting at every point of `V`.
   This gives affine etale charts with open finite locally free subgroupoids.
   Their images are open (lem-a1-space-etale-open-image) and cover `V`.
   Affineness makes `V` quasi-compact (lem-weil-pbc-affine-scheme-qcqs and
   def-weil-pbc-quasi-compact-scheme), so retain a finite subcover together with
   its subgroupoids. For empty `V`, use the empty family.
3. On each chart the restricted relation is monic on its endpoint pair and
   retains flat, locally finitely presented, locally quasi-finite projections.
   By pqf-def-quasifinite the first projection is locally of finite type;
   lem-trf-monomorphism-finite-type-composite-lqf makes the relation map separated
   and locally quasi-finite. Apply lem-sfb-divide-finite-flat-subgroupoid to its
   open finite locally free subgroupoid. Obtain `q : W → Wbar`, surjective finite
   locally free, and a groupoid on `Wbar` whose restriction is the given relation.
   The subgroupoid is both `W ×[Wbar] W` and the pullback of the new unit.
4. The singleton `q` is fppf (def-pc-finite-locally-free, def-pc-fppf-site).
   Factor the restricted endpoint projection through `Rbar ×[Wbar] W`.
   The first factor is a base change of `q`. Source and target descent from
   lem-sfb-representable-fppf-etale-open-descent makes each new endpoint
   projection flat and locally of finite presentation.
5. The restricted arrow scheme covers `Rbar` by two base changes of `q`.
   In the cartesian unit square the pulled-back new unit is the open subgroupoid.
   Target-local descent of open immersions
   (lem-sfb-representable-fppf-etale-open-descent) makes the new unit open.
6. Apply lem-sfb-groupoid-open-unit-etale to the new groupoid and steps 4 and 5.
   Its endpoint projections are etale. The theorem
   lem-sfb-fppf-groupoid-restriction-quotient reflects monicity of its relation
   map and identifies its fppf quotient with the restricted quotient.
   The groupoid laws make the arrow-existence relation an equivalence relation.
7. All schemes and finite pullbacks remain in the fixed universe. The finite
   subcover can be indexed in that universe, including its empty case, and the
   orbit presheaves are lifted into the next universe before sheafification,
   as required by def-weil-size-convention. -/
theorem fppf_relation_etale_replacement {S : Scheme.{u}} {R V : Over S}
    (s t : R ⟶ V) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [IsAffine V.left] [Flat s.left] [Flat t.left]
    [LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left]
    (hs : s.left.IsLocallyQuasiFinite) (ht : t.left.IsLocallyQuasiFinite) :
    ∃ (I : Type u) (_ : Finite I) (W : I → Over S) (g : ∀ i : I, W i ⟶ V),
      (∀ i : I, IsAffine (W i).left ∧ Etale (g i).left) ∧
      (∀ v : V.left, ∃ (i : I) (w : (W i).left), (g i).left w = v) ∧
      ∀ i : I, ∃ (Wbar Rbar : Over S) (sbar tbar : Rbar ⟶ Wbar),
        Mono (prod.lift sbar tbar) ∧
        (∀ T : Over S, Equivalence (fun a b : T ⟶ Wbar ↦
          ∃ r : T ⟶ Rbar, r ≫ sbar = a ∧ r ≫ tbar = b)) ∧
        Etale sbar.left ∧ Etale tbar.left ∧
        Nonempty
          ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
              (coequalizer
                (uliftYoneda.{u + 1}.map (restrictedEtaleRelationSource s t (g i)))
                (uliftYoneda.{u + 1}.map (restrictedEtaleRelationTarget s t (g i)))) ≅
            (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
              (coequalizer (uliftYoneda.{u + 1}.map sbar)
                (uliftYoneda.{u + 1}.map tbar))) := by
  sorry

end AlgebraicGeometry
