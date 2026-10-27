/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.FiniteDiagramLiftOfModels
import WeilConjectures.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage
import Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of finite Nisnevich covering families

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé III, Lemma 3.1.1,
printed p. 38; the finite-family form is obtained by taking the disjoint union.
(blueprint: lem-per-nisnevich-cover-limit-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite completely decomposed étale family over a Noetherian ring colimit is
completely decomposed and étale at every sufficiently late stage of its fixed models.
The models are only required to be finite type over the initial Noetherian base.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé III, Lemma 3.1.1,
printed p. 38, applied to the disjoint union of the finite family.
(blueprint: lem-per-nisnevich-cover-limit-descent).

Proof:
1. Finite-type schemes over the Noetherian initial base are Noetherian, hence qcqs
   (lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-locally-noetherian-quasi-separated). Every arrow between these models
   is locally finite type: affine generators over the base also generate over the
   target affine coordinate ring. Noetherianity makes this finite presentation
   (lem-weil-pbc-finite-type-noetherian-finite-presentation); qcqs permanence gives
   finite presentation of the model arrows (lem-weil-pbc-qcqs-morphism-permanence).
2. The spectrum of the ring colimit is the affine inverse limit, and base change
   expresses P as the limit of its models (lem-weil-pbc-limit-affine-transition,
   lem-weil-pbc-scheme-over-limit). Descend étaleness of the finitely many arrows to
   a common stage (lem-weil-pbc-descend-etale). It persists at later stages by
   lem-weil-pbc-etale-scheme-base-change.
3. Form the finite disjoint union of the sources (lem-weil-pbc-scheme-coproduct-family).
   It is completely decomposed over P. Use lem-per-cd-finite-presentation-section-cover
   to cover P by finitely presented immersions with lifts to this disjoint union.
   Split each immersion's source by the inverse images of the clopen summands, so
   every lift lands in one V_j. These pieces remain finitely presented immersions
   by qcqs permanence and lem-sbc-locally-finite-presentation-composition.
4. Factor the immersions as closed immersions into quasi-compact opens of P
   (def-weil-closed-immersion). These opens are finitely presented over P by
   Noetherianity and qcqs permanence. Descend all these objects at a common stage
   (lem-weil-pbc-finite-presentation-family-descent).
5. Retaining the prescribed P and V_j models, descend the finitely many arrows
   and their section equations by lem-weil-pbc-finite-diagram-lift-of-models.
   Their local finite presentation follows from the affine argument in step 1.
6. Descend the closed and open factors by lem-weil-pbc-descend-closed-immersion
   and lem-weil-pbc-descend-open-immersion-qcqs. Closed factors persist under base
   change (lem-weil-pbc-closed-immersion-base-change); the open descent statement
   includes all later stages. Make the finite immersion family jointly surjective
   at all later stages (lem-weil-pbc-finite-family-joint-surjectivity-stage).
   Take a common upper bound with the étale stage of step 2.
7. A point p at any later stage lifts to a point t on one of these immersions;
   its section gives z in a V_j above p. The immersion induces an isomorphism
   k(p) -> k(t), using lem-weil-pbc-closed-immersion-residue-field-iso and
   def-weil-open-immersion. By residue-field functoriality (def-weil-residue-field)
   it factors through k(z). A composite of two field embeddings that is an
   isomorphism forces the first embedding to be an isomorphism: after identifying
   the composite with the identity, injectivity of the second map gives the other
   inverse equation. This proves complete decomposition. For an empty family the
   limit target is empty, and the empty immersion cover forces eventual emptiness
   by the same joint-surjectivity lemma. No nonempty scheme or family is assumed. -/
theorem exists_completelyDecomposedEtale_family_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c) [IsNoetherianRing c.pt]
    (i₀ : I) (P₀ : Over (Spec (R.obj i₀)))
    [LocallyOfFiniteType P₀.hom] [QuasiCompact P₀.hom]
    {J : Type v} [Finite J] (V₀ : J → Over (Spec (R.obj i₀)))
    [∀ j : J, LocallyOfFiniteType (V₀ j).hom] [∀ j : J, QuasiCompact (V₀ j).hom]
    (f₀ : ∀ j : J, V₀ j ⟶ P₀)
    (het : ∀ j : J, Etale (((Over.pullback (Spec.map (c.ι.app i₀))).map (f₀ j)).left))
    (hcd : ∀ p : ((Over.pullback (Spec.map (c.ι.app i₀))).obj P₀).left,
      ∃ (j : J) (z : ((Over.pullback (Spec.map (c.ι.app i₀))).obj (V₀ j)).left),
        ((Over.pullback (Spec.map (c.ι.app i₀))).map (f₀ j)).left z = p ∧
          IsIso (Scheme.Hom.residueFieldMap
            (((Over.pullback (Spec.map (c.ι.app i₀))).map (f₀ j)).left) z)) :
    ∃ (i₁ : I) (h₀₁ : i₀ ≤ i₁), ∀ (i : I) (h₁ : i₁ ≤ i),
      (∀ j : J, Etale (((Over.pullback
        (Spec.map (R.map (homOfLE (h₀₁.trans h₁))))).map (f₀ j)).left)) ∧
      ∀ p : ((Over.pullback (Spec.map (R.map (homOfLE (h₀₁.trans h₁))))).obj P₀).left,
        ∃ (j : J)
          (z : ((Over.pullback
            (Spec.map (R.map (homOfLE (h₀₁.trans h₁))))).obj (V₀ j)).left),
          ((Over.pullback (Spec.map (R.map (homOfLE (h₀₁.trans h₁))))).map (f₀ j)).left
              z = p ∧
            IsIso (Scheme.Hom.residueFieldMap
              (((Over.pullback
                (Spec.map (R.map (homOfLE (h₀₁.trans h₁))))).map (f₀ j)).left) z) := by
  sorry

end AlgebraicGeometry
