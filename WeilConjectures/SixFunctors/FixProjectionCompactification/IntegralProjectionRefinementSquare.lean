/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionCompactificationData
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionSystemCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization

/-! # The integral projection square for a single proper refinement

Source: current blueprint, prop-sf-pf-coherence.proof.md, compactification-independence
sentence; the integral realization of the tensor/counit calculation.
(blueprint: lem-sf-integral-projection-refinement-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

set_option synthInstance.maxSize 4096

attribute [local irreducible] coefficientSequenceLimit
  compactificationProjection RefinementProjection.systemComparison
  SixFunctorExchangeData.projectionComponent

/-- Transport four individual arrows along endpoint isomorphisms.
Source: functoriality and cancellation (blueprint: lem-sf-integral-projection-refinement-square).
-/
private theorem realizeDirectedSquare
    {A B H : Type*} [Category A] [Category B] [Category H]
    (F : A ⥤ H) [F.Faithful] (R : B ⥤ H)
    {a b c d : A} {a' b' c' d' : B}
    {p : a ⟶ b} {q : c ⟶ d} {s : a ⟶ c} {t : b ⟶ d}
    {p' : a' ⟶ b'} {q' : c' ⟶ d'} {s' : a' ⟶ c'} {t' : b' ⟶ d'}
    {ea : R.obj a' ≅ F.obj a} {eb : R.obj b' ≅ F.obj b}
    {ec : R.obj c' ≅ F.obj c} {ed : R.obj d' ≅ F.obj d}
    (hp : R.map p' ≫ eb.hom = ea.hom ≫ F.map p)
    (hq : R.map q' ≫ ed.hom = ec.hom ≫ F.map q)
    (hs : R.map s' ≫ ec.hom = ea.hom ≫ F.map s)
    (ht : R.map t' ≫ ed.hom = eb.hom ≫ F.map t)
    (h : p' ≫ t' = s' ≫ q') : p ≫ t = s ≫ q := by
  apply F.map_injective
  simp only [Functor.map_comp]
  apply (cancel_epi ea.hom).mp
  have he := congrArg (fun v ↦ R.map v ≫ ed.hom) h
  simp only [Functor.map_comp, Category.assoc] at he
  rw [ht, hq] at he
  simp only [← Category.assoc] at he
  rw [hp, hs] at he
  simpa only [Category.assoc] using he

/-- Reverse the direction of the two invertible vertical arrows in a square.
Source: isomorphism cancellation (blueprint: lem-sf-integral-projection-refinement-square).
-/
private theorem forwardOfBackward
    {A : Type*} [Category A] {a b c d : A} (s : a ≅ c) (t : b ≅ d)
    {p : a ⟶ b} {q : c ⟶ d} (h : q ≫ t.inv = s.inv ≫ p) :
    p ≫ t.hom = s.hom ≫ q := by
  apply (cancel_mono t.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Iso.hom_inv_id_assoc]

/-- The integral counit projection commutes with one proper refinement, before the
common-refinement argument. Only the second tensor input is assumed finite Tor.

Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence;
lem-fix-projection-compactification-comparison, proof steps 7--8.
(blueprint: lem-sf-integral-projection-refinement-square).

Proof: use integral residue Tor to obtain uniform finite-reduction intervals for K
and L. Pullback, tensor, exact open extension and proper direct image preserve the
required constructibility and uniform bounds; open tensor normalization makes the
open outputs normalized. All compactifying schemes are finite type over the field,
hence Noetherian; the opens are quasi-compact. Realize the resulting finite diagram
in the derived category of strict semilinear systems. The proper/open projection
mate for (j_c, id_X, r, j_d), together with the counit-composition identity, gives
PF_d followed by the inverse refinement map = tensor of the inverse refinement map
followed by PF_c, in that system category itself. Naturality moves the inner proper
projection past the outer one. Cancel the two witnessed proper/open isomorphisms
to obtain the forward refinement square. Apply total limit to this equality.
The compactification-system realization intertwines every tensor, pullback,
open, counit, composition and proper/open factor, so the resulting square is the
one displayed here in the operation datum's coordinates. The completed open
comparison preserves completeness. No faithfulness of finite evaluation is used,
and no projection map is inverted. Identity refinements give the identity square;
zero inputs and empty opens give the zero square with the same construction. -/
theorem integralRefinementProjection
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k)) :
    refinementLaw S.higher.integral S.higher.integralTensor S.higher.integralExchange
      (fun Y K ↦ finiteTorConstructibleIntegral C.l E Y.obj.left K.obj) := by
  obtain ⟨o, ⟨z⟩⟩ := integralCompactificationSystemRealization C.l E D C.different
  intro X Y f _ _ _ c d r K L hL
  obtain ⟨alpha, beta, hp, hq⟩ :=
    integralProjectionSystemCoordinates D C E n hn S hl o z f K L hL
  let M := (calculus C.l E X.obj.left).reduction.obj K.obj
  let N := (calculus C.l E Y.obj.left).reduction.obj L.obj
  let F := (sfIntegralConstructible C.l E Y.obj.left).ι
  let R := coefficientSequenceLimit C.l E Y.obj.left
  have hs := (AlgebraicGeometry.ProEtale.AmbientProperOpen.refinementProjectionCounit
    D C.l C.different E 0 c d r).2 o z M N
  have hback :
      (S.higher.integralExchange (identitySquare f d)).projectionComponent K L ≫
          (S.higher.integral.comparison f c d).inv.app
            (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull f).obj L)) =
        ((S.higher.integralTensor Y).map
          ((S.higher.integral.comparison f c d).inv.app K)).app L ≫
            (S.higher.integralExchange (identitySquare f c)).projectionComponent K L := by
    exact realizeDirectedSquare F R (hp d) (hp c) (hq c d r).2 (hq c d r).1 hs
  exact forwardOfBackward
    (((S.higher.integralTensor Y).mapIso ((S.higher.integral.comparison f c d).app K)).app L)
    ((S.higher.integral.comparison f c d).app
      (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull f).obj L))) hback

end WeilConjectures.FixProjectionCompactification
