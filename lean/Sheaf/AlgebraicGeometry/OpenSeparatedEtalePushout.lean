module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceOpenChartTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Limits

/-!
# Pushouts along an open immersion and a separated etale map

Source: Stacks Project, spaces-pushouts.tex, Tag 0DVJ,
lemma-construct-elementary-distinguished-square
(blueprint: lem-per-open-separated-etale-pushout).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An open immersion and a separated chartwise etale map admit an algebraic-space
pushout which is Cartesian, with an open bottom map, a chartwise etale right map,
and an isomorphism over the reduced closed complement of the bottom open.

Source: Stacks Project, Tag 0DVJ, lemma-construct-elementary-distinguished-square
(blueprint: lem-per-open-separated-etale-pushout).

Proof:
1. Put P = W times_V W. Its diagonal is open by etale permanence and the
etale-monomorphism lemma, and closed by separatedness. Thus E = P minus the diagonal
is open and P is the clopen union of the diagonal and E.
2. Form A = V coproduct Z and R = V coproduct W coproduct W coproduct Z coproduct E.
Use the finite scheme-atlas coproducts and the clopen-partition description of sheaf
coproducts (lem-trf-algebraic-space-coproduct, lem-trf-fppf-sheaf-coproduct-partition).
The two maps R -> A are the identities on V and Z, the pairs (q,j), (j,q) on W,
and (j pr1,j pr2) on E. On clopen scheme-test pieces the relation is equality on V,
identification by q between V and W, and equality or equal-q pairs in W on Z.
This is monic, reflexive, symmetric and transitive; local relation sections glue uniquely.
3. Both projections are chartwise etale by base change and composition, the open-chart
tests and finite-coproduct etaleness (lem-trf-space-chartwise-etale-permanence,
lem-a1-space-open-chart-tests, lem-sc-etale-coproduct-etale).
4. Apply lem-per-space-etale-relation-quotient to obtain Y = A/R, the chartwise etale
quotient with etale-local lifts and kernel pair R. Restrict it to obtain a and b.
The two W components give commutativity. The VV kernel-pair component makes b monic,
so lem-sfb-space-etale-monomorphism-open makes b open. The ZV component identifies
W with the pullback of a and b, respecting j and q.
5. Take any reduced closed subspace C supported on the complement of the image of b;
its existence and uniqueness are lem-sfb-space-reduced-closed-support. The point
pullback formula (lem-a1-space-point-open-calculus) makes the pullbacks of V and W
to C empty. The quotient's etale-local lifts therefore lift to Z times_Y C, and its
kernel relation has only the diagonal Z component, since E factors through W.
These lifts are unique, agree on overlaps, and glue by the sheaf condition. They give
an inverse to the canonical projection Z times_Y C -> C. Reducedness of its base
changes is neither needed nor asserted.
6. Compatible maps g : Z -> H and h : V -> H give a coproduct map A -> H equalizing
R: compatibility handles the W components, and g j = h q handles E since q pr1 = q pr2.
The quotient universal property gives a unique Y -> H with the prescribed restrictions.
All constructions are over S. No finiteness or affineness hypothesis is used.
-/
theorem exists_openSeparatedEtalePushout {S : Scheme.{u}} (W Z V : AlgebraicSpace S)
    (j : W ⟶ Z) (q : W ⟶ V)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (hq : IsChartwiseEtale q)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal q.hom.hom)) :
    ∃ (Y : AlgebraicSpace S) (a : Z ⟶ Y) (b : V ⟶ Y),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) b.hom.hom ∧
      IsChartwiseEtale a ∧
      IsPullback j.hom q.hom a.hom b.hom ∧
      (∀ C : ClosedSubspace Y, IsReduced (C.val : AlgebraicSpace S) →
        pointImage C.val.arrow.hom.hom = (pointImage b.hom.hom)ᶜ →
        IsIso (Limits.pullback.snd a.hom C.val.arrow.hom)) ∧
      ∀ (H : AlgebraicSpace S) (g : Z ⟶ H) (h : V ⟶ H), j ≫ g = q ≫ h →
        ∃! t : Y ⟶ H, a ≫ t = g ∧ b ≫ t = h := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
