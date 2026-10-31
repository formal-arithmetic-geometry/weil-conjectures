/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Borel
public import WeilConjectures.AlgebraicGeometry.ToriMultiplicativeType
import WeilConjectures.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# A torus and a commuting point lie in a common Borel subgroup

Source: Milne, Algebraic Groups (2017), Lemma 17.37 and its proof, printed p.363.
(blueprint: lem-sfb-torus-commuting-point-common-borel)

The torus may have any rank, including zero. Commutation is required on every
commutative test algebra, and containment of the torus is containment as group schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A torus and a rational point commuting with it belong to a common Borel subgroup.
Source: Milne, Lemma 17.37 and its proof, printed p.363.
(blueprint: lem-sfb-torus-commuting-point-common-borel)

Proof plan:
1. Choose a Borel B₀ using lem-sfb-borel-conjugation-cover and form the represented
   quotient q : G → X = G/B₀ using lem-sfb-homogeneous-orbit-quotient-geometry.
   Its kernel pair identifies q(a) = q(b) with a⁻¹b belonging to B₀, on every test scheme.
   Left multiplication descends to the action on X.
2. The quotient map is locally of finite type by lemma-nagata-finite-type-to-separated-target.
   The target X is Noetherian by lem-weil-pbc-finite-type-over-noetherian, so
   pqf-lem-lft-fp-locnoeth makes q locally of finite presentation. The quasi-compactness
   assertion of lem-weil-pbc-qcqs-morphism-permanence makes q of finite presentation.
3. Flatness, surjectivity and quasi-compactness persist under pullback by
   lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-surjective-base-change and
   lem-weil-pbc-qcqs-morphism-permanence. Thus test points lift fpqc locally along q,
   in the sense of def-weil-pbc-fpqc-covering. Apply
   lem-sfb-borel-quotient-proper-geometry to obtain properness of X.
4. By lem-sfb-borel-conjugation-cover write c = g₀b₀g₀⁻¹. Then q(g₀) is fixed by c,
   so the equalizer Y of c acting on X and the identity has a rational point.
5. Express Y as the pullback of the diagonal of the separated scheme X. It is closed
   by lem-weil-pbc-closed-immersion-base-change, and proper by
   lem-weil-pbc-closed-immersion-proper. It is nonempty and of finite type; no reduction
   or smoothness of this fixed subscheme is imposed.
6. Commutation on every test algebra shows c(t y) = t(c y) = t y. Hence the T-action
   restricts to the defining equalizer Y, with its unit and associativity identities.
7. The torus is smooth and connected by lem-sfb-multiplicative-type-largest-subtorus,
   and its commutativity makes it solvable. Apply lem-sfb-solvable-proper-fixed-point
   to obtain a rational point of Y fixed by T as a group scheme. Lift its image in X
   to g in G(k), using lem-sfb-homogeneous-orbit-quotient-geometry.
8. Set B = gB₀g⁻¹. Conjugation preserves closedness, smoothness, connectedness,
   solvability and maximality. The kernel-pair criterion gives g⁻¹tg in B₀(A) for
   every algebra A and t in T(A), and g⁻¹cg in B₀(k). Thus T factors through B
   as a group scheme, and c lifts to a rational point of B. -/
theorem exists_borelGroupScheme_torus_commuting_point
    {k : Type u} [Field k] [IsAlgClosed k]
    (G T : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : T ⟶ G) (hi : IsClosedSubgroupScheme i.hom.hom)
    (hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ G.X)
    (hc : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : StandardGroupSchemes.affine k A ⟶ T.X),
      Commute (toUnit (StandardGroupSchemes.affine k A) ≫ c) (t ≫ i.hom.hom)) :
    ∃ (B : Grp (Over (Spec (.of k)))) (j : B ⟶ G),
      IsBorelGroupScheme j.hom.hom ∧ (∃ f : T ⟶ B, f ≫ j = i) ∧
        ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X, b ≫ j.hom.hom = c := by
  sorry

end AlgebraicGeometry
