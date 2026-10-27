module

public import Sheaf.AlgebraicGeometry.GroupScheme.ParabolicSubgroup
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.AlgebraicGeometry.GroupScheme.SmoothUnipotentExtension
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # A noncentral split torus gives a proper minimal rational parabolic

Source: Milne, Algebraic Groups (2017), Proposition 25.2, p.545, and
Chapter 25(a), Theorems 25.1 and 25.8, pp.544--546
(blueprint: lem-sfb-field-parabolic-isotropy-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A reductive group containing a noncentral closed split torus contains a proper
minimal parabolic over the original field, including finite and imperfect fields.
Noncentrality is witnessed on an arbitrary commutative algebra, with no reducedness
restriction. Properness means that the inclusion is not an isomorphism.

Source: Milne, Algebraic Groups (2017), Proposition 25.2, p.545; Chapter 25(a),
Theorems 25.1 and 25.8, pp.544--546
(blueprint: lem-sfb-field-parabolic-isotropy-criterion).

Proof plan (the four steps of the DAG node):
1. Choose a split presentation T ≅ G_m^r. Its coordinate cocharacters multiply
   to every T-point over every test algebra. If all coordinate cocharacters
   were central, so would be T. Thus one coordinate cocharacter λ is noncentral,
   and r > 0.
2. Apply lem-sfb-reductive-cocharacter-parabolic-geometry. Its P_λ is a smooth
   geometrically connected closed subgroup, and its fppf coset sheaf is represented
   by a smooth projective scheme. By lem-kun-projective-implies-proper the latter
   is proper and finite type (def-weil-proper-morphism). Thus P_λ is parabolic
   with the specified fppf right-coset convention.
3. If P_λ = G, the cocharacter geometry gives G ≅ U_λ ⋊ Z_λ and a split
   additive series for U_λ. Extend to an algebraic closure. The trivial group
   and G_a are unipotent, the latter via its upper unitriangular 2 by 2 embedding.
   Descending induction through the series, using lem-sfb-smooth-unipotent-extension,
   makes U_λ unipotent. Reductivity kills this smooth connected normal subgroup,
   so G = Z_λ after extension. The defining ideal of Z_λ then vanishes already
   over k, since scalar extension of vector spaces to an algebraic closure is
   faithful (extend any nonzero vector to a basis). The centralizer's functorial
   definition contradicts the noncentrality of λ. Hence P_λ is proper.
4. The affine finite-type group G is Noetherian by lem-wf-affine-noetherian-components.
   Among supports of parabolics contained in P_λ choose a minimal one; otherwise
   successive strict descent contradicts the descending chain condition. If Q is
   parabolic and contained in this P, minimality gives equal supports. Both are
   reduced, since smooth over k, by sbc-lem-smooth-geometrically-reduced.
   The uniqueness in lem-weil-pbc-reduced-induced-closed-subscheme gives equality
   of their ideal sheaves and hence of their closed subgroup schemes. Thus P is
   minimal, and P ⊆ P_λ ≠ G makes it proper. This uses no perfection or infinitude.
-/
theorem exists_proper_minimalParabolic_of_noncentral_splitTorus
    {k : Type u} [Field k] (G T : Grp (Over (Spec (.of k))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (i : T ⟶ G) [IsClosedImmersion i.hom.hom.left]
    (hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (hnoncentral : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A)
      (t : StandardGroupSchemes.affine k A ⟶ T.X)
      (g : StandardGroupSchemes.affine k A ⟶ G.X),
        ¬ Commute (t ≫ i.hom.hom) g) :
    ∃ (P : Grp (Over (Spec (.of k)))) (j : P ⟶ G),
      IsMinimalParabolicSubgroup j ∧ ¬ IsIso j := by
  sorry

end AlgebraicGeometry
