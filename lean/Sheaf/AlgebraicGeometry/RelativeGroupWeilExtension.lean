module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Gluing

/-! # Weil extension into a relative smooth separated group scheme

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §4.4, Theorem 1,
printed pp. 109--110 (PDF pp. 115--116)
(blueprint: lem-sfb-relative-group-weil-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A morphism from a fibrewise dense open of a smooth scheme over a normal Noetherian
base into a smooth separated group scheme extends uniquely if its domain contains every
point whose local ring has dimension at most one. Neither source nor target is assumed
quasi-compact, and the group is not assumed commutative or fibrewise connected.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §4.4, Theorem 1,
printed pp. 109--110 (PDF pp. 115--116)
(blueprint: lem-sfb-relative-group-weil-extension).

Proof:
1. Cover Z by affine opens T lying over affine opens S₀ of S. Smoothness restricts
   by lem-weil-pbc-smooth-restrict-open-subschemes. By lem-sfb-smooth-normal-ascent
   and lem-trf-smooth-reduced-dense-pullback, T is normal, reduced and Noetherian.
   The open U ∩ T contains every generic point, hence is dense, also after further
   open restriction. The local-ring dimension condition is unchanged.
2. Form P = T ×[S₀] T. Its projections are smooth by lem-pc-proper-base-change.
   The open D = (U ∩ T) ×[S₀] (U ∩ T) is dense by two applications of
   lem-trf-smooth-reduced-dense-pullback. On D define g(z₁,z₂) = u(z₁)u(z₂)⁻¹.
   Its restriction along the diagonal is the unit section. The target remains
   separated over S₀ because its diagonal is the restricted closed immersion.
3. Apply lem-sfb-smooth-section-rational-extension to the first projection P → T,
   the diagonal section, g on D and the unit map T → H. The inverse image of D
   along the section is U ∩ T, containing all points of local dimension at most one.
   Obtain a morphism v on an open V containing the diagonal and agreeing with g on V ∩ D.
4. Set W = V ∩ p₂⁻¹(U ∩ T). The first projection f : W → T is smooth by
   lem-pc-proper-base-change and lem-weil-pbc-smooth-restrict-open-subschemes,
   hence flat and locally of finite presentation by lem-pc-smooth-flat, and open
   by lem-weil-pbc-flat-lfp-open. Each fibre V_z is nonempty since V contains the
   diagonal. By lem-sc-scheme-over-field-universally-open, its image in T_s is a
   nonempty open, meeting the dense (U ∩ T)_s. Thus f is surjective. On every affine
   of T its inverse-image affine opens have open images covering that affine;
   compactness chooses finitely many. This is def-weil-pbc-fpqc-covering.
5. The morphism h(z₁,z₂) = v(z₁,z₂)u(z₂) on W agrees with u after f over U ∩ T,
   by associativity and the inverse identity, without commutativity. On W ×[T] W
   the two pullbacks of h agree over U ∩ T. Their source is reduced and that open
   is dense by successive smooth pullbacks, using lem-trf-smooth-reduced-dense-pullback
   and lem-pc-proper-base-change. By lem-sfb-relative-separated-dominant-ext the
   two morphisms agree everywhere, giving the descent cocycle.
6. Apply lem-weil-pbc-fpqc-representable-descent to descend h uniquely to T → H.
   The same uniqueness, with target S, proves that the descended map is over S.
   Restricting the cover to U ∩ T and using h = u after f proves the restriction
   equation by uniqueness in descent. The restricted cover is fpqc by step 4's argument.
7. On overlaps these local maps agree on the dense open induced by U, hence agree
   by lem-sfb-relative-separated-dominant-ext. Glue by lem-weil-pbc-scheme-morphism-gluing.
   The same separatedness argument proves uniqueness on Z. Arbitrary covers suffice;
   the empty source has its unique map, and empty fibres impose no extra condition.
-/
theorem existsUnique_relative_group_weil_extension
    (S : Scheme.{u}) [IsNoetherian S]
    (_hS : ∀ s : S,
      IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    (Z : Scheme.{u}) (p : Z ⟶ S) [Smooth p]
    (H : Over S) [GrpObj H] [Smooth H.hom] [IsSeparated H.hom]
    (U : Z.Opens) (f : U.toScheme ⟶ H.left) (_hf : f ≫ H.hom = U.ι ≫ p)
    (_hdense : ∀ s : S, Dense ((p.fiberι s) ⁻¹' (U : Set Z)))
    (_hcodim : ∀ z : Z, ringKrullDim (Z.presheaf.stalk z) ≤ 1 → z ∈ U) :
    ∃! g : Z ⟶ H.left, g ≫ H.hom = p ∧ U.ι ≫ g = f := by
  sorry

end AlgebraicGeometry
