/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.AlgebraicGeometry.GroupScheme.BorelCharacteristicPicardSequence
import Sheaf.AlgebraicGeometry.MultiplicativeIsogenyComposition
import Sheaf.AlgebraicGeometry.CharacterPicardIsogenySequence

/-! # A multiplicative cover with trivial Picard group

Source: Milne, Algebraic Groups (2017), Proposition 18.22 (Iversen 1976, 2.7),
printed pp.392--393, and Definition 18.1
(blueprint: lem-sfb-picard-trivial-multiplicative-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every smooth connected affine algebraic group over an algebraically closed field has
 a smooth connected affine multiplicative cover with trivial Picard group.

Source: Milne, Algebraic Groups (2017), Proposition 18.22, printed pp.392--393;
Definition 18.1 and Proposition 18.2, printed p.387
(blueprint: lem-sfb-picard-trivial-multiplicative-cover).

Proof plan:
1. Choose a Borel subgroup B of G. The node lem-sfb-borel-characteristic-picard-sequence
   makes Pic(G/B) → Pic(G) surjective. By lem-sfb-flag-effective-picard-generators choose
   finitely many generating line bundles L_i on G/B with nonzero global sections.
   Their pullbacks generate Pic(G).
2. By lem-sfb-flag-projective-linear-system, each L_i is the pullback of O(1) under a
   G-equivariant map G/B → P(V_i), where G → PGL(V_i) is a projective representation
   and V_i is nonzero and finite-dimensional. Retain the tautological linear action.
3. Start with P_0 = G and f_0 = id. Successively apply
   lem-sfb-projective-representation-smooth-lift to the projective representation of
   P_{i-1}. Obtain a smooth connected multiplicative cover q_i : P_i → P_{i-1} and
   a lift to SL(V_i). Set f_i = q_i ≫ f_{i-1}; multiplicativity follows from
   lem-sfb-multiplicative-isogeny-composition. This uses the smooth connected lift,
   rather than assuming the raw fibre product smooth or connected.
4. At y_i = t_i(eB), let W_i be the one-dimensional fibre of O(1). Equivariance and
   the lifted linear action identify P_i × W_i with f_i*π*L_i: on fibres the map is
   (p,w) ↦ (p,ρ_i(p)w), with inverse (p,z) ↦ (p,ρ_i(p)⁻¹z). These regular maps are
   inverse after every scalar extension. A basis of W_i trivializes the line bundle.
   Previous trivializations persist under pullback along q_i. Thus f_r* kills all
   generators, so f_r* : Pic(G) → Pic(P_r) is zero.
5. By lem-sfb-character-picard-isogeny-sequence that pullback is also surjective.
   Every Picard class on P_r is therefore zero. If there are no generators, take
   P_r = G and f_r = id; its kernel is D(0). This includes the trivial group.

`IsFiniteDiagonalizableGroupScheme` specifies D(M) by its natural group-valued functor
on all test schemes, including nonreduced ones. `Subsingleton P.left.Pic` says that every
invertible module class equals the class of the structure sheaf; the existing Picard group
uses multiplicative notation for tensor product. -/
theorem picard_trivial_multiplicative_cover
    (F : Type u) [Field F] [IsAlgClosed F]
    (G : Over (Spec (.of F))) [GrpObj G]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left] :
    ∃ (P : Over (Spec (.of F))) (_ : GrpObj P),
      IsAffine P.left ∧ LocallyOfFiniteType P.hom ∧ QuasiCompact P.hom ∧
      Smooth P.hom ∧ ConnectedSpace P.left ∧
      ∃ (f : P ⟶ G) (_ : IsMonHom f),
        f.left.appTop.hom.FaithfullyFlat ∧ IsFinite (GrpObj.ker f).hom ∧
        IsFiniteDiagonalizableGroupScheme (GrpObj.ker f) ∧ Subsingleton P.left.Pic := by
  sorry

end AlgebraicGeometry
