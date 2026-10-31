/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Representability of one free integral root level

Source: the Roots of unity and Integral twist paragraphs of the current blueprint
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`.
(blueprint: lem-pur-transport-tate-level-representation).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The underlying set sheaf of a single finite integral Tate level is finite etale.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`, Roots of unity and Integral twist.
(blueprint: lem-pur-transport-tate-level-representation).

Proof: reduction of the continuous integral coefficient ring modulo ell^n is the
constant finite residue ring. Consequently its tensor with the ell^n-torsion root
sheaf is canonically the root sheaf: multiplication and z -> 1 tensor z are inverse.
This can be checked on a primitive-root cover using the free constant residue
comparison; both maps are canonical and hence descend. The root functor is
represented by Spec(O_Y[t]/(t^(ell^n)-1)), constructed by base change from
Spec Gamma(Y,O_Y). The representing equivalence sends a map to the pullback of t.
The polynomial is monic, so the morphism is finite. Its derivative is a unit on
the root scheme because ell and t are units, so the morphism is etale. These
section equivalences give the displayed lifted-Yoneda isomorphism. At n=0 both
abelian sheaves are zero and their set sheaf is represented by Y itself; the
empty base is included. No choice of a comparison at another level is asserted. -/
theorem tateLevelRepresentation (Y : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (n : ℕ) :
    ∃ V : Y.ProEt, IsFinite V.hom ∧ Etale V.hom ∧
      Nonempty ((ProEt.topology Y).uliftYoneda.{u + 1}.obj V ≅
        (sheafCompose (ProEt.topology Y) (forget Ab.{u + 1})).obj
          (tateModuleLevel Y ell n).X) := by sorry

end AlgebraicGeometry.ProEtale.PurityTransport
