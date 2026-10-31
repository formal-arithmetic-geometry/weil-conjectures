/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
import WeilConjectures.AlgebraicGeometry.FlatInertiaAlgebraicSpaceQuotient
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.AlgebraicGeometry.PicardDiagonalLocallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The relative Picard algebraic space of a flat proper family

Source: Stacks Project, quot.tex, Tags 0D2C and 0D2D; local finite presentation
from Tags 08KD, 0D03 and 04AK
(blueprint: lem-sfb-flat-proper-picard-algebraic-space).

The algebraic space has small section sets. Its commutative-group-valued functor
of points, lifted one universe, is identified with the existing relative Picard
group functor. This identification specifies tensor product, the trivial module
and dualization, and identifies the underlying sheaf with `picardFunctor f`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A flat proper finitely presented family with universally trivial structure-sheaf
pushforward has a locally finitely presented relative Picard algebraic space with
immersion diagonal and its canonical commutative group law.
Source: Stacks Project, quot.tex, Tags 0D2C and 0D2D; Tags 08KD, 0D03 and 04AK
(blueprint: lem-sfb-flat-proper-picard-algebraic-space).

Proof:
1. The coherent-module stack is algebraic and locally finitely presented by
   lem-sfb-coherent-stack-algebraic-lfp. Invertible modules form its representable
   open substack by lem-sfb-invertible-open-in-coherent-stack. Thus the Picard
   stack is algebraic and locally finitely presented by lem-sfb-open-stack-algebraic-lfp.
2. Scalar multiplication identifies the automorphisms of any line module on X_T
   with Gamma(X_T,O)^times. The hypothesis identifies these with Gamma(T,O)^times.
   Hence inertia is G_m,T. It is finitely presented; a unit and its inverse lift
   across a square-zero extension, since (1+i)(1-i)=1. Therefore it is smooth,
   flat and locally finitely presented (lem-sfb-stack-chartwise-smooth-etale-calculus).
3. Apply lem-sfb-flat-inertia-algebraic-space-quotient. The quotient sheaf is
   picardFunctor f by def-pc-picard-functor. Local representatives and local
   equality from lem-weil-pbc-site-sheafification-sections-local make the Picard
   stack a gerbe over it. A smooth atlas gives a flat locally finitely presented
   surjection to this quotient by lem-sfb-gerbe-smooth-universal-homeomorphism.
   Descent by lem-sfb-representable-fppf-etale-open-descent gives local finite
   presentation of the quotient over S. Its small section sets give P.
4. Tensor product, the trivial module and dualization descend on local bundle
   representatives and commute with restriction. The group identities hold
   locally and hence in the sheaf. This gives G and its group-valued natural
   isomorphism with the already defined picardFunctorGrp f.
5. Represent two test sections locally by V and W and apply
   lem-sc-picard-diagonal-locally-closed to V tensor W-dual. Flatness, properness
   and finite presentation persist by lem-sfb-space-flat-proper-fp-locality.
   The universal structure-sheaf hypothesis persists too. The resulting finite
   locally free module on the base has rank one: every geometric fibre is
   nonempty since its global functions are its nonzero base field. By
   lem-pc-pic-exact, this immersion represents equality of the two Picard sections
   on every test scheme, including nonreduced schemes.
6. These finite-presentation immersions are quasi-compact. Apply
   lem-sfb-space-quasi-compact-immersion-locality to descend them, including
   their scheme representability. Every scheme test of the diagonal is such
   an equality functor, so the diagonal is representable by immersions. -/
theorem flat_proper_picard_algebraic_space {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf))) :
    ∃ (P : AlgebraicSpace S) (G : (Over S)ᵒᵖ ⥤ CommGrpCat.{u}),
      G ⋙ forget CommGrpCat = P.obj.obj ∧
      Nonempty (G ⋙ forget₂ CommGrpCat GrpCat ⋙ GrpCat.uliftFunctor.{u + 1, u} ≅
        picardFunctorGrp f) ∧
      (∀ (U : Over S) (a : yoneda.obj U ⟶ P.obj.obj),
        AlgebraicSpace.IsEtale a → LocallyOfFinitePresentation U.hom) ∧
      AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
        (prod.lift (𝟙 P.obj.obj) (𝟙 P.obj.obj)) := by
  sorry

end AlgebraicGeometry
