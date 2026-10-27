/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.FlatInertiaAlgebraicSpaceQuotient
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Smooth relative Picard spaces of families of curves

Source: Stacks Project, quot.tex, Tags 0D2C and 0D2D; moduli.tex, Tags 0DNI and 0DPK
(blueprint: lem-sfb-picard-space-curves-smooth).

The small group functor underlying the algebraic space is identified, after the standard
universe lift, with the existing group-valued relative Picard functor. Thus its group law
is the sheafification of tensor product, rather than an unspecified group structure.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The relative Picard fppf sheaf of a proper flat finitely presented family with fibres
of dimension at most one and universally trivial structure-sheaf pushforward is a smooth,
quasi-separated commutative group algebraic space, locally of finite presentation, with
representable immersion diagonal.
Source: Stacks Project, quot.tex, Tags 0D2C and 0D2D; moduli.tex, Tags 0DNI and 0DPK
(blueprint: lem-sfb-picard-space-curves-smooth).

Proof:
1. By lem-sfb-picard-stack-curve-geometry, the stack of invertible modules on C_T,
   retaining their automorphisms, is algebraic and smooth over S. Properness, flatness
   and finite presentation give algebraicity, and the fibre bound gives smoothness.
2. Local trivializations identify an automorphism of a line module with a global unit
   on C_T. The universal structure-sheaf isomorphism identifies these with units on T,
   so the inertia projection is the multiplicative group over each object. Its affine
   presentation is A[z,w]/(zw-1). Lift a unit and its inverse through a square-zero
   extension to a,b with ab=1+i; then b(1-i) is inverse to a. Thus inertia is formally
   smooth and finitely presented, hence smooth, flat and locally finitely presented
   by def-sbc-smooth-morphisms and lem-sfb-stack-chartwise-smooth-etale-calculus.
3. Apply lem-sfb-flat-inertia-algebraic-space-quotient to get a smooth algebraic-space
   quotient Q. By lem-cbc-set-presheaf-sheafification-local-bijection and the
   sheafification adjunction, sections of Q locally have line-module representatives,
   and equality is local equality of their classes. Base line modules are Zariski
   locally trivial, so quotienting Pic(C_T) by their pullbacks has the same fppf
   sheafification. Hence Q is picardFunctor f. Smooth scheme charts are locally of
   finite presentation. Small section sets supply the small sheaf underlying P.
4. Tensor product, the trivial module and duality commute with pullback. Apply them
   to local representatives on a common fppf refinement. Independence and the group
   identities hold locally, hence glue uniquely. This produces the commutative group
   functor G and its natural group isomorphism with picardFunctorGrp f.
5. Given two sections on a scheme T, represent them fppf locally by V,W and put
   L=V tensor W-dual. Properness, flatness and finite presentation persist by
   lem-sfb-space-flat-proper-fp-locality, as does the universal structure-sheaf
   hypothesis. Apply lem-sc-picard-diagonal-locally-closed to L to get a finitely
   presented immersion representing the locus where L comes from a finite locally
   free base module N. Each fibre is nonempty, since its global functions equal
   its nonzero residue field. Thus N has rank one. By lem-pc-pic-exact the locus
   represents equality of the Picard sections on every test scheme, including
   nonreduced ones.
6. The local equality immersions are quasi-compact by finite presentation. Apply
   lem-sfb-space-quasi-compact-immersion-locality to descend them to a quasi-compact
   immersion over T, including representability by a scheme. These are precisely
   the scheme tests of the diagonal, giving both its immersion property and its
   quasi-compactness, which is quasi-separatedness over S. -/
theorem picard_space_curves_smooth {C S : Scheme.{u}} (f : C ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ (1 : WithBot ℕ∞))
    (hO : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf))) :
    ∃ (P : AlgebraicSpace S) (G : (Over S)ᵒᵖ ⥤ CommGrpCat.{u}),
      G ⋙ forget CommGrpCat = P.obj.obj ∧
      Nonempty (G ⋙ forget₂ CommGrpCat GrpCat ⋙ GrpCat.uliftFunctor.{u + 1, u} ≅
        picardFunctorGrp f) ∧
      (∀ (U : Over S) (a : yoneda.obj U ⟶ P.obj.obj),
        AlgebraicSpace.IsEtale a → Smooth U.hom ∧ LocallyOfFinitePresentation U.hom) ∧
      AlgebraicSpace.IsRepresentableWith
        (fun _ _ p ↦ QuasiCompact p.left ∧ IsImmersion p.left)
        (prod.lift (𝟙 P.obj.obj) (𝟙 P.obj.obj)) := by
  sorry

end AlgebraicGeometry
