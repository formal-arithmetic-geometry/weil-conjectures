module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import Sheaf.AlgebraicGeometry.ClosedImmersionUnboundedProjectionFormula
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.ClosedPushforwardNonpositiveFreeTensor
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded

/-! # Pullback and relative pseudo-coherence

Source: Stacks Project, More on Morphisms, Tag 09US,
`lemma-pull-relative-pseudo-coherent`
(blueprint: lem-sfb-relative-pseudocoherent-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback along a morphism whose structure module is relatively pseudo-coherent
preserves relative `m`-pseudo-coherence over the base. The object is an arbitrary
object of the unbounded structure-module derived category.
Source: Stacks Project, More on Morphisms, Tag 09US,
`lemma-pull-relative-pseudo-coherent`
(blueprint: lem-sfb-relative-pseudocoherent-pullback).

Proof:
1. By lem-sfb-relative-pseudocoherence-all-affine-charts and
   lem-sfb-relative-pseudocoherence-local-on-source, restrict to affine triples X, Y, S.
   Derived pullback composition (lem-pc-ringed-spaces-derived-pullback-composition)
   identifies the restriction of the pullback with the pullback of the restriction.
2. Apply lem-weil-pbc-lft-affine-pairs to choose finite algebra generators. The resulting
   polynomial surjections give closed embeddings i : X → P = affine d-space over Y and
   j : P → W = affine (n+d)-space over S, with h = i followed by the projection p.
   These use def-nagata-relative-affine-space and def-weil-closed-immersion.
3. The all-affine-charts criterion applied in every degree makes Ri_* O_X[0]
   pseudo-coherent on P. Exactness in
   lem-sfb-closed-immersion-unbounded-projection-formula identifies it with i_* O_X[0].
   By lem-pc-affine-pseudo-coherent-criterion its affine module B[0] is pseudo-coherent.
   Apply lem-pc-pseudo-coherent-bounded-finite-free-model with bound zero and then
   lem-pc-affine-qcoh-derived-equivalence to obtain a nonpositive finite free complex F
   representing Ri_* O_X[0].
4. The projection S' = affine d-space over S is flat by
   lem-nagata-polynomial-projection-flat. Since P = Y ×_S S',
   lem-sfb-relative-pseudocoherence-flat-base-change makes Q = Lp^* K relatively
   m-pseudo-coherent over S'. The all-affine-charts criterion for j gives absolute
   m-pseudo-coherence of Rj_* Q on W. No quasi-coherence of K is used.
5. Derived pullback composition and the closed-immersion unbounded projection formula
   identify Ri_* Lh^* K with Q tensor F. Use the unit and symmetry from
   def-pc-scheme-derived-tensor-structure. Now
   lem-sfb-closed-pushforward-nonpositive-free-tensor makes Rj_* (Q tensor F)
   m-pseudo-coherent. By lem-pc-derived-direct-image-composition this is R(ij)_* Lh^* K.
6. The composite closed embedding into W is one of the charts in
   def-sfb-relative-pseudo-coherent-complex. Its conclusion on each affine triple
   therefore assembles, by step 1, to the claimed relative m-pseudo-coherence. -/
theorem isMPseudoCoherentRelativeTo_derivedPullback
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)
    [LocallyOfFiniteType h] [LocallyOfFiniteType (h ≫ f)] [LocallyOfFiniteType f]
    (hOX : IsPseudoCoherentRelativeTo h
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace))))
    (m : ℤ) (K : schemeDerivedCategory Y)
    (hK : IsMPseudoCoherentRelativeTo f m K) :
    IsMPseudoCoherentRelativeTo (h ≫ f) m ((derivedPullback h).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
