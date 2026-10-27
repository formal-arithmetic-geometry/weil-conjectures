module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Noetherian.Defs

/-! # Lifting cocharacters over a complete discrete valuation ring

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto decompositions,
Lemma 3.6, proof of (2) implies (1), printed p.6
(blueprint: lem-sfb-complete-dvr-cocharacter-lifting).

The special fibre of the multiplicative group is represented by its actual pullback,
with the induced group law. Thus reduction of a homomorphism is a literal application
of the group-object pullback functor, without choosing a comparison isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every cocharacter of the special fibre of a smooth affine finite-type group
scheme over a complete DVR lifts, with equality on the special fibre.

Source: Alper--Halpern-Leistner--Heinloth, Lemma 3.6, printed p.6; Conrad,
Reductive Group Schemes, Corollary B.3.5, pp.292--293, rank-one specialization
(blueprint: lem-sfb-complete-dvr-cocharacter-lifting).

Proof:
1. The DVR is local and principal, hence Noetherian (def-sc-discrete-valuation-ring,
   def-weil-pbc-noetherian-ring). Its maximal ideal is (pi), whose nth power is (pi^n).
   The stated completeness therefore is maximal-ideal completeness, in the sense of
   def-weil-pbc-adic-completion, with residue field A/(pi).
2. Smoothness gives locally finite presentation (def-sbc-smooth-morphisms).
   Affineness gives quasi-compactness and quasi-separatedness by
   lem-weil-pbc-affine-morphism-permanence, hence finite presentation by
   def-sbc-locally-finite-presentation.
3. Apply lem-sfb-complete-local-split-torus-hom-lift at rank one. Its torus
   Spec A[x,y]/(xy-1) is canonically isomorphic to Spec A[z,z^-1] by x -> z,
   y -> z^-1, with inverse z -> x, z^-1 -> y. These maps preserve the Hopf
   comultiplication, counit and inverse and commute with reduction. Transport
   lambda0 to this torus, lift it, and compose with the isomorphism. Reduction
   is exactly lambda0. No reductivity, connectedness, perfection or injectivity
   hypothesis is used. -/
theorem completeDvr_cocharacter_lifting
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (pi : A) (hpi : IsLocalRing.maximalIdeal A = Ideal.span ({pi} : Set A))
    [IsAdicComplete (Ideal.span ({pi} : Set A)) A]
    (H : Grp (Over (Spec (.of A))))
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (lambda0 :
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span ({pi} : Set A)))))).mapGrp.obj
          (RingGroupSchemes.multiplicative A) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span ({pi} : Set A)))))).mapGrp.obj H) :
    ∃ lambda : RingGroupSchemes.multiplicative A ⟶ H,
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span ({pi} : Set A)))))).mapGrp.map lambda = lambda0 := by
  sorry

end AlgebraicGeometry
