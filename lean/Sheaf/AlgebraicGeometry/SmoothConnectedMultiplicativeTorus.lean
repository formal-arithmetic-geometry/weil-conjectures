module

public import Sheaf.AlgebraicGeometry.RelativeMultiplicativeType
public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.LinearAlgebra.FreeModule.PID
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Smooth multiplicative-type groups with connected geometric fibres are tori

Source: Conrad, Reductive group schemes, Appendix B, Proposition B.3.4 and its
character-sheaf description of tori; Milne, Algebraic Groups (2017), Examples 12.1--12.2,
Proposition 12.3 and Remark 12.5, printed pp.231--232.
(blueprint: lem-sfb-smooth-connected-multiplicative-torus).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth finitely presented group of multiplicative type with connected whole
geometric fibres is an fppf-local product of finitely many copies of G_m.
The ranks may vary and zero rank and empty, disconnected or nonreduced bases are allowed.

Source: Conrad, Reductive group schemes, Appendix B, Proposition B.3.4 and the
character-sheaf description of tori; Milne, Examples 12.1--12.2, Proposition 12.3 and
Remark 12.5, printed pp.231--232
(blueprint: lem-sfb-smooth-connected-multiplicative-torus).

Proof following the accepted split:
1. Choose the fppf splitting cover and discard empty members (def-pc-fppf-site).
   On one affine member Spec R, P is D_R(M) for a finitely generated abelian M
   (def-sfb-ring-diagonalizable-group). Choose a geometric point there using
   def-weil-algebraic-closure and def-weil-geometric-point. The affine pullback formula
   lem-weil-pbc-fibre-product-affine-spectra and the tensor universal property
   lem-weil-pbc-algebra-tensor-pushout-universal-property identify its whole geometric
   fibre with Spec Ω[M]: a tensor times a basis monomial maps to the corresponding
   monomial with the multiplied coefficient; the inverse sends a monomial to its tensor.
2. By sbc-lem-smooth-geometrically-reduced this fibre is reduced, hence Ω[M] is reduced
   by lem-weil-pbc-affine-scheme-reduced-iff. If an element m of order n has n divisible
   by the positive characteristic p, a = (n/p)m has order p. The basis element
   difference e_a - e_0 is nonzero but its p-th power is zero, a contradiction.
3. Any remaining torsion element m of order n > 1 has n invertible in Ω. The element
   b = (1/n) sum_{j=0}^{n-1} e_(jm) is an idempotent different from zero and one:
   each residue class appears n times in the product, and the monomials are distinct.
   By lem-weil-pbc-spec-clopen-idempotent it gives two nonempty complementary clopens,
   contradicting the assumed connectedness (def-weil-connected-scheme). Thus M is
   torsion-free. This concerns the entire geometric fibre, not its identity component.
4. By lem-trf-fg-torsionfree-group-free choose a finite integral basis of M. The inverse
   algebra maps between B[M] and the rank-r Laurent polynomial algebra send e_(sum n_j b_j)
   to the product of x_j^n_j and back. They preserve all Hopf operations and restrictions.
   The affine-spectrum construction (def-weil-affine-spectrum) gives inverse group maps;
   lem-a1-locally-ringed-space-affine-adjunction identifies their point functor with
   r-tuples of units of global functions. This identifies the split model with G_m^r
   on every covering member and gives IsRelativeTorus. Rank zero is the empty product;
   for the empty base the empty cover suffices. -/
theorem smooth_connected_multiplicativeType_isRelativeTorus
    {S : Scheme.{u}} (P : Grp (Over S))
    [LocallyOfFinitePresentation P.X.hom] [QuasiCompact P.X.hom]
    (hP : IsRelativeMultiplicativeType P) [Smooth P.X.hom]
    (hconn : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S), ConnectedSpace (pullback P.X.hom s : Scheme.{u})) :
    IsRelativeTorus P.X := by
  sorry

end AlgebraicGeometry
