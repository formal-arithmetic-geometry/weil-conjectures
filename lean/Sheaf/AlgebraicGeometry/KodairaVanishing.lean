module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing
import Sheaf.DeligneLaumon.BertiniSections
import Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import Sheaf.AlgebraicGeometry.BertiniSmoothMember
import Sheaf.AlgebraicGeometry.KollarSmoothDivisorInjectivity

/-!
# Kodaira vanishing in characteristic zero

Source: Milne, Algebraic Groups, Theorem 22.51 proof, printed page 480;
Popa, Kodaira dimension of algebraic varieties, section 1.6, printed page 22,
Theorem 1.6.1, printed page 23, and its proof, printed pages 27--28.
(blueprint: lem-sfb-kodaira-vanishing)

The canonical module is the top exterior power of relative differentials.
Cohomology is the right derived functor of Zariski module global sections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Kodaira vanishing: tensoring the canonical module of a smooth projective
geometrically integral variety with an ample invertible module kills every
positive Zariski module cohomology group, including in dimension zero.

Source: Popa, Kodaira dimension of algebraic varieties, section 1.6 opening
paragraph, printed page 22, Theorem 1.6.1, printed page 23, and proof using
Theorem 1.6.6, printed pages 27--28. Milne, Algebraic Groups, Theorem 22.51
proof, printed page 480, invokes this theorem.
(blueprint: lem-sfb-kodaira-vanishing)

Proof:
1. Projectivity gives properness (lem-pc-projective-proper). By
   lem-trf-proper-field-invertible-coherent, Y is Noetherian and its structure
   sheaf is coherent. Relative differentials are finite locally free by
   lem-ag-smooth-relative-differentials-finite-locally-free. Locally their
   n-th exterior power has the finite basis of increasing n-tuples of basis
   vectors, with the empty wedge for n = 0. It is therefore coherent by the
   finite-sum closure in lem-weil-pbc-coherent-kernel-cokernel-locnoeth and
   locality of the definition pqf-def-coherent; no rank formula is needed.
2. A field is Noetherian. Apply lem-weil-pbc-coherent-serre-vanishing to this
   exterior power and A, obtaining a bound a for all positive degrees.
   The affine-loci criterion lem-pc-ample-affine-loci-criterion turns the
   absolute ampleness hypothesis into the relative ampleness used by
   lem-zl-bertini-sections. With empty closed subscheme, that lemma gives,
   for all sufficiently large m, generating sections of A to the power m
   whose complete linear system is an immersion. Choose m at least 2 and
   m + 1 at least a. Proper-field coherence and
   lem-pc-projective-coherent-finiteness make this generating space finite
   dimensional; since Y is nonempty it has positive dimension r.
3. Apply lem-zl-bertini-smooth-member to get a nonempty open in affine
   r-space parametrizing smooth zero schemes. Remove the zero vector; the
   open remains nonempty since affine r-space is integral and r is positive.
   Take a nonempty principal open D(g) inside it. A nonzero polynomial over
   the infinite field F is nonzero at some F-valued tuple: induct on r by
   first making a nonzero coefficient nonzero, then avoiding finitely many
   roots in the last variable. This yields a nonzero section s of A to the
   power m whose zero scheme is smooth. Empty zero schemes are allowed.
4. Apply lem-sfb-kollar-smooth-divisor-injectivity with L = A, m and s.
   It embeds H^i of the canonical module tensor A into H^i of the canonical
   module tensor A to the power m + 1, for every i at least zero. Its
   characteristic-zero scope needs no embedding of F into the complex field.
5. For i positive the target is zero by step 2. Injectivity forces every
   element of the source to be zero, giving the asserted vanishing. -/
theorem kodaira_vanishing
    (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of F)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsProjective f] [GeometricallyIntegral f]
    (A : Y.Modules) [A.IsInvertible] (hA : Scheme.Modules.IsAmple Y A)
    (i : ℕ) (hi : 0 < i) :
    IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace i).obj
      (Scheme.Modules.exteriorSheaf f.relativeDifferentials n ⊗ A)) := by
  sorry

end AlgebraicGeometry
