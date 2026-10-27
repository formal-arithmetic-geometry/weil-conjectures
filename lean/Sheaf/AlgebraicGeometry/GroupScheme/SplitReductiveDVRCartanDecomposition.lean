module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.CompletionOfDVR
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Cartan decomposition over an arbitrary DVR

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto decompositions,
Theorem 4.1 and Remark 4.2, p.7, and Remark 3.5, p.5
(blueprint: lem-sfb-split-reductive-dvr-cartan-decomposition).

An L-point of the generic fibre is expressed, by the pullback universal property,
as an R-morphism Spec L → D. Integral points restrict by precomposition with the
unique map to Spec R. Thus the displayed equality uses the canonical inclusions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every generic point factors through two integral points and the given split
maximal torus, without assuming completeness or local compactness.

Source: AHLH, Theorem 4.1 and Remark 4.2, p.7, Remark 3.5, p.5
(blueprint: lem-sfb-split-reductive-dvr-cartan-decomposition).

Proof plan:
1. Choose a uniformizer pi. The completion is a DVR by
   lem-weil-pbc-completion-of-dvr-is-dvr. Its maximal ideal, residue field and
   quotient comparisons follow from lem-weil-pbc-local-completion-local-ring and
   lem-weil-pbc-module-completion-complete. Using
   lem-weil-pbc-dvr-unit-times-uniformizer-power shows R embeds in its completion
   and L intersects the completed ring in precisely R inside its fraction field.
2. Base change D and T to the completion. Smoothness and finite type persist by
   lem-pc-proper-base-change and lem-sfb-finite-type-composition-base-change;
   affineness follows from lem-weil-pbc-fibre-product-affine-spectra. The group
   diagrams, closed torus and geometric fibre conditions persist. Apply
   lem-sfb-complete-dvr-cocharacter-cartan and then
   lem-sfb-complete-dvr-torus-cocharacter-conjugacy, absorbing the conjugating
   integral elements, to obtain g = a nu(pi) b.
3. Under the split coordinates, a group-like Laurent polynomial over the completed
   domain is a single monomial: its coefficients are orthogonal idempotents with
   sum one. Hence nu has integral exponent coordinates and descends to R.
   Put t = nu(pi) in T(L); for rank zero this is the identity.
4. Write D = Spec A with finitely many generators x_j, using
   def-weil-affine-spectrum and def-weil-finite-type-morphism. The generic ring is
   A[1/pi] by lem-weil-pbc-fibre-product-affine-spectra. Write the conjugation
   pullbacks x_j(t h t⁻¹) as y_j/pi^m_j. If e is congruent to one modulo pi^N
   with N larger than every m_j, all these evaluations are integral. Thus
   t e t⁻¹ lies in the completed integral group.
5. By lem-sfb-split-reductive-local-quotient-points lift b modulo pi^N to an
   integral point k. Then e = b k⁻¹ is congruent to one. Set
   h = a (t e t⁻¹) = g k⁻¹ t⁻¹; it is completed-integral and L-rational.
6. The affine coordinate map of h takes values in the intersection of L and the
   completed ring, namely R, so h is integral by def-weil-affine-spectrum.
   Consequently g = h t k. Completion was auxiliary only. -/
theorem splitReductive_dvr_cartan_decomposition
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (L : Type u) [Field L] [Algebra R L] [IsFractionRing R L]
    (D T : Grp (Over (Spec (.of R))))
    [Smooth D.X.hom] [IsAffine D.X.left]
    [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    (i : T ⟶ D) [IsClosedImmersion i.hom.hom.left]
    (r : ℕ) (e : T ≅ RingGroupSchemes.splitTorus R r)
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : R →+* Ω),
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj D))
    (hmax : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : R →+* Ω),
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map i))
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ D.X) :
    ∃ (k₁ k₂ : 𝟙_ (Over (Spec (.of R))) ⟶ D.X)
      (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ T.X),
      g = (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L)))) ≫ k₁) *
        (t ≫ i.hom.hom) *
        (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L)))) ≫ k₂) := by
  sorry

end AlgebraicGeometry
