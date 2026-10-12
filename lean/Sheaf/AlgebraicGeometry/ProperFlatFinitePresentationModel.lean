/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel
import Sheaf.AlgebraicGeometry.AffineFlatConnectiveTruncation
import Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel

/-! # Finite-presentation flat models on a fixed affine base -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A proper flat finitely presented module has a bounded, nonnegative model with
finitely presented flat quasi-coherent terms on any specified affine open of the base.
The upper bound is not prescribed, and no input cohomology model is required.
Source: Stacks Project, https://stacks.math.columbia.edu/tag/0B91, part (2),
with Tag 0A1H (Noetherian approximation) and Tag 08EB (affine perfect models).
(blueprint: lem-pc-proper-flat-finite-presentation-model).

Proof:
1. Restrict f and F by the cartesian square over U. Properness, finite presentation,
   and relative flatness survive base change. Apply Tag 0B91(2): the derived direct
   image K on U is perfect and commutes with every base change. Its proof, Tag 0A1H,
   descends the morphism and the finitely presented flat module to a Noetherian stage,
   applies proper coherence there, and pulls the perfect direct image back to U.
2. Write U = Spec A via its canonical affine isomorphism. Tag 08EB gives a bounded
   finite-projective A-complex representing K. The derived fibres are the cohomology
   of a sheaf in degree zero, so vanish in negative degrees. The residue-field
   Tor-amplitude criterion (Tag 068V) gives lower Tor bound zero. Truncate a finite
   free resolution at degree zero: its degree-zero opcycle is finitely presented
   and flat, hence finite projective. Cancel the exact upper tail to obtain a
   finite-projective representative in [0,b], enlarging b to a natural number.
3. Associate sheaves termwise and transport to U. Finite projective modules give
   finitely presented, flat, quasi-coherent sheaves. Bounded flat complexes compute
   derived pullback by ordinary pullback. Compose with derived base change and
   take homology to obtain the comparison with higher direct images. For arbitrary
   cartesian squares transport the standard fibre-product calculation through their
   canonical isomorphism. The comparison is global for nonaffine new bases, since
   it comes from derived base change. For an empty U or empty inverse image use the
   zero complex with b = 0. -/
theorem exists_proper_flat_finitePresentation_model {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme) :
    ∃ (B : CochainComplex U.toScheme.Modules ℤ) (b : ℕ),
      B.IsStrictlyGE 0 ∧ B.IsStrictlyLE b ∧
      (∀ n : ℤ, (B.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (B.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (B.X n).IsFinitePresentation) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj B).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by
  obtain ⟨C, a, b, hCge, hCle, hCflat, hCqc, hCfp, hneg, hcompare⟩ :=
    exists_proper_flat_boundedPresentation_model f F hF U hU
  obtain ⟨hBflat, hBqc, hBfp, htrunc⟩ :=
    affine_flat_connective_truncation U.toScheme hU C a b hCge hCle
      hCflat hCqc hCfp hneg
  have : C.IsStrictlyLE (b : ℤ) := hCle
  have hBle : (C.truncGE 0).IsStrictlyLE (b : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have hi0 : (0 : ℤ) < i := lt_of_le_of_lt (Int.natCast_nonneg b) hi
    exact (C.isZero_of_isStrictlyLE b i hi).of_iso (C.truncGEXIso 0 i hi0)
  refine ⟨C.truncGE 0, b, inferInstance, hBle, hBflat, hBqc, hBfp, ?_⟩
  intro T' X' g g' f' _ hsquare q
  obtain ⟨e⟩ := htrunc g q
  obtain ⟨e'⟩ := hcompare g g' f' hsquare q
  exact ⟨e ≪≫ e'⟩

end AlgebraicGeometry.Scheme.Modules
