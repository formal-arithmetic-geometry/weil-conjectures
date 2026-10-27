/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Connected.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.AlgebraicGeometry.SquareActionGenerationLocusStable
import WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
import Sheaf.AlgebraicGeometry.SquareActionProjImmersionLocusStable
import Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective

/-! # Affine section orbits detect ampleness under the square condition

Source: Guo, Divisors on coherent schemes and homogeneous spaces, section 5.6 and
Corollary 6.5, sufficient direction, affine-locus specialization, printed p.17
(March 31, 2026 version).
(blueprint: lem-sfb-square-action-affine-orbit-criterion)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.Scheme.Modules

/-- If the group translates of the affine positive-power section loci cover the scheme,
then an invertible module satisfying the square condition is absolutely ample.
Source: Guo, section 5.6 and Corollary 6.5, sufficient direction, affine-locus
specialization, printed p.17, March 31, 2026 version.
(blueprint: lem-sfb-square-action-affine-orbit-criterion)

The group and action are objects in `Over S`. For `B : Over S`, `X ⊗ B` is the
chosen fibre product `X ×_S B`, and `(snd X B ≫ g) • fst X B` sends `(x,b)` to
`g(b)x`. Its tensor pullback of `M` is canonically `τ_g^* M_B` by composition.
The square hypothesis requires only an invertible base module and existence of an
isomorphism, with no chosen isomorphisms or coherence. The open `U` is exactly the
union of the affine nonvanishing loci, as specified by `hU`. The preimage under the
second projection is the underlying open of `H ×_S U`, so `horbit` uses all its points.

Proof plan:
1. Finite presentation over the affine base makes X quasi-compact. Separatedness
   over an affine base gives absolute separatedness
   (lem-sc-separated-over-affine-scheme-separated), hence quasi-separatedness
   (lem-pc-separated-quasi-separated). Cancelling M in the square identity gives
   additivity of translation differences modulo modules pulled back from B.
2. Let E be the union of all positive-power section loci, including nonaffine ones.
   By lem-sfb-square-action-generation-locus-stable, H·E = E. Since U is contained
   in E and H·U = X, E = X; hence these section loci cover X.
3. Apply lem-sc-ample-proj-canonical-map to construct r : X → Proj Γ_*(X,M),
   with inverse images X_s and the fraction formula on every standard chart.
   Let P₀ be its target-open immersion locus and W = r⁻¹(P₀).
   The cover from step 2 lets lem-sfb-square-action-proj-immersion-locus-stable
   give H·W = W and ampleness on every quasi-compact open contained in W.
4. If X_s is affine, the chart ring map is bijective by
   lem-sc-section-ring-localization-bijective, using qcqs from step 1 and the
   fraction formula from step 3. By def-pc-proj the chart D_+(s) is affine;
   lem-sc-affine-global-sections-iso makes X_s → D_+(s) an isomorphism.
   Since r⁻¹(D_+(s)) = X_s, this chart belongs to P₀ and X_s is contained in W.
   Taking the union yields U ⊆ W.
5. Thus X = H·U ⊆ H·W = W ⊆ X. Apply the last clause of
   lem-sfb-square-action-proj-immersion-locus-stable to the quasi-compact open
   T = X = W to obtain absolute ampleness. -/
theorem squareAction_affine_orbit_criterion
    (S : Scheme.{u}) [IsAffine S]
    (H : Over S) [GrpObj H] [Smooth H.hom] [IsSeparated H.hom]
    [LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom]
    (hconnected : ∀ s : S, ConnectedSpace (H.hom.fiber s))
    (X : Over S) [IsSeparated X.hom] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom] [ModObj H X]
    (M : X.left.Modules) [M.IsInvertible]
    (hsquare : ∀ (B : Over S) (g h : B ⟶ H),
      ∃ N : B.left.Modules, N.IsInvertible ∧
        Nonempty
          (((tensorPullback (((snd X B ≫ (g * h)) • fst X B).left)).obj M ⊗
            (tensorPullback (fst X B).left).obj M) ≅
           (((tensorPullback (((snd X B ≫ g) • fst X B).left)).obj M ⊗
             (tensorPullback (((snd X B ≫ h) • fst X B).left)).obj M) ⊗
            (tensorPullback (snd X B).left).obj N)))
    (U : X.left.Opens)
    (hU : ∀ x : X.left, x ∈ U ↔
      ∃ (n : ℕ) (_ : 0 < n)
        (s : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤)) (V : X.left.Opens),
        IsAffineOpen V ∧ (V : Set X.left) = nonvanishingLocus (M.tensorPow n) s ∧ x ∈ V)
    (horbit : Set.image (γ[H, X].left.base)
      ((snd H X).left.base ⁻¹' (U : Set X.left)) = Set.univ) :
    IsAmple X.left M := by
  sorry

end AlgebraicGeometry.Scheme.Modules
