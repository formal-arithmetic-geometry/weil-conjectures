/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.Compactification.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction
import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunctionCore

/-!
# Affine-space ambient adjunction

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/cor-amb-affine-space-adjunction.md
(blueprint: cor-amb-affine-space-adjunction).

Both functors act on the entire ordinary unbounded small-etale derived categories.
The compactification instance comes from the existing relative projective compactification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Ordinary compact supports for affine `d`-space are left adjoint to exact inverse image,
followed by the finite torsion Tate twist `(d)` and cohomological shift `[2d]`.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/cor-amb-affine-space-adjunction.md
(blueprint: cor-amb-affine-space-adjunction).

Proof:
1. Factor affine `r`-space over `S` into the successive affine-line projections, using
   the polynomial-coordinate identifications of `def-sbc-affine-space`. They are separated
   and finite type (`def-weil-finite-type-morphism`, `def-weil-proper-morphism`), so every
   intermediate scheme is Noetherian (`lem-weil-pbc-finite-type-over-noetherian`). Units
   remain units under pullback. The standard affine chart and projective-space properness
   (`lemma-nagata-relative-affine-space-open-immersion` and
   `lemma-nagata-projective-space-base-change-proper`) give compactifications
   (`def-asd-compactifiable`) with Noetherian ambient schemes.
2. The affine-line chart `j` is etale (`lem-weil-pbc-open-immersion-etale`), separated, and
   finite type: on either projective chart its inverse image is the whole chart or a
   principal open. Thus `lem-amb-etale-adjoint-locality` gives `Dj_!` left adjoint to `j^*`
   on the entire unbounded categories. Its extension is ordinary open extension by zero
   by `def-weil-pbc-etale-sum-extension`.
3. For the projective-line projection `q`, compact supports are `Rq_* Dj_!`
   (`def-amb-etale-compact-support`, `lem-amb-unbounded-compact-support-comparisons`).
   Apply `thm-amb-p1-adjunction` and the preceding open adjunction to obtain natural Hom
   bijections with target `j^*(q^*K(1)[2])`. Move the twist through inverse image by
   `lem-asd-etale-finite-twist-pullback`; inverse-image composition and exactness
   (`lem-weil-pbc-inverse-image-composition-module-linear`,
   `prop-weil-pbc-inverse-image-modules-exact`) identify this with `p_1^*K(1)[2]`.
   These are the composite adjunction bijections of `def-weil-pbc-composite-adjunction`.
4. Each nonnegative Tate sheaf is flat (`lem-asd-finite-etale-twist-line`), so tensoring
   a K-flat resolution with it computes ordinary termwise tensor as well as derived
   tensor (`def-kun-derived-tensor`). Regroup the degree-zero Tate factors using
   `def-asd-finite-etale-tate-twist`, with the scalar unit when the exponent is zero.
   These chain isomorphisms are natural. Even shifts have sign one and add, giving
   `(K(r)[2r])(1)[2]` naturally isomorphic to `K(r+1)[2r+2]`, without boundedness.
5. In dimension zero the affine projection is canonically the identity. Compactification
   independence identifies its compact supports with the identity, and the scalar-unit
   and zero-shift identifications identify its right adjoint with the identity. Use the
   identity adjunction (`def-weil-pbc-composite-adjunction`).
6. Induct on `d`. Compose the preceding adjunction with the affine-line adjunction over
   affine `d`-space, using `lem-amb-unbounded-compact-support-comparisons` to identify
   the composite compact supports. Exact inverse-image composition and pullback of
   twists identify the reversed composite right adjoint with `p_(d+1)^*(-)(d+1)[2d+2]`,
   by step 4. Every comparison is natural in both unrestricted derived arguments. -/
theorem nonempty_affineSpaceAmbientAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣
        ((upperStar (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin d)) S ↘ S)).mapDerivedCategory ⋙
          derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) S)
            ((DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) S) N A hA d))) ⋙
          shiftFunctor _ (2 * (d : ℤ))) := by
  let f : AffineSpace (ULift.{u} (Fin d)) S ⟶ S :=
    AffineSpace (ULift.{u} (Fin d)) S ↘ S
  let c : Compactification f :=
    Compactification.ofIsImmersionAffineSpace (𝟙 _) (Category.id_comp _)
  let hcomp : HasCompactification f := c.hasCompactification
  obtain ⟨a⟩ := affineSpaceAmbientAdjunction_of_compactification N hN A hA S hS d c
  exact ⟨a.ofNatIsoLeft (@rightDerivedLowerShriekIso _ _ f A inferInstance inferInstance
    inferInstance hcomp c)⟩

end AlgebraicGeometry.Etale
