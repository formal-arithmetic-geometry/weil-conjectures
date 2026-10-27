/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Restriction of a derived Chow transform

Source: Stacks Project, More on Morphisms of Spaces, Tag 0CTS,
lemma-compute-Fourier-Mukai-for-derived-chow
(blueprint: lem-sfb-space-derived-chow-transform-restriction).

The projective space and its open inclusion are the usual representable sheaves.
The functors use the fixed small ringed models, K-flat pullback and tensor, and
K-injective direct image. The conclusion is a natural isomorphism on D_QCoh(X).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Projective n-space over Spec A, with n+1 homogeneous coordinates.
Source: Stacks Project, Tag 0CTS
(blueprint: lem-sfb-space-derived-chow-transform-restriction). -/
def chowProjectiveSpace (A : CommRingCat.{u}) (n : ℕ) : Over (Spec A) :=
  Over.mk (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec A) ↘ Spec A)

/-- The open V of projective space, retaining its structure morphism to Spec A.
Source: Stacks Project, Tag 0CTS
(blueprint: lem-sfb-space-derived-chow-transform-restriction). -/
def chowProjectiveOpen (A : CommRingCat.{u}) (n : ℕ)
    (V : (chowProjectiveSpace A n).left.Opens) : Over (Spec A) :=
  Over.mk (V.ι ≫ (chowProjectiveSpace A n).hom)

/-- The actual Yoneda map of the open immersion V into projective space.
Source: Stacks Project, Tag 0CTS
(blueprint: lem-sfb-space-derived-chow-transform-restriction). -/
def chowProjectiveOpenInclusion (A : CommRingCat.{u}) (n : ℕ)
    (V : (chowProjectiveSpace A n).left.Opens) :
    schemeSpace (chowProjectiveOpen A n V) ⟶ schemeSpace (chowProjectiveSpace A n) :=
  ObjectProperty.homMk ⟨yoneda.map (Over.homMk V.ι)⟩

/-- Restriction of a Chow kernel computes the direct image from the étale chart,
naturally in every unbounded complex with quasi-coherent cohomology. Since b_W is
étale, its derived tensor pullback in the right side is exactly ordinary restriction.
The cartesian square for W says W = (h followed by q)^{-1}(V); its closed immersion
j into the scheme V also shows that W is a scheme.
Source: Stacks Project, Tag 0CTS, displayed isomorphism and its proof
(blueprint: lem-sfb-space-derived-chow-transform-restriction).

Proof:
1. Set T_V = X times_A V. Base change of h gives a closed immersion i:W -> T_V.
   It is affine and qcqs by def-sfb-space-closed-subspace and def-weil-closed-immersion.
2. Apply lem-sfb-space-derived-etale-chart-calculus to localize Rq_* over V.
   Restriction preserves K-flat representatives by lem-sfb-ringed-site-restriction-kflat,
   identifying the restricted tensor and the restricted derived pullback with those on T_V.
3. The kernel restriction and lem-trf-space-etale-module-pushforward-restriction identify
   the second factor with (i_* O_W)[0]. Derived pullback preserves quasi-coherent
   cohomology by lem-sfb-space-derived-etale-chart-calculus, and O_W is quasi-coherent.
4. By lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives,
   take a bounded-below injective resolution of O_W[0]. It is K-injective by
   lem-weil-pbc-bounded-below-injectives-kinjective. The theorem
   lem-sfb-space-affine-module-higher-image-vanishing and left exactness identify
   Ri_* O_W[0] with (i_* O_W)[0], including in negative degrees.
5. Apply lem-sfb-space-qcqs-derived-projection-formula to i and Lp_V^*K, using the
   symmetry and unit of lem-sf-ringed-derived-closed-symmetric-monoidal. The inner
   object becomes Ri_* Li^* Lp_V^*K.
6. Derived composition identifies this with Rj_* Lb_W^*K. The étale hypothesis
   identifies Lb_W^* with restriction. Localization, the kernel comparison, tensor,
   projection formula and composition are all natural in K, giving the natural iso. -/
theorem derived_chow_transform_restriction (A : CommRingCat.{u}) (n : ℕ)
    [∀ Y : AlgebraicSpace (Spec A), HasDerivedCategory.{w} Y.SmallModules]
    (X T Z : AlgebraicSpace (Spec A))
    (s : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A))))
    (_hsep : MapIsSeparated s) (_hqc : MapIsQuasiCompact s.hom.hom)
    (_hqs : MapIsQuasiCompact (Limits.pullback.diagonal s.hom.hom))
    (_hlfp : MapIsLocallyOfFinitePresentation s)
    (p : T ⟶ X) (q : T ⟶ schemeSpace (chowProjectiveSpace A n))
    (_hT : IsLimit (BinaryFan.mk p q)) (h : Z ⟶ T)
    (_hh : IsRepresentableWith (fun _ _ k ↦ IsClosedImmersion k.left) h.hom.hom)
    (V : (chowProjectiveSpace A n).left.Opens)
    (T_V : AlgebraicSpace (Spec A)) (a : T_V ⟶ T)
    (q_V : T_V ⟶ schemeSpace (chowProjectiveOpen A n V))
    (_hTV : IsPullback a q_V q (chowProjectiveOpenInclusion A n V))
    (W : AlgebraicSpace (Spec A)) (wZ : W ⟶ Z)
    (j : W ⟶ schemeSpace (chowProjectiveOpen A n V))
    (_hW : IsPullback wZ j (h ≫ q) (chowProjectiveOpenInclusion A n V))
    (_hj : IsRepresentableWith (fun _ _ k ↦ IsClosedImmersion k.left) j.hom.hom)
    (_hbW : IsEtale (wZ ≫ h ≫ p).hom.hom)
    (E : T.DerivedQCoh)
    (_hE : Nonempty ((derivedTensorPullback a).obj E.obj ≅
      (derivedTensorPullback a).obj ((DerivedCategory.singleFunctor T.SmallModules 0).obj
        ((smallModuleDirectImage h).obj (SheafOfModules.unit Z.smallStructureRings))))) :
    Nonempty
      ((X.derivedQCohProperty.ι ⋙ derivedTensorPullback p ⋙
          (Functor.curry.obj T.derivedDualityModel.closed.tensor).flip.obj E.obj ⋙
          derivedDirectImage q ⋙ derivedTensorPullback (chowProjectiveOpenInclusion A n V)) ≅
        (X.derivedQCohProperty.ι ⋙ derivedTensorPullback (wZ ≫ h ≫ p) ⋙
          derivedDirectImage j)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
