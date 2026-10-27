/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceHigherDirectImageQuasiCoherent
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.CategoryTheory.RingedSiteLeraySpectralSequence
import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
import Sheaf.AlgebraicGeometry.SpaceChartLimitEnlargedSections

/-! # Affine-base cohomology and sections of higher direct images

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 08EX,
lemma-quasi-coherence-higher-direct-images-application, with V equal to the affine base
(blueprint: lem-sfb-space-affine-base-higher-image-sections).

Both derived functors are computed by injective resolutions in all module sheaves.
The restriction equivalence with the small affine model changes neither coefficients
nor the ringed topos. The cocycle equation specifies the canonical Leray edge.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (A : Type u) [CommRing A]
  (Y : Over S) (a : Y.left ≅ Spec (.of A))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)

/-- Module cohomology, restricted to quasi-coherent inputs only after right derivation
in all modules. Source: Stacks 08EX
(blueprint: lem-sfb-space-affine-base-higher-image-sections). -/
abbrev affineBaseModuleCohomology (q : ℕ) : X.QCoh ⥤ ModuleCat.{u} A :=
  (SheafOfModules.isQuasicoherent X.structureSheaf).ι ⋙ X.smallModuleRestriction ⋙
    (affineScalarSections A Y a X f).rightDerived q

/-- Sections of the module higher direct image, computed in all modules.
Source: Stacks 08EX (blueprint: lem-sfb-space-affine-base-higher-image-sections). -/
abbrev affineBaseHigherImageSections (q : ℕ) : X.QCoh ⥤ ModuleCat.{u} A :=
  (SheafOfModules.isQuasicoherent X.structureSheaf).ι ⋙ X.smallModuleRestriction ⋙
    (smallModuleDirectImage f).rightDerived q ⋙
      affineScalarSections A Y a (schemeSpace Y) (𝟙 _)

/-- The complex of global sections of a module resolution.
Source: Stacks 08EX (blueprint: lem-sfb-space-affine-base-higher-image-sections). -/
abbrev affineBaseSectionsComplex (P : CochainComplex X.SmallModules ℕ) :=
  ((affineScalarSections A Y a X f).mapHomologicalComplex (.up ℕ)).obj P

/-- The direct-image complex of a module resolution, retaining the canonical chart limits.
Source: Stacks 08EX (blueprint: lem-sfb-space-affine-base-higher-image-sections). -/
abbrev affineBaseImageComplex (P : CochainComplex X.SmallModules ℕ) :=
  ((smallModuleDirectImage f).mapHomologicalComplex (.up ℕ)).obj P

/-- The canonical comparison sends a global cocycle to its section of the cohomology
sheaf. The formula is imposed on every injective resolution, so it also fixes resolution
independence. Source: Stacks 08EX, via the Leray edge in Tags 0732 and 0733
(blueprint: lem-sfb-space-affine-base-higher-image-sections). -/
def AffineBaseHigherImageSectionsNormalization
    (e : ∀ q : ℕ, affineBaseModuleCohomology A Y a X f q ≅
      affineBaseHigherImageSections A Y a X f q) : Prop :=
  ∀ (q : ℕ) (M : X.QCoh) (I : InjectiveResolution (X.smallModuleRestriction.obj M.obj)),
    ∃ c : (affineScalarSections A Y a (schemeSpace Y) (𝟙 _)).obj
          ((affineBaseImageComplex Y X f I.cocomplex).cycles q) ⟶
        (affineBaseSectionsComplex A Y a X f I.cocomplex).cycles q,
      c ≫ (affineBaseSectionsComplex A Y a X f I.cocomplex).iCycles q =
        (affineScalarSections A Y a (schemeSpace Y) (𝟙 _)).map
            ((affineBaseImageComplex Y X f I.cocomplex).iCycles q) ≫
          (affineSectionsComposition A Y a X f).inv.app (I.cocomplex.X q) ∧
      c ≫ (affineBaseSectionsComplex A Y a X f I.cocomplex).homologyπ q ≫
          (I.isoRightDerivedObj (affineScalarSections A Y a X f) q).inv ≫
          (e q).hom.app M ≫
          (affineScalarSections A Y a (schemeSpace Y) (𝟙 _)).map
            (I.isoRightDerivedObj (smallModuleDirectImage f) q).hom =
        (affineScalarSections A Y a (schemeSpace Y) (𝟙 _)).map
          ((affineBaseImageComplex Y X f I.cocomplex).homologyπ q)

/-- Over an arbitrary affine base, module cohomology is canonically and naturally
isomorphic to sections of the higher module direct image.
Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 08EX,
lemma-quasi-coherence-higher-direct-images-application, V=T
(blueprint: lem-sfb-space-affine-base-higher-image-sections).

Proof:
1. By lem-sfb-space-higher-direct-image-quasi-coherent, every R^b f_* M is
quasi-coherent: the two hypotheses below are precisely quasi-compactness and
quasi-separatedness. No properness or finite presentation is used.
2. By lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
lem-sc-etale-affine-qcoherent, a quasi-coherent module on the affine base has zero
positive abelian cohomology. The comparison of module and abelian resolutions in
lem-sfb-module-resolution-derived-presheaf-comparison is a quasi-isomorphism of
presheaf complexes; evaluation is exact, so module cohomology has the same vanishing.
3. Use lem-trf-space-enlarged-etale-ringed-site-model to realize f as a morphism of
ringed topoi and lem-trf-space-chart-limit-enlarged-sections to identify its direct
image with the specified chart-limit functor. Equivalences preserve injectives and
global sections. Apply lem-sfb-ringed-site-leray-spectral-sequence to obtain the
natural first-quadrant sequence H^a(Y,R^b f_*M) converging to H^(a+b)(X,M), with its
finite filtration and the cocycle edge. The scalar sections compositor is normalized
by the same chart projections, so the edge is A-linear with the formula above.
4. Only column a=0 survives. For r>=2 incoming differentials to (0,q) start in
negative first degree, and outgoing ones land in a zero column. All other graded
pieces in total degree q vanish; descending along the finite filtration gives
Fil^1=0. Thus the edge is an isomorphism, naturally in M and independently of the
resolution. At q=0 it is the ordinary sections compositor; zero modules and the
empty affine base give zero modules on both sides.
-/
theorem exists_affineBaseHigherImageSections_iso
    (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)) :
    ∃ e : ∀ q : ℕ, affineBaseModuleCohomology A Y a X f q ≅
        affineBaseHigherImageSections A Y a X f q,
      AffineBaseHigherImageSectionsNormalization A Y a X f e := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
