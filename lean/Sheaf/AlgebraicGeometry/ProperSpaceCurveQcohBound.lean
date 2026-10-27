/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections
import Sheaf.AlgebraicGeometry.CurveEtaleSchemeCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Quasi-coherent cohomological dimension of proper algebraic-space curves

Source: Stacks Project, moduli-curves.tex, Tag 0E6F; limits.tex, Tag 0E7D;
spaces-cohomology.tex, Tag 08EX
(blueprint: lem-sfb-proper-space-curve-qcoh-bound).

Higher direct images and cohomology are right derived functors in all module sheaves,
using the existing equivalent small affine model of the small etale ringed site.
The affine-base assertion quantifies over all quasi-coherent modules on each pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper, flat, finitely presented family with geometric fibres of dimension at most
one has no quasi-coherent higher direct images above degree one. After any affine base
change, every quasi-coherent module on the pullback has vanishing cohomology above one.
Empty fibres are allowed by `IsProperCurveFamily`. No Noetherian, coherent, nodal, reduced,
connected or Gorenstein hypothesis is made.
Source: Stacks, Tags 0E6F, 0E7D and 08EX
(blueprint: lem-sfb-proper-space-curve-qcoh-bound).

Proof:
1. By lem-sfb-curve-etale-scheme-cover choose a jointly surjective etale scheme covering
   of T on which X is a scheme. By lem-sfb-space-flat-proper-fp-locality the local maps
   are proper, flat and finitely presented. By lem-sfb-proper-flat-space-fibre-dimension
   their fibres still have dimension at most one, including empty fibres.
2. Restrict F to these sources. The local presentations of
   def-trf-space-quasi-coherent-module restrict to presentations on the slice sites.
   By lem-sfb-scheme-etale-higher-image-comparison identify etale higher images with
   the etale modules of the Zariski higher images. Properness gives quasi-compactness
   and quasi-separatedness. Apply lem-sfb-proper-quasicoherent-fibre-dimension-vanishing
   with d = 1 to conclude that all these local higher images vanish when q > 1.
3. By lem-sfb-space-higher-image-etale-restriction these are the restrictions of the
   original higher image. Base change the covering to each test scheme using
   lem-trf-space-fibre-products-etale-covers. The sheaf equalizer condition of
   def-weil-pbc-sites-and-cohomology makes every section zero, so the higher image is zero.
4. For any affine V -> T and any G on its pullback, the two geometric permanence lemmas
   from step 1 retain the same family hypotheses. Repeat steps 1--3 for this G; it need
   not descend from X. By lem-sfb-space-affine-base-higher-image-sections its cohomology
   is the sections of its higher image, hence zero. Transport through the fixed module
   restriction equivalences changes neither vanishing nor the injective-resolution
   derived functors. -/
theorem proper_space_curve_qcoh_bound {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Over S) (f : X ⟶ schemeSpace T)
    (hf : IsProperCurveFamily X T f.hom.hom) :
    (∀ (F : X.QCoh) (q : ℕ), 1 < q →
      IsZero (((smallModuleDirectImage f).rightDerived q).obj
        (X.smallModuleRestriction.obj F.obj))) ∧
    (∀ (A : Type u) [CommRing A] (V : Over S) (a : V.left ≅ Spec (.of A))
      (g : V ⟶ T)
      (G : (enlargedFibreProduct
        (ObjectProperty.homMk ⟨yoneda.map g⟩ : schemeSpace V ⟶ schemeSpace T) f).QCoh)
      (q : ℕ), 1 < q →
      IsZero (((affineScalarSections A V a
        (enlargedFibreProduct
          (ObjectProperty.homMk ⟨yoneda.map g⟩ : schemeSpace V ⟶ schemeSpace T) f)
        (enlargedFibreProductFst
          (ObjectProperty.homMk ⟨yoneda.map g⟩ : schemeSpace V ⟶ schemeSpace T)
          f)).rightDerived q).obj
        ((smallModuleRestriction (enlargedFibreProduct
          (ObjectProperty.homMk ⟨yoneda.map g⟩ : schemeSpace V ⟶ schemeSpace T)
          f)).obj G.obj))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
