/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.AlgebraicGeometry.SchemeEtaleCotangentRingMap
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Ring.FilteredColimits

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsAdjunctionExtension
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsOpenDetermination
import Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel
import Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageSectionDescription
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-! # Scheme differentials and differentials on the small étale ringed topos

Source: Stacks Project, More on Morphisms of Spaces, Tags 04CS and 04CT
(blueprint: lem-sfb-scheme-etale-relative-differentials-comparison).

The right-hand module is the sheafification of the actual sectionwise differential
presheaf for the canonical inverse-image structural ring map. The comparison is an
additive sheaf isomorphism with explicit linearity; its inverse carries the étale
universal derivation to the associated Zariski derivation on every étale chart.
All schemes, rings and module sections retain their original universe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open PresheafOfModules.DifferentialsConstruction
namespace AlgebraicGeometry.Scheme.Hom

/-- The module sheafification of `W ↦ Ω_{O(W)/(f⁻¹O)(W)}`. The presheaf and
its restriction maps are Mathlib's sectionwise Kähler differential construction.
Source: Stacks, Tags 04CS, 04CT and 04BL
(blueprint: lem-sfb-scheme-etale-relative-differentials-comparison). -/
def etaleRelativeDifferentials {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (PresheafOfModules.sheafification (𝟙
    ((sheafCompose X.smallEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (etaleDifferentialStructure X)).obj)).obj
    (relativeDifferentials' (etaleDifferentialRingMap f).hom)

/-- The sectionwise universal derivations followed by the module-sheafification unit.
This construction includes naturality, additivity, Leibniz and annihilation of `f⁻¹O`.
Source: Stacks, Tags 04CS and 04BL
(blueprint: lem-sfb-scheme-etale-relative-differentials-comparison). -/
def etaleRelativeDifferentialsDerivation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleRelativeDifferentials f).val.Derivation' (etaleDifferentialRingMap f).hom :=
  (derivation' (etaleDifferentialRingMap f).hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction (𝟙
      ((sheafCompose X.smallEtaleTopology (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (etaleDifferentialStructure X)).obj)).unit.app _)

/-- The canonical linear comparison, normalized by the universal derivations.
The isomorphism is expressed on underlying additive sheaves with sectionwise
linearity, equivalently as an isomorphism of module sheaves. The final equation
uses the canonical map `h* Ω_{X/Y} → Ω_{W/Y}`: its inverse transports `d_{W/Y}`
to the associated derivation, exactly as in Tag 04CS. Quasi-coherence is a conclusion,
not an additional hypothesis. No finiteness or geometric restriction on `f` is used.
Source: Stacks, Tags 04CS and 04CT
(blueprint: lem-sfb-scheme-etale-relative-differentials-comparison).

Proof plan:
1. On every étale chart h, lem-sfb-etale-localization-relative-differentials
   identifies h* Ω_{X/Y} with Ω_{W/Y} by the canonical differential map. Pull the
   universal derivation back along this isomorphism. The universal property,
   module-pullback adjunction and composition comparisons show naturality under
   chart restriction (lem-sfb-relative-differentials-sheaf-universal-property,
   lem-pc-module-pullback-adjunction, lem-pc-module-pullback-identity-composition,
   lem-weil-pbc-etale-composition-cancellation). The affine comparison for the
   Zariski sheaf gives quasi-coherence, including without finite presentation.
2. This derivation kills f⁻¹O: locally inverse-image sections come from an étale
   target chart by lem-weil-pbc-etale-inverse-image-section-description and the
   canonical model of lem-trf-space-enlarged-etale-ringed-site-model. Apply étale
   localization on that target chart and base-vanishing of the universal derivation;
   separatedness then gives the global assertion.
3. By lem-trf-sheafified-module-differentials-cokernel, the sectionwise sheafification
   represents these derivations. Obtain its unique map to the associated module.
4. For an arbitrary module sheaf and derivation, restrict to Zariski opens. The
   scheme differential universal property gives a unique linear map there. Extend
   it by lem-trf-etale-tensor-sections-adjunction-extension, using
   lem-trf-zariski-etale-tensor-sections and def-sc-etale-qcoherent-module.
5. The extended map carries the associated derivation to the given derivation on
   all charts: their difference vanishes on base affine opens. For an affine étale
   chart Spec B over Spec A it is an A-derivation, hence zero since Ω_{B/A}=0
   (lem-weil-pbc-etale-ring-map-iff-etale-affine and
   def-weil-pbc-kahler-differentials). Glue over open covers; no affine-intersection
   hypothesis and no quasi-coherence of the target module are needed.
6. Uniqueness on opens and lem-trf-etale-tensor-sections-open-determination give
   uniqueness on the whole site. Thus the associated module also represents the
   same derivations, with the specified local normalization.
7. Apply both universal properties to the two universal derivations. The maps are
   inverse because their composites fix the derivations. This gives the unique
   linear isomorphism displayed below and its formula on every étale chart,
   including empty charts and empty schemes.
-/
theorem scheme_etale_relativeDifferentials_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ hF : f.relativeDifferentials.IsQuasicoherent,
      ∃! e : @Modules.etaleTensorSectionsSheaf X f.relativeDifferentials hF ≅
          (SheafOfModules.toSheaf _).obj (etaleRelativeDifferentials f),
        (∀ (W : X.Etale) (r : Γ(W.left, ⊤))
          (s : Γ((Modules.tensorPullback W.hom).obj f.relativeDifferentials, ⊤)),
          e.hom.hom.app (op W)
              ((((Modules.tensorPullback W.hom).obj f.relativeDifferentials).smul r).hom s) =
            r • (@id ((etaleRelativeDifferentials f).val.obj (op W))
              (e.hom.hom.app (op W) s))) ∧
        (∀ (W : X.Etale) (a : Γ(W.left, ⊤)),
          (relativeDifferentialsPullbackMap f W.hom).app ⊤
              (@id (Γ((Modules.tensorPullback W.hom).obj f.relativeDifferentials, ⊤))
                (e.inv.hom.app (op W)
                  ((etaleRelativeDifferentialsDerivation f).d (X := op W) a))) =
            (W.hom ≫ f).relativeDifferentialsDerivation.d (X := op ⊤) a) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
