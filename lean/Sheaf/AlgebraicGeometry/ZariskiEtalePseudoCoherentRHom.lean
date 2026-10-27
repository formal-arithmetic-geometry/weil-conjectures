/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomMapQuasiIso
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized

/-! # Zariski to étale comparison for pseudo-coherent derived Hom

Source: Stacks Project, spaces-perfect.tex, Tag 08JP, case (1), and
sites-cohomology.tex, Tag 08JI
(blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom).

Restriction to the small model of the affine étale basis keeps the module universe
unchanged. The local-section equation fixes pullback of sheaf Hom, the product
projections fix the chain map, and the localization equation fixes the derived map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genInjectivity false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A small model of the existing affine étale basis, with no coefficient enlargement.
Source: Stacks 03ED, 039Z (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
abbrev ZariskiEtaleRHomSite (X : Scheme.{u}) := SmallModel.{u} X.AffineEtale

/-- Actual affine étale charts underlying the small model.
Source: Stacks 03ED, 039Z (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def zariskiEtaleRHomInclusion (X : Scheme.{u}) : ZariskiEtaleRHomSite X ⥤ X.Etale :=
  (equivSmallModel X.AffineEtale).inverse ⋙ AffineEtale.Spec X

/-- The topology induced from the given small étale site.
Source: Stacks 039Z (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
abbrev zariskiEtaleRHomTopology (X : Scheme.{u}) :=
  (zariskiEtaleRHomInclusion X).inducedTopology X.smallEtaleTopology

/-- The actual commutative structure rings restricted to the small affine basis.
Source: Stacks 03G7, 039Z (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def zariskiEtaleRHomRing (X : Scheme.{u}) :
    Sheaf (zariskiEtaleRHomTopology X) CommRingCat.{u} :=
  ((zariskiEtaleRHomInclusion X).sheafPushforwardContinuous CommRingCat.{u}
    (zariskiEtaleRHomTopology X) X.smallEtaleTopology).obj
      ⟨X.etaleStructurePresheaf, X.isSheaf_etaleStructurePresheaf⟩

/-- The same module category expressed on the small affine basis.
Source: Stacks 039Z, 03DX (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
abbrev ZariskiEtaleRHomModules (X : Scheme.{u}) :=
  SheafOfModules.{u} ((sheafCompose (zariskiEtaleRHomTopology X)
    (forget₂ CommRingCat RingCat)).obj (zariskiEtaleRHomRing X))

/-- Actual module restriction to the affine basis, by precomposition and the identity
on regular functions. Source: Stacks 039Z
(blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def zariskiEtaleRHomRestriction (X : Scheme.{u}) :
    SmallEtaleModules X ⥤ ZariskiEtaleRHomModules X :=
  SheafOfModules.pushforward (F := zariskiEtaleRHomInclusion X) ⟨𝟙 _⟩

/-- The canonical epsilon pullback followed by actual restriction to affine charts.
Source: Stacks 08H8, 08JP (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def zariskiEtaleRHomExtension {X : Scheme.{u}} (c : ZariskiEtaleModuleContext X) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤ ZariskiEtaleRHomModules X :=
  c.extension ⋙ zariskiEtaleRHomRestriction X

/-- Pullback of a section on an open, restricted along an affine étale chart over that
open. These sections locally generate the module pullback.
Source: Stacks 03FH, 08JI (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def zariskiEtaleRHomSection {X : Scheme.{u}} (c : ZariskiEtaleModuleContext X)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (V : ZariskiEtaleRHomSite X) (U : X.Opens)
    (h : (zariskiEtaleRHomInclusion X).obj V ⟶ (gabberOpenEtale X).obj U)
    (s : M.val.obj (op U)) :
    ((zariskiEtaleRHomExtension c).obj M).val.obj (op V) :=
  (c.extension.obj M).val.map h.op ((c.adjunction.unit.app M).val.app (op U) s)

/-- The existing K-injective derived Hom on the Zariski site.
Source: Stacks 08J7 (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
abbrev zariskiRHom (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :=
  derivedInternalHomOfUniverses.{u, u, u, w} (Opens.grothendieckTopology X) X.sheaf

/-- The existing K-injective derived Hom on the equivalent small affine étale site.
Source: Stacks 08J7, 039Z (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
abbrev smallEtaleRHom (X : Scheme.{u})
    [HasDerivedCategory.{w} (ZariskiEtaleRHomModules X)] :=
  derivedInternalHomOfUniverses.{u, u, u, w}
    (zariskiEtaleRHomTopology X) (zariskiEtaleRHomRing X)


/-- The complete canonical comparison, expressed on the small affine basis. The
restriction functor is fixed, rather than an arbitrary equivalence. The section and
projection equations determine the ordinary and complex maps uniquely. The final
localization equation uses the fixed K-injective augmentations on both sites.
Source: Stacks 08JP(1), 08JI, 039Z
(blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
structure ZariskiEtalePseudoCoherentRHomData (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (ZariskiEtaleRHomModules X)]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (c : ZariskiEtaleModuleContext X) where
  restriction_equivalence : (zariskiEtaleRHomRestriction X).IsEquivalence
  [extension_additive : (zariskiEtaleRHomExtension c).Additive]
  [extension_limits : PreservesFiniteLimits (zariskiEtaleRHomExtension c)]
  [extension_colimits : PreservesFiniteColimits (zariskiEtaleRHomExtension c)]
  ordinary : ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
    (zariskiEtaleRHomExtension c).obj (SheafOfModules.homObj (R := X.sheaf) M N) ⟶
      SheafOfModules.homObj (R := zariskiEtaleRHomRing X)
        ((zariskiEtaleRHomExtension c).obj M) ((zariskiEtaleRHomExtension c).obj N)
  ordinary_sections : ∀ (M N : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (V : ZariskiEtaleRHomSite X) (U : X.Opens)
      (h : (zariskiEtaleRHomInclusion X).obj V ⟶ (gabberOpenEtale X).obj U)
      (φ : (SheafOfModules.homObj (R := X.sheaf) M N).val.obj (op U))
      (W : ZariskiEtaleRHomSite X) (g : W ⟶ V) (A : X.Opens)
      (i : A ⟶ U)
      (k : (zariskiEtaleRHomInclusion X).obj W ⟶ (gabberOpenEtale X).obj A)
      (_hk : k ≫ (gabberOpenEtale X).map i = (zariskiEtaleRHomInclusion X).map g ≫ h)
      (m : M.val.obj (op A)),
    (((ordinary M N).val.app (op V)
        (zariskiEtaleRHomSection c _ V U h φ)).app (op (Over.mk g)))
          (zariskiEtaleRHomSection c M W A k m) =
      zariskiEtaleRHomSection c N W A k (φ.app (op (Over.mk i)) m)
  complex : ∀ A B : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    ((zariskiEtaleRHomExtension c).mapHomologicalComplex (.up ℤ)).obj
        (homComplex (R := X.sheaf) A B) ⟶
      homComplex (R := zariskiEtaleRHomRing X)
        (((zariskiEtaleRHomExtension c).mapHomologicalComplex (.up ℤ)).obj A)
        (((zariskiEtaleRHomExtension c).mapHomologicalComplex (.up ℤ)).obj B)
  complex_projections : ∀ (A B : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (n p q : ℤ) (hpq : p + n = q),
    (complex A B).f n ≫ homComplexπ (R := zariskiEtaleRHomRing X)
        (((zariskiEtaleRHomExtension c).mapHomologicalComplex (.up ℤ)).obj A)
        (((zariskiEtaleRHomExtension c).mapHomologicalComplex (.up ℤ)).obj B) n p q hpq =
      (zariskiEtaleRHomExtension c).map (homComplexπ (R := X.sheaf) A B n p q hpq) ≫
        ordinary (A.X p) (B.X q)
  comparison : zariskiRHom X ⋙ (zariskiEtaleRHomExtension c).mapDerivedCategory ⟶
    ((zariskiEtaleRHomExtension c).mapDerivedCategory.op.prod
      (zariskiEtaleRHomExtension c).mapDerivedCategory) ⋙ smallEtaleRHom X
  isIso : ∀ (K L : schemeDerivedCategory X), X.IsPseudoCoherent K →
    (∃ a : ℤ, ∀ i : ℤ, i < a → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj L)) →
    IsIso (comparison.app (op K, L))

section Representatives
variable {X : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (ZariskiEtaleRHomModules X)]
  [∀ U : X.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
  {c : ZariskiEtaleModuleContext X} (d : ZariskiEtalePseudoCoherentRHomData X c)
  (A B : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)

/-- Termwise epsilon pullback with the data record's explicit additivity proof.
Source: Stacks 08H8 (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def ZariskiEtalePseudoCoherentRHomData.complexExtension :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (ZariskiEtaleRHomModules X) ℤ :=
  letI := d.extension_additive
  (zariskiEtaleRHomExtension c).mapHomologicalComplex (.up ℤ)

/-- Exact epsilon pullback on derived categories with the record's exactness proofs.
Source: Stacks 08H8 (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def ZariskiEtalePseudoCoherentRHomData.derivedExtension :
    schemeDerivedCategory X ⥤ DerivedCategory (ZariskiEtaleRHomModules X) :=
  letI := d.extension_additive
  letI := d.extension_limits
  letI := d.extension_colimits
  (zariskiEtaleRHomExtension c).mapDerivedCategory

/-- The actual localization factorization of exact termwise epsilon pullback.
Source: Stacks 08H8, 05RU (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def ZariskiEtalePseudoCoherentRHomData.derivedFactors :
    DerivedCategory.Q ⋙ d.derivedExtension ≅ d.complexExtension ⋙ DerivedCategory.Q :=
  letI := d.extension_additive
  letI := d.extension_limits
  letI := d.extension_colimits
  (zariskiEtaleRHomExtension c).mapDerivedCategoryFactors

/-- The common target: Hom of the pulled-back source into the second fixed replacement.
Source: Stacks 08JI (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def ZariskiEtalePseudoCoherentRHomData.representativeTarget :
    DerivedCategory.{w} (ZariskiEtaleRHomModules X) :=
  (DerivedCategory.Q (C := ZariskiEtaleRHomModules X)).obj
    (homComplex (R := zariskiEtaleRHomRing X)
      (d.complexExtension.obj A)
      ((WeilConjectures.coefficientHomResolution.{u, u, u}
        (zariskiEtaleRHomTopology X) (zariskiEtaleRHomRing X)).obj
        (d.complexExtension.obj
          ((WeilConjectures.coefficientHomResolution.{u, u, u}
            (Opens.grothendieckTopology X) X.sheaf).obj B))))

/-- The comparison's target identification through the pulled-back augmentation and
fixed etale resolution. Source: Stacks 08JI
(blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def ZariskiEtalePseudoCoherentRHomData.targetIdentification :
    (smallEtaleRHom X).obj
        (op (d.derivedExtension.obj (DerivedCategory.Q.obj A)),
          d.derivedExtension.obj (DerivedCategory.Q.obj B)) ⟶
      d.representativeTarget A B :=
      (smallEtaleRHom X).map
        (Prod.mkHom
          ((d.derivedFactors.inv.app A).op)
          (d.derivedFactors.hom.app B ≫
            DerivedCategory.Q.map
              (d.complexExtension.map
                ((ringedSiteHomAugmentation.{u, u, u}
                  (Opens.grothendieckTopology X) X.sheaf).app B)))) ≫
      (WeilConjectures.coefficientHomResolutionIso.{u, u, u, w}
        (zariskiEtaleRHomTopology X) (zariskiEtaleRHomRing X)
        (d.complexExtension.obj A)
        (d.complexExtension.obj
          ((WeilConjectures.coefficientHomResolution.{u, u, u}
            (Opens.grothendieckTopology X) X.sheaf).obj B))).hom

/-- The prescribed chain-map composite, localized after the two fixed replacements.
Source: Stacks 08JI, 08JP (blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom). -/
def ZariskiEtalePseudoCoherentRHomData.sourceIdentification :
    d.derivedExtension.obj
        ((zariskiRHom X).obj (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B)) ⟶
      d.representativeTarget A B :=
      d.derivedExtension.map
        (WeilConjectures.coefficientHomResolutionIso.{u, u, u, w}
          (Opens.grothendieckTopology X) X.sheaf A B).hom ≫
      d.derivedFactors.hom.app
        (homComplex (R := X.sheaf) A
          ((WeilConjectures.coefficientHomResolution.{u, u, u}
            (Opens.grothendieckTopology X) X.sheaf).obj B)) ≫
      DerivedCategory.Q.map
        (d.complex A ((WeilConjectures.coefficientHomResolution.{u, u, u}
            (Opens.grothendieckTopology X) X.sheaf).obj B) ≫
          ((homComplexFunctor (R := zariskiEtaleRHomRing X)).obj
            (op (d.complexExtension.obj A))).map
            ((ringedSiteHomAugmentation.{u, u, u} (zariskiEtaleRHomTopology X)
              (zariskiEtaleRHomRing X)).app
                (d.complexExtension.obj
                  ((WeilConjectures.coefficientHomResolution.{u, u, u}
                    (Opens.grothendieckTopology X) X.sheaf).obj B))))


end Representatives

/-- Exact epsilon pullback commutes with derived internal Hom from pseudo-coherent
objects into bounded-below objects. No quasi-coherence or Noetherian condition is imposed.
Source: Stacks 08JP(1), 08H8, 08JI
(blueprint: lem-sfb-zariski-etale-pseudocoherent-rhom).
Proof:
1. Restrict to the small affine étale basis. The comparison lemma identifies the
module categories by actual restriction, preserving the original module universe.
2. Exact epsilon pullback preserves cohomology and quasi-isomorphisms. Pullback of
local module maps determines ordinary_sections; product projections determine the
complex comparison. The signed differential commutes with this map by additivity.
3. Apply the fixed K-injective augmentation on the Zariski site and then the fixed
one on the étale site. The two-out-of-three property makes the composite replacement
of the pulled-back second argument a quasi-isomorphism. Localization gives comparison
and representatives, natural contravariantly in K and covariantly in L.
4. Check invertibility on Zariski opens. Restriction preserves K-injectives and the
specified component maps, so the representative equation is compatible with opens.
5. Pseudo-coherence gives locally a bounded-above finite-free representative P for K.
The bound on cohomology of L gives a bounded-below representative F by good truncation.
6. These Hom complexes compute RHom. In degree n only a-n ≤ p ≤ b contributes,
so each product is finite. Pullback commutes with finite biproducts and with Hom
from a finite-free module, including rank zero. Thus the ordinary comparison is a
chain isomorphism on these models.
7. The augmentation square compares this chain isomorphism to the fixed comparison.
The vertical maps are quasi-isomorphisms by the bounded-free RHom model lemma, even
when the K-injective target is unbounded. Thus the fixed comparison is invertible
locally and hence globally. Empty schemes and zero objects are included. -/
theorem zariski_etale_pseudoCoherent_rhom (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (ZariskiEtaleRHomModules X)]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (c : ZariskiEtaleModuleContext X) :
    ∃ d : ZariskiEtalePseudoCoherentRHomData X c,
      ∀ A B : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        d.comparison.app (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≫
          d.targetIdentification A B = d.sourceIdentification A B := by
  sorry

end AlgebraicGeometry.Scheme.Modules
