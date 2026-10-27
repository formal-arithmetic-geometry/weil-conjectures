/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # Coherent constant-coefficient restriction to open small sites

Source: Stacks Project, sites.tex, Tags 00XZ, 03EH and 00WH; sites-modules.tex,
Tags 04IX, 04IY and 03DJ (blueprint: lem-pur-open-small-ringed-site-coherence).
The two namespaces give the same statement for the small etale and pro-etale sites.
All constructions below use the bounded concrete sites in the common universe `u + 1`.
No independent skeleton choices: transport this whole diagram to small models.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Etale

/-- The published open-site equivalence, oriented towards the localized ambient site.
Source: Stacks Tags 00XZ and 03EH
(blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenEquiv {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    U.Etale ≌ Over (Etale.mk j) :=
  (overEquiv (Etale.mk j)).symm

/-- Composition of a small-site object with the open inclusion, forgetting its slice map.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenComposition {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    U.Etale ⥤ T.Etale :=
  (purOpenEquiv j).functor ⋙ Over.forget (Etale.mk j)

/-- Continuity of the published slice equivalence followed by localization.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
instance purOpenCompositionContinuous {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (purOpenComposition j).IsContinuous (U.smallEtaleTopology) (T.smallEtaleTopology) := by
  have : (purOpenEquiv j).functor.IsContinuous U.smallEtaleTopology
      (T.smallEtaleTopology.over (Etale.mk j)) :=
    inferInstanceAs ((overEquiv (Etale.mk j)).inverse.IsContinuous
      (Etale.mk j).left.smallEtaleTopology (T.smallEtaleTopology.over (Etale.mk j)))
  exact Functor.isContinuous_comp _ _ _ (T.smallEtaleTopology.over (Etale.mk j)) _

/-- Cocontinuity of the same open localization functor.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
instance purOpenCompositionCocontinuous {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (purOpenComposition j).IsCocontinuous (U.smallEtaleTopology) (T.smallEtaleTopology) := by
  have : (purOpenEquiv j).functor.IsCocontinuous U.smallEtaleTopology
      (T.smallEtaleTopology.over (Etale.mk j)) :=
    overEquiv_inverse_isCocontinuous (Etale.mk j)
  exact CategoryTheory.isCocontinuous_comp _ _ _ (T.smallEtaleTopology.over (Etale.mk j))

/-- The canonical coefficient comparison, constructed from ring-valued sheafification.
It is the comparison for the constant presheaf, with its sheafification-unit normalization.
Source: Stacks Tags 00WH and 00XZ
(blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenRingComparison {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (A : CommRingCat.{u + 1}) :
    (constantSheaf (U.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A) ≅
      ((purOpenComposition j).sheafPushforwardContinuous RingCat.{u + 1}
        (U.smallEtaleTopology) (T.smallEtaleTopology)).obj
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A)) :=
  ((purOpenComposition j).pushforwardContinuousSheafificationCompatibility
    RingCat.{u + 1} (U.smallEtaleTopology) (T.smallEtaleTopology)).app
      ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))

/-- Actual module restriction: precomposition and scalar transport along the canonical
coefficient comparison. Both object and morphism section formulas are definitional.
Source: Stacks Tags 04IX and 04IY
(blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenRestriction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (A : CommRingCat.{u + 1}) :
    ringedSiteModules.{u + 1}
      ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A)) ⥤
    ringedSiteModules.{u + 1}
      ((constantSheaf (U.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A)) :=
  SheafOfModules.pushforward (purOpenRingComparison j A).hom

/-- The concrete relocalization comparison: both paths keep the scheme and its arrows.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenCompositionComp {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    purOpenComposition (k ≫ j) ≅ purOpenComposition k ⋙ purOpenComposition j :=
  MorphismProperty.Over.mapComp (P := @AlgebraicGeometry.Etale) ⊤
    (inferInstance : AlgebraicGeometry.Etale k) (inferInstance : AlgebraicGeometry.Etale j)

/-- The identity localization comparison, with the identity underlying scheme arrow.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenCompositionId (T : Scheme.{u}) : purOpenComposition (𝟙 T) ≅ 𝟭 T.Etale :=
  MorphismProperty.Over.mapId (P := @AlgebraicGeometry.Etale) ⊤ T

/-- Transport of the actual restriction functor along equality of the open arrow.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenRestrictionCongr {U T : Scheme.{u}} {j j' : U ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : j = j') (A : CommRingCat.{u + 1}) :
    purOpenRestriction j A ≅ purOpenRestriction j' A :=
  eqToIso (by cases h; rfl)

/-- Coherent small open ringed-site realization and exact restriction.

Source: Stacks Project, sites.tex Tags 00XZ, 03EH, 00WH and 00XR; sites-modules.tex
Tags 04IX, 04IY and 03DJ (blueprint: lem-pur-open-small-ringed-site-coherence).

Proof plan (the six steps of the DAG node):
1. Use the published small-site slice equivalence. Its two functors leave schemes and
   arrows unchanged, and identify the covering families. Transfer to common small models.
2. Apply ring-valued sheafification/localization compatibility to the constant presheaf.
   Its unit equation proves that the comparison preserves each constant section.
3. Restriction to the slice is exact by localizedSystemExact; transport along the site
   equivalence and the coefficient isomorphism preserves kernels and cokernels. This
   proves exactness of the actual specified functor, without asserting section surjectivity.
4. Relocalization sends a nested slice object to the same scheme over the ambient base;
   purOpenCompositionComp records the resulting identity on underlying arrows.
5. Precompose both coefficient composites with the constant-presheaf sheafification unit.
   They are equal by Step 2. Uniqueness of sheafification gives the full coefficient
   cocycle, including identity normalization, on all sections.
6. Both module restrictions have the same section group. The cocycle identifies their
   scalar actions, so the identity on sections gives the natural isomorphism eta. On
   morphisms its naturality square is the original component. The identity comparison
   delta and both composites for three restrictions are identities on sections; this
   proves both identity laws and associativity by extensionality.

The composition and identity clauses use the canonical transports of scheme arrows.
They retain the maps on all sections, not just constant sections.
Finite coefficients are allowed to include the zero ring.
-/
theorem purOpenSmallRingedSiteCoherence (A : CommRingCat.{u + 1}) [Finite A] :
    ∃ (eta : ∀ {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion j],
        purOpenRestriction j A ⋙ purOpenRestriction k A ≅ purOpenRestriction (k ≫ j) A)
      (delta : ∀ T : Scheme.{u}, purOpenRestriction (𝟙 T) A ≅ 𝟭 _),
      (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
        (∀ (V : U.Etale) (S : Sieve V),
          S ∈ (U.smallEtaleTopology) V ↔
            S.functorPushforward (purOpenEquiv j).functor ∈
              ((T.smallEtaleTopology).over (Etale.mk j)) ((purOpenEquiv j).functor.obj V)) ∧
        (∀ (V : Over (Etale.mk j)) (S : Sieve V),
          S ∈ ((T.smallEtaleTopology).over (Etale.mk j)) V ↔
            S.functorPushforward (purOpenEquiv j).inverse ∈
              (U.smallEtaleTopology) ((purOpenEquiv j).inverse.obj V)) ∧
        (∀ V : U.Etale,
          (toSheafify (U.smallEtaleTopology)
            ((Functor.const U.Etaleᵒᵖ).obj (RingCat.of A))).app (op V) ≫
              (purOpenRingComparison j A).hom.hom.app (op V) =
          (toSheafify (T.smallEtaleTopology)
            ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app
              (op ((purOpenComposition j).obj V))) ∧
        (purOpenRestriction j A).Additive ∧
        PreservesFiniteLimits (purOpenRestriction j A) ∧
        PreservesFiniteColimits (purOpenRestriction j A) ∧
        (∀ (F : ringedSiteModules.{u + 1}
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A)))
          (V : U.Etale),
          (((purOpenRestriction j A).obj F).val.obj (op V) : Type (u + 1)) =
            (F.val.obj (op ((purOpenComposition j).obj V)) : Type (u + 1))) ∧
        (∀ (F G : ringedSiteModules.{u + 1}
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A))) (f : F ⟶ G)
          (V : U.Etale),
          (((purOpenRestriction j A).map f).val.app (op V)).hom.toAddMonoidHom =
            (f.val.app (op ((purOpenComposition j).obj V))).hom.toAddMonoidHom) ∧
        (∀ (F : ringedSiteModules.{u + 1}
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A)))
          (V : U.Etale)
          (b : ((constantSheaf (U.smallEtaleTopology) RingCat.{u + 1}).obj
            (RingCat.of A)).obj.obj (op V))
          (x : ((purOpenRestriction j A).obj F).val.obj (op V)),
          (b • x) =
            (@SMul.smul _ (F.val.obj (op ((purOpenComposition j).obj V))) _
              ((purOpenRingComparison j A).hom.hom.app (op V) b) x))) ∧
      (∀ {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion j] (V : W.Etale),
        ((purOpenCompositionComp k j).hom.app V).left = 𝟙 V.left) ∧
      (∀ {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion j] (V : W.Etale),
        (purOpenRingComparison (k ≫ j) A).hom.hom.app (op V) =
          ((purOpenRingComparison k A).hom.hom.app (op V) ≫
            (purOpenRingComparison j A).hom.hom.app
              (op ((purOpenComposition k).obj V)) ≫
            ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A)).obj.map
              ((purOpenCompositionComp k j).hom.app V).op)) ∧
      (∀ (T : Scheme.{u}) (V : T.Etale),
        (purOpenRingComparison (𝟙 T) A).hom.hom.app (op V) =
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A)).obj.map
            ((purOpenCompositionId T).hom.app V).op) ∧
      (∀ {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion j]
        (F : ringedSiteModules.{u + 1}
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A))) (V : W.Etale)
        (x : ((purOpenRestriction k A).obj ((purOpenRestriction j A).obj F)).val.obj (op V)),
        ((eta k j).hom.app F).val.app (op V) x =
          F.val.map ((purOpenCompositionComp k j).hom.app V).op x) ∧
      (∀ (T : Scheme.{u})
        (F : ringedSiteModules.{u + 1}
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A)))
        (V : T.Etale) (x : ((purOpenRestriction (𝟙 T) A).obj F).val.obj (op V)),
        ((delta T).hom.app F).val.app (op V) x =
          F.val.map ((purOpenCompositionId T).inv.app V).op x) ∧
      (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
        (F : ringedSiteModules.{u + 1}
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A))),
        ((eta (𝟙 U) j).hom.app F ≫
          (purOpenRestrictionCongr (Category.id_comp j) A).hom.app F) =
          ((delta U).hom.app ((purOpenRestriction j A).obj F)) ∧
        ((eta j (𝟙 T)).hom.app F ≫
          (purOpenRestrictionCongr (Category.comp_id j) A).hom.app F) =
          ((purOpenRestriction j A).map ((delta T).hom.app F))) ∧
      (∀ {Z W U T : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion h] [IsOpenImmersion k] [IsOpenImmersion j]
        (F : ringedSiteModules.{u + 1}
          ((constantSheaf (T.smallEtaleTopology) RingCat.{u + 1}).obj (RingCat.of A))),
        ((purOpenRestriction h A).map ((eta k j).hom.app F) ≫
          (eta h (k ≫ j)).hom.app F) =
          ((eta h k).hom.app ((purOpenRestriction j A).obj F) ≫
            (eta (h ≫ k) j).hom.app F ≫
            (purOpenRestrictionCongr (Category.assoc h k j) A).hom.app F)) := by
  sorry

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.ProEt

/-- The published open-site equivalence, oriented towards the localized ambient site.
Source: Stacks Tags 00XZ and 03EH
(blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenEquiv {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    U.ProEt ≌ Over (ProEt.mk j) :=
  (sliceEquiv T (ProEt.mk j)).symm

/-- Composition of a small-site object with the open inclusion, forgetting its slice map.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenComposition {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    U.ProEt ⥤ T.ProEt :=
  (purOpenEquiv j).functor ⋙ Over.forget (ProEt.mk j)

/-- Continuity of the published slice equivalence followed by localization.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
instance purOpenCompositionContinuous {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (purOpenComposition j).IsContinuous (ProEt.topology U) (ProEt.topology T) := by
  have := sliceDense T (ProEt.mk j)
  have : (purOpenEquiv j).functor.IsContinuous (ProEt.topology U)
      ((ProEt.topology T).over (ProEt.mk j)) :=
    inferInstanceAs ((sliceEquiv T (ProEt.mk j)).inverse.IsContinuous
      (ProEt.topology (ProEt.mk j).left) ((ProEt.topology T).over (ProEt.mk j)))
  exact Functor.isContinuous_comp _ _ _ ((ProEt.topology T).over (ProEt.mk j)) _

/-- Cocontinuity of the same open localization functor.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
instance purOpenCompositionCocontinuous {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (purOpenComposition j).IsCocontinuous (ProEt.topology U) (ProEt.topology T) := by
  have : (purOpenEquiv j).functor.IsCocontinuous (ProEt.topology U)
      ((ProEt.topology T).over (ProEt.mk j)) := sliceFrom_cocont T (ProEt.mk j)
  exact CategoryTheory.isCocontinuous_comp _ _ _ ((ProEt.topology T).over (ProEt.mk j))

/-- The canonical coefficient comparison, constructed from ring-valued sheafification.
It is the comparison for the constant presheaf, with its sheafification-unit normalization.
Source: Stacks Tags 00WH and 00XZ
(blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenRingComparison {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (A : CommRingCat.{u + 1}) :
    (constantSheaf (ProEt.topology U) RingCat.{u + 1}).obj (RingCat.of A) ≅
      ((purOpenComposition j).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology T)).obj
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A)) :=
  ((purOpenComposition j).pushforwardContinuousSheafificationCompatibility
    RingCat.{u + 1} (ProEt.topology U) (ProEt.topology T)).app
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A))

/-- Actual module restriction: precomposition and scalar transport along the canonical
coefficient comparison. Both object and morphism section formulas are definitional.
Source: Stacks Tags 04IX and 04IY
(blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenRestriction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (A : CommRingCat.{u + 1}) :
    ringedSiteModules.{u + 1}
      ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A)) ⥤
    ringedSiteModules.{u + 1}
      ((constantSheaf (ProEt.topology U) RingCat.{u + 1}).obj (RingCat.of A)) :=
  SheafOfModules.pushforward (purOpenRingComparison j A).hom

/-- The concrete relocalization comparison: both paths keep the scheme and its arrows.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenCompositionComp {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    purOpenComposition (k ≫ j) ≅ purOpenComposition k ⋙ purOpenComposition j :=
  MorphismProperty.Over.mapComp (P := @WeaklyEtale) ⊤
    (inferInstance : WeaklyEtale k) (inferInstance : WeaklyEtale j)

/-- The identity localization comparison, with the identity underlying scheme arrow.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenCompositionId (T : Scheme.{u}) : purOpenComposition (𝟙 T) ≅ 𝟭 T.ProEt :=
  MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ T

/-- Transport of the actual restriction functor along equality of the open arrow.
Source: Stacks Tag 03EH (blueprint: lem-pur-open-small-ringed-site-coherence). -/
def purOpenRestrictionCongr {U T : Scheme.{u}} {j j' : U ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : j = j') (A : CommRingCat.{u + 1}) :
    purOpenRestriction j A ≅ purOpenRestriction j' A :=
  eqToIso (by cases h; rfl)

/-- Coherent small open ringed-site realization and exact restriction.

Source: Stacks Project, sites.tex Tags 00XZ, 03EH, 00WH and 00XR; sites-modules.tex
Tags 04IX, 04IY and 03DJ (blueprint: lem-pur-open-small-ringed-site-coherence).

Proof plan (the six steps of the DAG node):
1. Use the published small-site slice equivalence. Its two functors leave schemes and
   arrows unchanged, and identify the covering families. Transfer to common small models.
2. Apply ring-valued sheafification/localization compatibility to the constant presheaf.
   Its unit equation proves that the comparison preserves each constant section.
3. Restriction to the slice is exact by localizedSystemExact; transport along the site
   equivalence and the coefficient isomorphism preserves kernels and cokernels. This
   proves exactness of the actual specified functor, without asserting section surjectivity.
4. Relocalization sends a nested slice object to the same scheme over the ambient base;
   purOpenCompositionComp records the resulting identity on underlying arrows.
5. Precompose both coefficient composites with the constant-presheaf sheafification unit.
   They are equal by Step 2. Uniqueness of sheafification gives the full coefficient
   cocycle, including identity normalization, on all sections.
6. Both module restrictions have the same section group. The cocycle identifies their
   scalar actions, so the identity on sections gives the natural isomorphism eta. On
   morphisms its naturality square is the original component. The identity comparison
   delta and both composites for three restrictions are identities on sections; this
   proves both identity laws and associativity by extensionality.

The composition and identity clauses use the canonical transports of scheme arrows.
They retain the maps on all sections, not just constant sections.
Finite coefficients are allowed to include the zero ring.
-/
theorem purOpenSmallRingedSiteCoherence (A : CommRingCat.{u + 1}) [Finite A] :
    ∃ (eta : ∀ {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion j],
        purOpenRestriction j A ⋙ purOpenRestriction k A ≅ purOpenRestriction (k ≫ j) A)
      (delta : ∀ T : Scheme.{u}, purOpenRestriction (𝟙 T) A ≅ 𝟭 _),
      (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
        (∀ (V : U.ProEt) (S : Sieve V),
          S ∈ (ProEt.topology U) V ↔
            S.functorPushforward (purOpenEquiv j).functor ∈
              ((ProEt.topology T).over (ProEt.mk j)) ((purOpenEquiv j).functor.obj V)) ∧
        (∀ (V : Over (ProEt.mk j)) (S : Sieve V),
          S ∈ ((ProEt.topology T).over (ProEt.mk j)) V ↔
            S.functorPushforward (purOpenEquiv j).inverse ∈
              (ProEt.topology U) ((purOpenEquiv j).inverse.obj V)) ∧
        (∀ V : U.ProEt,
          (toSheafify (ProEt.topology U)
            ((Functor.const U.ProEtᵒᵖ).obj (RingCat.of A))).app (op V) ≫
              (purOpenRingComparison j A).hom.hom.app (op V) =
          (toSheafify (ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A))).app
              (op ((purOpenComposition j).obj V))) ∧
        (purOpenRestriction j A).Additive ∧
        PreservesFiniteLimits (purOpenRestriction j A) ∧
        PreservesFiniteColimits (purOpenRestriction j A) ∧
        (∀ (F : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A)))
          (V : U.ProEt),
          (((purOpenRestriction j A).obj F).val.obj (op V) : Type (u + 1)) =
            (F.val.obj (op ((purOpenComposition j).obj V)) : Type (u + 1))) ∧
        (∀ (F G : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A))) (f : F ⟶ G)
          (V : U.ProEt),
          (((purOpenRestriction j A).map f).val.app (op V)).hom.toAddMonoidHom =
            (f.val.app (op ((purOpenComposition j).obj V))).hom.toAddMonoidHom) ∧
        (∀ (F : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A)))
          (V : U.ProEt)
          (b : ((constantSheaf (ProEt.topology U) RingCat.{u + 1}).obj
            (RingCat.of A)).obj.obj (op V))
          (x : ((purOpenRestriction j A).obj F).val.obj (op V)),
          (b • x) =
            (@SMul.smul _ (F.val.obj (op ((purOpenComposition j).obj V))) _
              ((purOpenRingComparison j A).hom.hom.app (op V) b) x))) ∧
      (∀ {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion j] (V : W.ProEt),
        ((purOpenCompositionComp k j).hom.app V).left = 𝟙 V.left) ∧
      (∀ {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion j] (V : W.ProEt),
        (purOpenRingComparison (k ≫ j) A).hom.hom.app (op V) =
          ((purOpenRingComparison k A).hom.hom.app (op V) ≫
            (purOpenRingComparison j A).hom.hom.app
              (op ((purOpenComposition k).obj V)) ≫
            ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A)).obj.map
              ((purOpenCompositionComp k j).hom.app V).op)) ∧
      (∀ (T : Scheme.{u}) (V : T.ProEt),
        (purOpenRingComparison (𝟙 T) A).hom.hom.app (op V) =
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A)).obj.map
            ((purOpenCompositionId T).hom.app V).op) ∧
      (∀ {W U T : Scheme.{u}} (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion j]
        (F : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A))) (V : W.ProEt)
        (x : ((purOpenRestriction k A).obj ((purOpenRestriction j A).obj F)).val.obj (op V)),
        ((eta k j).hom.app F).val.app (op V) x =
          F.val.map ((purOpenCompositionComp k j).hom.app V).op x) ∧
      (∀ (T : Scheme.{u})
        (F : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A)))
        (V : T.ProEt) (x : ((purOpenRestriction (𝟙 T) A).obj F).val.obj (op V)),
        ((delta T).hom.app F).val.app (op V) x =
          F.val.map ((purOpenCompositionId T).inv.app V).op x) ∧
      (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
        (F : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A))),
        ((eta (𝟙 U) j).hom.app F ≫
          (purOpenRestrictionCongr (Category.id_comp j) A).hom.app F) =
          ((delta U).hom.app ((purOpenRestriction j A).obj F)) ∧
        ((eta j (𝟙 T)).hom.app F ≫
          (purOpenRestrictionCongr (Category.comp_id j) A).hom.app F) =
          ((purOpenRestriction j A).map ((delta T).hom.app F))) ∧
      (∀ {Z W U T : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ U) (j : U ⟶ T)
        [IsOpenImmersion h] [IsOpenImmersion k] [IsOpenImmersion j]
        (F : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of A))),
        ((purOpenRestriction h A).map ((eta k j).hom.app F) ≫
          (eta h (k ≫ j)).hom.app F) =
          ((eta h k).hom.app ((purOpenRestriction j A).obj F) ≫
            (eta (h ≫ k) j).hom.app F ≫
            (purOpenRestrictionCongr (Category.assoc h k j) A).hom.app F)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt

