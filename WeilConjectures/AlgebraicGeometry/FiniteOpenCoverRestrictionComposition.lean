/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import WeilConjectures.AlgebraicGeometry.Sites.KInjectiveComparisonPrinciple
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.CategoryTheory.TotalSiteAugmentationData.TotalSiteInjectiveAugmentationExactness
public import Mathlib.Order.Fin.Basic
public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
public import WeilConjectures.Algebra.Homology.TotalComplexRowResolution
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Composition of canonical open-image restrictions

Source: Stacks Project, Tag 00XZ; the unit and composition coherence of inverse
and direct image, specialized to inclusions of opens.
(blueprint: new-finite-cover-restriction-composition)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

private theorem upperStarComp_named_assoc_inv
    {W₀ X₀ Y₀ Z₀ : Scheme.{u}} (a : W₀ ⟶ X₀) (b : X₀ ⟶ Y₀) (c : Y₀ ⟶ Z₀)
    (ab : W₀ ⟶ Y₀) (bc : X₀ ⟶ Z₀) (abc : W₀ ⟶ Z₀)
    (hab : ab = a ≫ b) (hbc : bc = b ≫ c) (habc : abc = ab ≫ c) :
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} B) c)
        (upperStarComp (ModuleCat.{u + 1} B) a b ab hab).inv ≫
      (upperStarComp (ModuleCat.{u + 1} B) ab c abc habc).inv =
    Functor.whiskerRight (upperStarComp (ModuleCat.{u + 1} B) b c bc hbc).inv
        (upperStar (ModuleCat.{u + 1} B) a) ≫
      (upperStarComp (ModuleCat.{u + 1} B) a bc abc
        (by rw [habc, hab, hbc, Category.assoc])).inv := by
  subst hab
  subst hbc
  subst habc
  have key := congrArg Iso.inv (upperStarComp_assoc (ModuleCat.{u + 1} B)
    a b c ((a ≫ b) ≫ c) (Category.assoc a b c))
  apply NatTrans.ext
  funext M
  simpa using (NatTrans.congr_app key M).symm

/-- Restriction along the identity inclusion is the identity.
Source: Stacks Project, Tag 00XZ; identity coherence for the localization adjunction.
(blueprint: new-finite-cover-restriction-composition)

Proof: Replace the self-inclusion by the identity scheme map. The two composition
comparisons are the unit comparisons. Naturality moves the direct-image identity
comparison past the inverse-image identity comparison. The unit form of the
adjunction identity law cancels the remaining unit and comparison. -/
theorem finiteCoverImageRestriction_id (f : X ⟶ Y) (V : X.Opens) :
    finiteCoverImageRestriction B f (U := V) (V := V) le_rfl = 𝟙 _ := by
  let A := ModuleCat.{u + 1} B
  have identityLaw (g : (V : Scheme) ⟶ (V : Scheme)) (hg : g = 𝟙 _)
      (h₁ : V.ι ≫ f = g ≫ (V.ι ≫ f)) (h₂ : V.ι = g ≫ V.ι) :
      Functor.whiskerLeft (upperStar A V.ι)
          (Functor.whiskerRight (upperStarLowerStarAdjunction A g).unit
            (lowerStar A (V.ι ≫ f))) ≫
        Functor.whiskerLeft (upperStar A V.ι ⋙ upperStar A g)
          (lowerStarComp A g (V.ι ≫ f) (V.ι ≫ f) h₁).hom ≫
        Functor.whiskerRight (upperStarComp A g V.ι V.ι h₂).inv
          (lowerStar A (V.ι ≫ f)) = 𝟙 (finiteCoverOpenImage B f V) := by
    subst g
    rw [lowerStarComp_id_left, upperStarComp_id_left]
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
      Category.id_comp, Category.comp_id, ← Functor.map_comp]
    simp only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
      Category.assoc]
    let F := lowerStar A (V.ι ≫ f)
    let G := (upperStar A V.ι).obj M
    change F.map ((upperStarLowerStarAdjunction A (𝟙 (V : Scheme))).unit.app G) ≫
      F.map ((lowerStarId A (V : Scheme)).hom.app
        ((upperStar A (𝟙 (V : Scheme))).obj G)) ≫
      F.map ((upperStarId A (V : Scheme)).hom.app G) = 𝟙 (F.obj G)
    have hn := (lowerStarId A (V : Scheme)).hom.naturality
      ((upperStarId A (V : Scheme)).hom.app G)
    dsimp only [Functor.id_map] at hn
    rw [← F.map_comp, ← hn, F.map_comp, ← Category.assoc, ← F.map_comp,
      upperStarId_hom_app_unit_app]
    simp
  exact identityLaw (X.homOfLE (show V ≤ V from le_rfl)) (X.homOfLE_rfl V)
    (by simp) (by simp)

/-- Canonical open-image restrictions compose.

Source: Stacks Project, Tag 00XZ; the canonical composite adjunction, as in
`upperStarComp_hom_app_unit_app` and the inverse/direct-image associativity laws.
(blueprint: new-finite-cover-restriction-composition)

Proof: Write k:V→W and l:W→Z for the two open inclusions. Their composite is
homOfLE(hVW.trans hWZ), by cancellation against the open immersion into X.
Evaluate the displayed transformations at M. Expand their three factors: the
unit, the direct-image composition isomorphism, and the inverse of the
inverse-image composition isomorphism. Move the latter across the next unit
using naturality of the unit. Move the resulting mapped morphism across the
next direct-image comparison using its naturality. The two units now form the
unit of the composite adjunction. The unit form of conjugateIsoEquiv identifies
this composite unit with the unit for k≫l, followed by the canonical comparison.
The direct-image associativity law combines the two direct-image comparisons;
the inverse-image associativity law combines the two inverse comparisons.
Cancel each adjacent inverse pair. What remains is exactly the restriction
for hVW.trans hWZ, with the specified comparison at V. Proof irrelevance identifies
the equality witnesses of the named composite morphisms. -/
theorem finiteCoverImageRestriction_comp (f : X ⟶ Y)
    (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z) :
    finiteCoverImageRestriction B f (hVW.trans hWZ) =
      finiteCoverImageRestriction B f hWZ ≫ finiteCoverImageRestriction B f hVW := by
  let A := ModuleCat.{u + 1} B
  let k := X.homOfLE hVW
  let l := X.homOfLE hWZ
  let kl := X.homOfLE (hVW.trans hWZ)
  have hkl : kl = k ≫ l := (X.homOfLE_homOfLE hVW hWZ).symm
  let K := upperStar A k
  let L := upperStar A l
  let KR := lowerStar A k
  let LR := lowerStar A l
  let R := lowerStar A kl
  let FZ := lowerStar A (Z.ι ≫ f)
  let FW := lowerStar A (W.ι ≫ f)
  let FV := lowerStar A (V.ι ≫ f)
  let t := upperStarComp A k l kl hkl
  let tl := upperStarComp A l Z.ι W.ι (by simp [l])
  let tk := upperStarComp A k W.ι V.ι (by simp [k])
  let tkl := upperStarComp A kl Z.ι V.ι (by simp [kl])
  let sl := lowerStarComp A l (Z.ι ≫ f) (W.ι ≫ f) (by simp [l])
  let sk := lowerStarComp A k (W.ι ≫ f) (V.ι ≫ f) (by simp [k])
  let skl := lowerStarComp A kl (Z.ι ≫ f) (V.ι ≫ f) (by simp [kl])
  let ss := lowerStarComp A k l kl hkl
  apply NatTrans.ext
  funext M
  let G := (upperStar A Z.ι).obj M
  let H := K.obj (L.obj G)
  have hn : FW.map (tl.inv.app M) ≫
      FW.map ((upperStarLowerStarAdjunction A k).unit.app ((upperStar A W.ι).obj M)) =
    FW.map ((upperStarLowerStarAdjunction A k).unit.app (L.obj G)) ≫
      FW.map (KR.map (K.map (tl.inv.app M))) := by
    rw [← FW.map_comp, ← FW.map_comp]
    exact congrArg FW.map ((upperStarLowerStarAdjunction A k).unit.naturality
      (tl.inv.app M))
  have hsk : FW.map (KR.map (K.map (tl.inv.app M))) ≫
      sk.hom.app (K.obj ((upperStar A W.ι).obj M)) =
    sk.hom.app H ≫ FV.map (K.map (tl.inv.app M)) :=
    sk.hom.naturality (K.map (tl.inv.app M))
  have hsl : sl.hom.app (L.obj G) ≫
      FW.map ((upperStarLowerStarAdjunction A k).unit.app (L.obj G)) =
    FZ.map (LR.map ((upperStarLowerStarAdjunction A k).unit.app (L.obj G))) ≫
      sl.hom.app (KR.obj H) :=
    (sl.hom.naturality ((upperStarLowerStarAdjunction A k).unit.app (L.obj G))).symm
  have hs : sl.hom.app (KR.obj H) ≫ sk.hom.app H =
      FZ.map (ss.hom.app H) ≫ skl.hom.app H := by
    exact (NatTrans.congr_app (lowerStarComp_assoc' A k l (Z.ι ≫ f)
      kl (W.ι ≫ f) (V.ι ≫ f) hkl (by simp [l]) (by simp [kl])) H).symm
  have ht : FV.map (K.map (tl.inv.app M)) ≫ FV.map (tk.inv.app M) =
      FV.map (t.inv.app G) ≫ FV.map (tkl.inv.app M) := by
    rw [← FV.map_comp, ← FV.map_comp]
    exact congrArg FV.map (NatTrans.congr_app
      (upperStarComp_named_assoc_inv B k l Z.ι kl W.ι V.ι
        hkl (by simp [l]) (by simp [kl])) M).symm
  have hu : FZ.map ((upperStarLowerStarAdjunction A l).unit.app G) ≫
      FZ.map (LR.map ((upperStarLowerStarAdjunction A k).unit.app (L.obj G))) ≫
        FZ.map (ss.hom.app H) =
    FZ.map ((upperStarLowerStarAdjunction A kl).unit.app G) ≫
      FZ.map (R.map (t.hom.app G)) := by
    have h := congrArg FZ.map
      (upperStarComp_hom_app_unit_app A k l G kl hkl).symm
    simpa only [Functor.map_comp, Adjunction.comp_unit_app, Category.assoc] using h
  have hskl : FZ.map (R.map (t.hom.app G)) ≫ skl.hom.app H =
      skl.hom.app ((upperStar A kl).obj G) ≫ FV.map (t.hom.app G) :=
    skl.hom.naturality (t.hom.app G)
  change FZ.map ((upperStarLowerStarAdjunction A kl).unit.app G) ≫
      skl.hom.app ((upperStar A kl).obj G) ≫ FV.map (tkl.inv.app M) =
    (FZ.map ((upperStarLowerStarAdjunction A l).unit.app G) ≫
      sl.hom.app (L.obj G) ≫ FW.map (tl.inv.app M)) ≫
    (FW.map ((upperStarLowerStarAdjunction A k).unit.app ((upperStar A W.ι).obj M)) ≫
      sk.hom.app (K.obj ((upperStar A W.ι).obj M)) ≫ FV.map (tk.inv.app M))
  symm
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hsk, reassoc_of% hsl, reassoc_of% hs,
    ht, reassoc_of% hu, reassoc_of% hskl]
  simp only [← FV.map_comp, Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Etale
