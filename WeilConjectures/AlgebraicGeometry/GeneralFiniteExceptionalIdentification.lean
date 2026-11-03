/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFiniteCompactIdentification
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.GeneralFiniteExceptionalCounitUniqueness
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteProCoefficientCounitTransport
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation

/-! # Identification of counit-characterized finite exceptional comparisons

Source: sk-thm-purity-transport proof, Step 1; sk-lem-sp-reduction, equation (10.15).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

open Etale.FiniteSmoothPurity

local instance (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem diagonalCounitNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {K K' : proCategory A Y}
    (hK : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedUpperShriek A f).obj ((origin A Y).obj K)))
    (hK' : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedUpperShriek A f).obj ((origin A Y).obj K')))
    (v : K ⟶ K') :
    (proCompact A f).map ((exceptional A f).map v) ≫ proCounit A f K' =
      proCounit A f K ≫ v := by
  have hs := compactSiteNaturality A f hK hK'
    ((Etale.rightDerivedUpperShriek A f).map ((origin A Y).map v))
  have he := (Etale.rightDerivedUpperShriekAdjunction A f).counit.naturality
    ((origin A Y).map v)
  have hc := (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at he hc
  simp only [proCounit, exceptional, Functor.comp_map, Category.assoc]
  rw [reassoc_of% hs, ← (comparison A Y).map_comp_assoc, he,
    (comparison A Y).map_comp_assoc]
  erw [hc]


attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The live counit-characterized comparison is the transported ordinary scalar mate.
Source: sk-thm-purity-transport proof, Step 1 (exceptional adjunction constituent),
and sk-lem-sp-reduction, equation (10.15).
(blueprint: lem-pur-general-side-exceptional-identification).

Proof: write J for the ordinary origin of K and M for f_A^! J. Its bounded
constructible finite-Tor property puts both scalar extensions and all site support
comparisons on their isomorphism loci. Decompose compact support into proper direct
image after open extension. The proper comparison is the mate of the scalar/pullback
square, and the open comparison is the derived ordinary extension-by-zero comparison.
Paste these squares with the scalar/comparison identification; this identifies the
live compact comparison with proCompactCoefficientMap conjugated by
sideScalarIdentification. Transport the supplied counit equation along this
identification. The ordinary mate transported to pro-etale complexes satisfies the
same equation by finiteProCoefficientCounitTransport. Cancel the invertible compact
comparison. Express maps between comparison images by the ordinary comparison
adjunction and its invertible units on bounded-below objects. Naturality of the site
support comparison reduces equality of their pro-etale counit transposes to equality
of ordinary compact-support/exceptional transposes. The ordinary adjunction Hom
bijection is injective, so the two maps agree. No orientation or purity map occurs
in this argument; in particular it precedes purity and biduality. -/
theorem sideExceptionalCoefficient_identification
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (φ : A →+* B) (f : X ⟶ Y) [HasCompactification f]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ X)]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ Y)]
    (c : Etale.FiniteSmoothPurity.exceptional A f ⋙ sideScalar φ X ⟶
      sideScalar φ Y ⋙ Etale.FiniteSmoothPurity.exceptional B f)
    (hcounit : ∀ K : Etale.FiniteSmoothPurity.proCategory A Y,
      Etale.FiniteSmoothPurity.IsCtf A Y K →
      canonicalCompactReduction f φ K ≫
          (Etale.FiniteSmoothPurity.proCompact B f).map (c.app K) ≫
          Etale.FiniteSmoothPurity.proCounit B f ((sideScalar φ Y).obj K) =
        (sideScalar φ Y).map (Etale.FiniteSmoothPurity.proCounit A f K))
    (K : Etale.FiniteSmoothPurity.proCategory A Y)
    (hK : Etale.FiniteSmoothPurity.IsCtf A Y K)
    (hG : Etale.DerivedCategory.boundedConstructibleFiniteTor A X
      ((Etale.rightDerivedUpperShriek A f).obj
        ((Etale.FiniteSmoothPurity.origin A Y).obj K)))
    (hGB : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedUpperShriek B f).obj
        ((Etale.FiniteSmoothPurity.origin B Y).obj
          ((Etale.FiniteSmoothPurity.proScalar φ Y).obj K)))) :
    c.app K ≫ (Etale.FiniteSmoothPurity.exceptional B f).map
        ((sideScalarIdentification φ Y).hom.app K) =
      (sideScalarIdentification φ X).hom.app
          ((Etale.FiniteSmoothPurity.exceptional A f).obj K) ≫
        Etale.FiniteSmoothPurity.proCoefficientMap φ f K := by
  let M := (Etale.rightDerivedUpperShriek A f).obj ((origin A Y).obj K)
  have hp : _root_.DerivedCategory.TStructure.t.plus ((ordinaryScalar φ X).obj M) := by
    simpa only [ordinaryScalar] using
      Etale.ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X M hG.2
  have hside : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedUpperShriek B f).obj
        ((origin B Y).obj ((sideScalar φ Y).obj K))) :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      (((Etale.rightDerivedUpperShriek B f).mapIso
        ((origin B Y).mapIso ((sideScalarIdentification φ Y).app K))).symm) hGB
  have hcompact : IsIso (proCompactCoefficientMap φ f ((exceptional A f).obj K)) := by
    have ha : IsIso (compactSiteMap A f M) := by
      unfold compactSiteMap
      rw [dif_pos hG.1.1.1]
      infer_instance
    have hb : IsIso (compactSiteInverse B f ((ordinaryScalar φ X).obj M)) := by
      unfold compactSiteInverse
      rw [dif_pos hp]
      infer_instance
    change IsIso (proCompactCoefficientMap φ f ((comparison A X).obj M))
    rw [compactCoefficientAtOrigin φ f M hG]
    have := Etale.ExceptionalCoefficients.compactSupport_isIso φ
      (HasCompactification.compactification f) M
    infer_instance
  have hcan : IsIso (canonicalCompactReduction f φ K) := by
    have hi : IsIso (canonicalCompactReduction f φ K ≫
        (proCompact B f).map ((sideScalarIdentification φ X).hom.app
          ((exceptional A f).obj K))) := by
      rw [sideCompactCoefficient_identification φ f K hG]
      infer_instance
    exact IsIso.of_isIso_comp_right (canonicalCompactReduction f φ K)
      ((proCompact B f).map ((sideScalarIdentification φ X).hom.app
        ((exceptional A f).obj K)))
  let a := c.app K ≫ (exceptional B f).map ((sideScalarIdentification φ Y).hom.app K)
  let b := (sideScalarIdentification φ X).hom.app ((exceptional A f).obj K) ≫
    proCoefficientMap φ f K
  have hleft : canonicalCompactReduction f φ K ≫ (proCompact B f).map a ≫
        proCounit B f ((proScalar φ Y).obj K) =
      (sideScalarIdentification φ Y).hom.app ((proCompact A f).obj
        ((exceptional A f).obj K)) ≫ (proScalar φ Y).map (proCounit A f K) := by
    dsimp only [a]
    rw [(proCompact B f).map_comp]
    simp only [Category.assoc]
    rw [diagonalCounitNaturality B f hside hGB ((sideScalarIdentification φ Y).hom.app K)]
    rw [reassoc_of% (hcounit K hK)]
    exact (sideScalarIdentification φ Y).hom.naturality (proCounit A f K)
  have hright : canonicalCompactReduction f φ K ≫ (proCompact B f).map b ≫
        proCounit B f ((proScalar φ Y).obj K) =
      (sideScalarIdentification φ Y).hom.app ((proCompact A f).obj
        ((exceptional A f).obj K)) ≫ (proScalar φ Y).map (proCounit A f K) := by
    dsimp only [b]
    rw [(proCompact B f).map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc, sideCompactCoefficient_identification φ f K hG]
    simp only [Category.assoc]
    rw [finiteProCoefficientCounitTransport φ f K hK hG hGB]
    unfold proCompactCoefficientInverse
    rw [dif_pos hcompact]
    simp only [IsIso.hom_inv_id_assoc]
  have ht : (proCompact B f).map a ≫ proCounit B f ((proScalar φ Y).obj K) =
      (proCompact B f).map b ≫ proCounit B f ((proScalar φ Y).obj K) :=
    (cancel_epi (canonicalCompactReduction f φ K)).mp (hleft.trans hright.symm)
  let e := ((sideComparisonReductionIso (T := X) φ).app M).symm
  apply (cancel_epi e.hom).mp
  apply exceptionalCounit_injective B f ((ordinaryScalar φ X).obj M) hp
    ((proScalar φ Y).obj K) hGB
  simpa only [a, b, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ (proCompact B f).map e.hom ≫ z) ht

end AlgebraicGeometry.ProEtale
