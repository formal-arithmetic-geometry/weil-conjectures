/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.FibredFppfSpaceModuleComparisons
public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction

/-! # Maps from quasi-coherent modules on a groupoid quotient

Source: Stacks Project, stacks-sheaves.tex, Tag 076S (lemma-map-from-quasi-coherent)
(blueprint: lem-sfb-groupoid-maps-from-quasicoherent).

Restrictions are literal evaluations on étale scheme charts, with the existing
regular-function universe lift. Comparisons are uniquely specified on local tensors.
Only comparisons for the quasi-coherent source are inverted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite CategoryTheory.Limits

namespace CategoryTheory

namespace GroupoidModuleHom

variable {S : Scheme.{u}} {U R : AlgebraicSpace S}
  {s t : R ⟶ U} {e : U.obj.obj ⟶ R.obj.obj} {i : R.obj.obj ⟶ R.obj.obj}
  {c : pullback s.hom.hom t.hom.hom ⟶ R.obj.obj}
  {C : BasedCategory.{v, w} (Over S)}
  {x : BasedFunctor (discreteModuli U.obj.obj) C}
  (P : SpaceGroupoidQuotientPresentation s.hom.hom t.hom.hom e i c C x)

/-- Comparison along the source map, using the source test for the common restriction.
Source: Stacks 076S (blueprint: lem-sfb-groupoid-maps-from-quasicoherent). -/
def sourceComparison
    (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1)) :=
  moduliSpaceComparison P.stack.1 s ((discreteModuliMap s.hom.hom).comp x) x
    ⟨Iso.refl _, fun T ↦ IsHomLift.id
      (((discreteModuliMap s.hom.hom).comp x).w_obj T)⟩ M

/-- Comparison along the target map, transported through the canonical groupoid arrow.
Source: Stacks 076S (blueprint: lem-sfb-groupoid-maps-from-quasicoherent). -/
def targetComparison
    (M : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1)) :=
  moduliSpaceComparison P.stack.1 t ((discreteModuliMap s.hom.hom).comp x) x
    P.arrows M

/-- The canonical source comparison as an isomorphism, retaining its actual forward map.
Source: Stacks 076S (blueprint: lem-sfb-groupoid-maps-from-quasicoherent). -/
def sourceComparisonIso
    (F : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1))
    (hF : F.IsQuasicoherent) :=
  letI : IsIso (sourceComparison P F) :=
    ((fibred_fppf_space_module_comparisons P.stack.1).2.2.2.2.2.2.2 F hF).2
      R U s ((discreteModuliMap s.hom.hom).comp x) x
        ⟨Iso.refl _, fun T ↦ IsHomLift.id
          (((discreteModuliMap s.hom.hom).comp x).w_obj T)⟩
  asIso (sourceComparison P F)

/-- The canonical target comparison as an isomorphism, retaining its actual forward map.
Source: Stacks 076S (blueprint: lem-sfb-groupoid-maps-from-quasicoherent). -/
def targetComparisonIso
    (F : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1))
    (hF : F.IsQuasicoherent) :=
  letI : IsIso (targetComparison P F) :=
    ((fibred_fppf_space_module_comparisons P.stack.1).2.2.2.2.2.2.2 F hF).2
      R U t ((discreteModuliMap s.hom.hom).comp x) x P.arrows
  asIso (targetComparison P F)

/-- Precisely the comparison equation in Tag 076S, read in diagrammatic composition order.
Only the F comparisons are inverted; H is an arbitrary module sheaf.
Source: Stacks 076S (blueprint: lem-sfb-groupoid-maps-from-quasicoherent). -/
def Compatible (F : (SheafOfModules.isQuasicoherent
        (moduliModuleRings C P.stack.1)).FullSubcategory)
    (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1))
    (a : moduliSpaceRestriction P.stack.1 x F.obj ⟶
      moduliSpaceRestriction P.stack.1 x H) : Prop :=
  (sourceComparisonIso P F.obj F.property).inv ≫
      (ambientModuleTensorPullback s).map a ≫ sourceComparison P H =
    (targetComparisonIso P F.obj F.property).inv ≫
      (ambientModuleTensorPullback t).map a ≫ targetComparison P H

/-- Restriction is injective and identifies maps out of a quasi-coherent module with
exactly the compatible maps on U; its inverse commutes with source and target maps.
No local quasi-coherence or flat-compatibility hypothesis is imposed on H.

Source: Stacks Project, stacks-sheaves.tex, Tag 076S (lemma-map-from-quasi-coherent)
(blueprint: lem-sfb-groupoid-maps-from-quasicoherent).

Proof:
1. By lem-sfb-stackification-module-equivalence, precomposition with the fppf
stackification identifies all module Hom sets and their restrictions. Work on the
presheaf quotient. An arrow (f,r) factors as its groupoid arrow followed by the
special arrow over f, using the given groupoid laws.
2. By lem-sfb-fibred-fppf-space-module-comparisons the comparisons of F are
isomorphisms. Given a compatible map a on U, on a test u:T→U define
b_u = c_u^H ∘ u^*a ∘ (c_u^F)⁻¹. Evaluating at T gives a map of the actual
module values, by lem-sfb-stack-quasi-coherent-scheme-restriction.
3. The composition law for comparisons gives b_u c_f^F = c_f^H f^*b_v for a
special arrow. On sections this is its required naturality square, including identities.
4. For a groupoid arrow r, pull the compatibility equation back along r and use
its canonical two-isomorphism. Cancelling only F comparisons gives the naturality
square for the groupoid arrow. The factorization in step 1 proves naturality for
every arrow, hence these section maps define a global module morphism.
5. Conversely naturality of any global morphism ψ gives ψ_R c_s^F = c_s^H s^*ψ_U
and the target analogue, so its restriction is compatible. At any test u it forces
ψ_u = c_u^H u^*ψ_U (c_u^F)⁻¹. Its restriction therefore determines all its values,
proving injectivity. For étale u all comparisons are restriction identifications,
so the morphism constructed in steps 2–4 restricts to a itself.
6. This proves bijectivity onto Compatible. Precomposition by any map between
quasi-coherent sources and postcomposition by any target map commute with
restriction. Uniqueness of the extension proves the displayed inverse naturality.
The flatness and local finite presentation hypotheses of Tag 076S are retained. -/
theorem restriction_equiv_compatible
    (hs : MapIsFlat s) (ht : MapIsFlat t)
    (hslfp : MapIsLocallyOfFinitePresentation s)
    (htlfp : MapIsLocallyOfFinitePresentation t) :
    (∀ (F : (SheafOfModules.isQuasicoherent
        (moduliModuleRings C P.stack.1)).FullSubcategory)
      (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1)),
      Function.Injective (fun a : F.obj ⟶ H ↦
        moduliSpaceRestrictionMap P.stack.1 x a)) ∧
    ∃ E : ∀ (F : (SheafOfModules.isQuasicoherent
        (moduliModuleRings C P.stack.1)).FullSubcategory)
      (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1)),
      (F.obj ⟶ H) ≃ {a // Compatible P F H a},
      (∀ (F : (SheafOfModules.isQuasicoherent
        (moduliModuleRings C P.stack.1)).FullSubcategory)
        (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1))
        (a : F.obj ⟶ H), (E F H a).val =
          moduliSpaceRestrictionMap P.stack.1 x a) ∧
      ∀ (F F' : (SheafOfModules.isQuasicoherent
        (moduliModuleRings C P.stack.1)).FullSubcategory)
        (H H' : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C P.stack.1))
        (a : F'.obj ⟶ F.obj) (b : H ⟶ H')
        (z : {q // Compatible P F H q}) (z' : {q // Compatible P F' H' q}),
        z'.val = moduliSpaceRestrictionMap P.stack.1 x a ≫ z.val ≫
          moduliSpaceRestrictionMap P.stack.1 x b →
        (E F' H').symm z' = a ≫ (E F H).symm z ≫ b := by
  sorry

end GroupoidModuleHom

end CategoryTheory
