/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheaves
public import WeilConjectures.AlgebraicGeometry.ClassicalDerivedDefinitions
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension

/-!
# Extension closure of classical module sheaves

Source: Weil conjectures blueprint, `sk-cor-pe-classical-derived`, extension paragraph
(blueprint: det-pe-classical-derived-weak-serre).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- An extension of two comparison sheaves is again in the comparison essential image.
Source: Weil conjectures blueprint, `sk-cor-pe-classical-derived`, extension paragraph
(blueprint: det-pe-classical-derived-weak-serre).

Proof: the source library's `etaleOrigin_of_shortExact` (resting on the full faithfulness of
the comparison inverse image on bounded-below derived categories) puts the middle term `E` of an
extension of two comparison inverse images in the essential image of the comparison inverse
image, say `E ≅ ν^* F`.  Every comparison inverse image is classical by the module
classical-sheaves equivalence, and classicality is transported along `E ≅ ν^* F` by naturality of
the continuity maps.  Since the comparison inverse image is fully faithful, the adjunction counit
is invertible exactly on its essential image, so the counit at `E` is an isomorphism.
-/
theorem classicalExtension
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F₁ F₂ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (E : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (i : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F₁ ⟶ E)
    (p : E ⟶ (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F₂)
    (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact) :
    IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.app E) ∧
      IsClassicalModuleFor X Λ E := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  have hPiso {F G : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
      (hF : IsClassicalModuleFor X Λ F) : IsClassicalModuleFor X Λ G := by
    intro I _ _ Q
    have hmap := continuityMap_natural Q e.hom.hom
    have : IsIso (Functor.whiskerLeft Q.diagram.op e.hom.hom) := by
      change IsIso (Functor.isoWhiskerLeft Q.diagram.op
        ((sheafToPresheaf _ _).mapIso e)).hom
      infer_instance
    apply (isIso_comp_left_iff
      (colimMap (Functor.whiskerLeft Q.diagram.op e.hom.hom)) _).mp
    rw [hmap]
    have : IsIso (continuityMap Q F.obj) := hF Q
    infer_instance
  have hL : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsClassicalModuleFor X Λ (L.obj F) := by
    intro F
    let hclass := (proEtaleClassicalSheaves X).2.2 Λ
    let K := hclass.choose
    have hK : K ⋙ ObjectProperty.ι _ = L := hclass.choose_spec.1
    have hEq := congrArg (fun T ↦ T.obj F) hK
    change (K.obj F).obj = L.obj F at hEq
    intro I _ _ Q
    change IsIso (continuityMap Q (L.obj F).obj)
    rw [← hEq]
    exact (K.obj F).property Q
  have hE : AlgebraicGeometry.ProEtale.etaleOrigin
      (ModuleCat.{u + 1} Λ) X E :=
    etaleOrigin_of_shortExact hS
      ⟨F₁, ⟨Iso.refl _⟩⟩ ⟨F₂, ⟨Iso.refl _⟩⟩
  let hE' := hE
  obtain ⟨F, ⟨e⟩⟩ := hE
  have hsource : IsClassicalModuleFor X Λ E := hPiso e (hL F)
  let adj := comparisonAdjunction (ModuleCat.{u + 1} Λ) X
  have hEiso : IsIso (adj.counit.app E) := by
    apply (adj.isIso_counit_app_iff_mem_essImage).2
    change L.essImage E
    exact hE'
  exact ⟨hEiso, hsource⟩

end AlgebraicGeometry.ProEtale
