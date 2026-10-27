/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Category.Grp.AB

/-!
# Coproduct Ext computed with one injective resolution

Source: Stacks Project, Cohomology on Sites, Tags 07AA and 07AC; Derived Categories,
Tags 013K, 06XR and 05TD (blueprint: lem-trf-coproduct-ext-resolution-cohomology).

The Hom complex and its precomposition maps below are specializations of Mathlib's
additive coyoneda functor. All complexes are indexed by integers, including the
extension by zero in negative degrees. The theorem declarations state the six clauses
of the node, including canonical comparison equations and arbitrary isomorphic models.
-/

@[expose] public section

set_option autoImplicit false

universe u w vD uD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Hom into the integer-indexed extension of an injective resolution.
Source: Stacks Project, Tag 07AA (blueprint: lem-trf-coproduct-ext-resolution-cohomology).
Its degree-q differential is postcomposition with the resolution differential. -/
noncomputable abbrev injectiveResolutionHomComplex
    {D : Type uD} [Category.{vD} D] [Abelian D] {F : D}
    (P : InjectiveResolution F) (M : D) : CochainComplex AddCommGrpCat.{vD} ℤ :=
  ((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).obj P.cochainComplex

/-- Precomposition on the Hom complex, using Mathlib's additive coyoneda map.
Source: Stacks Project, Tags 07AA/07AC
(blueprint: lem-trf-coproduct-ext-resolution-cohomology). -/
noncomputable abbrev injectiveResolutionHomPrecomp
    {D : Type uD} [Category.{vD} D] [Abelian D] {F M N : D}
    (P : InjectiveResolution F) (f : N ⟶ M) :
    injectiveResolutionHomComplex P M ⟶ injectiveResolutionHomComplex P N :=
  ((preadditiveCoyoneda.map f.op).mapHomologicalComplex (.up ℤ)).app P.cochainComplex

section RingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

variable (F : ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))

/-- A nonnegative injective resolution exists; `P.cochainComplex` is its zero extension.
Source: Stacks Project, Tags 079Q, 079H and 013K
(blueprint: lem-trf-coproduct-ext-resolution-cohomology).

Proof: lem-weil-pbc-ring-sheaves-grothendieck makes module sheaves Grothendieck abelian.
Apply lem-sp-grothendieck-enough-injectives and clause (1) of
lem-weil-pbc-left-exact-injective-resolution-degree-zero to F. The bundled resolution
has injective terms and an exact augmentation; Mathlib's extension is zero below zero. -/
theorem coproduct_ext_nonempty_injectiveResolution : Nonempty (InjectiveResolution F) := by
  sorry

variable {J R F}

/-- Hom cohomology is canonically independent of the resolution.
Source: Stacks Project, Tags 06XR and 07AA
(blueprint: lem-trf-coproduct-ext-resolution-cohomology).

Proof: lem-weil-pbc-ext-via-injective-resolution identifies both groups with Ext(M,F).
Comparison maps over the identity induce this same identification: any two comparison
maps are homotopic, and comparison maps in opposite directions compose homotopically
to the identity. Thus the displayed map on cohomology is the canonical isomorphism. -/
theorem coproduct_ext_resolution_independent
    (P Q : InjectiveResolution F)
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (q : ℕ) :
    ∃ e : (injectiveResolutionHomComplex P M).homology (q : ℤ) ≅
        (injectiveResolutionHomComplex Q M).homology (q : ℤ),
      ∀ φ : InjectiveResolution.Hom P Q (𝟙 F),
        e.hom = HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).map
            φ.hom') (q : ℤ) := by
  sorry

variable (P : InjectiveResolution F) {I : Type w}
  (E : I → ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))

/-- Restriction along the coprojections is an isomorphism of the actual Hom complexes.
Source: Stacks Project, Tags 07AA/07AC
(blueprint: lem-trf-coproduct-ext-resolution-cohomology).

Proof: In each degree the coproduct universal property bijectively identifies a map
out of the sum with its restrictions. The inverse is the unique coproduct descent.
Both maps are additive; associativity makes them commute with postcomposition by d_J.
For an isomorphic model M, precompose by the specified isomorphism and its inverse.
This includes the empty coproduct and arbitrary repeated indices. -/
theorem coproduct_ext_resolution_complex_iso
    {A : Type u} (i : A → I)
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (e : M ≅ ∐ (fun a : A ↦ E (i a))) :
    ∃ ρ : injectiveResolutionHomComplex P M ≅
        ∏ᶜ (fun a : A ↦ injectiveResolutionHomComplex P (E (i a))),
      ∀ a : A, ρ.hom ≫ Pi.π _ a =
        injectiveResolutionHomPrecomp P (Sigma.ι (fun a : A ↦ E (i a)) a ≫ e.inv) := by
  sorry

/-- The induced cohomology comparison is restriction to each summand.
Source: Stacks Project, Tags 07AA/07AC
(blueprint: lem-trf-coproduct-ext-resolution-cohomology).

Proof: Use coproduct_ext_resolution_complex_iso. Cycles of the product are coordinatewise
products of cycles. Apply lem-pc-abelian-groups-exact-products to the short exact sequences
cycles -> terms -> boundaries and boundaries -> cycles -> cohomology. Boundaries of the
product are products of boundaries, and the quotient is the product of cohomology.
The resulting comparison sends a cocycle class to its restricted classes, as stated. -/
theorem coproduct_ext_resolution_cohomology
    {A : Type u} (i : A → I)
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (e : M ≅ ∐ (fun a : A ↦ E (i a))) (q : ℕ) :
    ∃ σ : (injectiveResolutionHomComplex P M).homology (q : ℤ) ≅
        ∏ᶜ (fun a : A ↦ (injectiveResolutionHomComplex P (E (i a))).homology (q : ℤ)),
      ∀ a : A, σ.hom ≫ Pi.π _ a = HomologicalComplex.homologyMap
        (injectiveResolutionHomPrecomp P (Sigma.ι (fun a : A ↦ E (i a)) a ≫ e.inv))
        (q : ℤ) := by
  sorry

/-- The degree-zero comparison sends h to the class of the augmented h and is natural
for every map between coproducts, including arbitrary isomorphic models.
Source: Stacks Project, Tag 05TD, final paragraph, and Tags 07AA/07AC
(blueprint: lem-trf-coproduct-ext-resolution-cohomology).

Proof: Exactness identifies F with the kernel of J^0 -> J^1. Thus every degree-zero
cycle M -> J^0 factors uniquely through the augmentation. Negative terms are zero,
so there are no boundaries in degree zero. The resulting map is additive and bijective.
For any f : N -> M, associativity gives (ι h) f = ι (h f), proving naturality even
when f mixes summands. The same equation proves compatibility with every chosen model. -/
theorem coproduct_ext_resolution_degree_zero :
    ∃ η : ∀ (A : Type u) (i : A → I)
        (M : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)),
        (M ≅ ∐ (fun a : A ↦ E (i a))) →
        ((preadditiveCoyoneda.obj (op M)).obj F ≅
          (injectiveResolutionHomComplex P M).homology 0),
      (∀ (A : Type u) (i : A → I)
        (M : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (e : M ≅ ∐ (fun a : A ↦ E (i a))) (h : M ⟶ F)
        (z : (injectiveResolutionHomComplex P M).cycles 0),
        (injectiveResolutionHomComplex P M).iCycles 0 z =
            h ≫ P.ι.f 0 ≫ (P.cochainComplexXIso 0 0 rfl).inv →
          (η A i M e).hom h = (injectiveResolutionHomComplex P M).homologyπ 0 z) ∧
      (∀ (A B : Type u) (i : A → I) (k : B → I)
        (M N : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (eM : M ≅ ∐ (fun a : A ↦ E (i a)))
        (eN : N ≅ ∐ (fun b : B ↦ E (k b))) (f : N ⟶ M),
        (preadditiveCoyoneda.map f.op).app F ≫ (η B k N eN).hom =
          (η A i M eM).hom ≫
            HomologicalComplex.homologyMap (injectiveResolutionHomPrecomp P f) 0) := by
  sorry

/-- Positive Ext vanishing on summands implies vanishing on every small coproduct.
Source: Stacks Project, Tag 07AC (blueprint: lem-trf-coproduct-ext-resolution-cohomology).

Proof: By coproduct_ext_resolution_independent and lem-weil-pbc-ext-via-injective-resolution,
the hypothesis is resolution-independent positive Ext vanishing. Every factor of the
product in coproduct_ext_resolution_cohomology is then zero, so the product is zero.
The specified isomorphism transports this conclusion to M. Empty products in Ab are
zero; no distinctness of summands is used. -/
theorem coproduct_ext_resolution_vanishing
    (hExt : ∀ (j : I) (q : ℕ), 0 < q →
      IsZero ((injectiveResolutionHomComplex P (E j)).homology (q : ℤ)))
    {A : Type u} (i : A → I)
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (e : M ≅ ∐ (fun a : A ↦ E (i a))) (q : ℕ) (hq : 0 < q) :
    IsZero ((injectiveResolutionHomComplex P M).homology (q : ℤ)) := by
  sorry

end RingedSite

end CategoryTheory
