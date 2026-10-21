/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SequenceSiteCompletionProjection
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.RingedPresentationTransport
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Open extension on ringed sequence sites

Source: Stacks Project, sites-modules.tex, Tags 03DI, 03DJ and 03CY;
sites.tex, Tags 04GZ and 0791
(blueprint: lem-pur-sequence-site-open-extension).

The open site is expressed as the slice of the base site. For the pro-etale site
this is the recorded `Scheme.ProEt.sliceEquiv`, including its covering topology.
All level functors below are the recorded direct-sum-and-sheafification functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r u s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory
namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (U : C)

/-- Restrict the actual coefficient tower to the open slice.
Source: Stacks 04IE (blueprint: lem-pur-sequence-site-open-extension). -/
abbrev openTower (B : ℕ → Sheaf J CommRingCat.{max c v r}) := fun n ↦ (B n).over U

/-- Restrict the adjacent coefficient homomorphisms, without changing their sections.
Source: Stacks 04IE (blueprint: lem-pur-sequence-site-open-extension). -/
abbrev openTowerMap (B : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) :=
  fun n ↦ (J.overPullback CommRingCat.{max c v r} U).map (τ n)

/-- The summand section in the actual sheafified extension. The recorded normalized
adjunction unit is precisely the summand inclusion followed by sheafification.
Source: Stacks 03DI (blueprint: lem-pur-sequence-site-open-extension). -/
def openExtensionSection (R : Sheaf J CommRingCat.{max c v r})
    (M : Mod.{max c v, v, max c v r} (J.over U) (R.over U)) (X : (Over U)ᵒᵖ)
    (x : M.val.obj X) :=
  (SheafOfModules.localizedSystemAdjunction.{c, v, r} R U).unit.app M |>.val.app X <| x

/-- Coefficient comparisons for open extension, normalized on the actual summands.
The normalization says identity on the common underlying additive sheafification.
`composition` and `overComposition` are the identity scalar-restriction comparisons.
Source: Stacks 03DI and 03CY (blueprint: lem-pur-sequence-site-open-extension). -/
structure SequenceOpenCoefficientData where
  comparison : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S),
    res ((J.overPullback CommRingCat.{max c v r} U).map φ) ⋙
        SheafOfModules.localizedSystemExtension.{c, v, r} R U ≅
      SheafOfModules.localizedSystemExtension.{c, v, r} S U ⋙ res φ
  summand : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (M : Mod.{max c v, v, max c v r} (J.over U) (S.over U)) (X : (Over U)ᵒᵖ)
    (x : M.val.obj X),
    ((comparison φ).hom.app M).val.app (op X.unop.left)
      (openExtensionSection.{c, v, r} J U R
        ((res ((J.overPullback CommRingCat.{max c v r} U).map φ)).obj M) X x) =
      openExtensionSection.{c, v, r} J U S M X x
  restriction : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S),
    res φ ⋙ SheafOfModules.localizedSystemRestriction.{c, v, r} R U ≅
      SheafOfModules.localizedSystemRestriction.{c, v, r} S U ⋙
        res ((J.overPullback CommRingCat.{max c v r} U).map φ)
  restriction_section : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (M : Mod.{c, v, max c v r} J S) (X : (Over U)ᵒᵖ),
    HEq (fun x ↦ ((restriction φ).hom.app M).val.app X x)
      (fun x : M.val.obj (op X.unop.left) ↦ x)
  unit : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (M : Mod.{max c v, v, max c v r} (J.over U) (S.over U)),
    (SheafOfModules.localizedSystemAdjunction.{c, v, r} R U).unit.app
        ((res ((J.overPullback CommRingCat.{max c v r} U).map φ)).obj M) ≫
      (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).map
        ((comparison φ).hom.app M) ≫
      (restriction φ).hom.app
        ((SheafOfModules.localizedSystemExtension.{c, v, r} S U).obj M) =
    (res ((J.overPullback CommRingCat.{max c v r} U).map φ)).map
      ((SheafOfModules.localizedSystemAdjunction.{c, v, r} S U).unit.app M)
  counit : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (N : Mod.{c, v, max c v r} J S),
    (SheafOfModules.localizedSystemExtension.{c, v, r} R U).map
        ((restriction φ).inv.app N) ≫
      (SheafOfModules.localizedSystemAdjunction.{c, v, r} R U).counit.app ((res φ).obj N) =
    (comparison φ).hom.app
        ((SheafOfModules.localizedSystemRestriction.{c, v, r} S U).obj N) ≫
      (res φ).map ((SheafOfModules.localizedSystemAdjunction.{c, v, r} S U).counit.app N)
  composition : ∀ {R S T : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) (ψ : S ⟶ T),
    res ψ ⋙ res φ ≅ res (φ ≫ ψ)
  composition_section : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (M : Mod.{c, v, max c v r} J T) (X : Cᵒᵖ),
    HEq (fun x ↦ ((composition φ ψ).hom.app M).val.app X x)
      (fun x : M.val.obj X ↦ x)
  overComposition : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (ψ : S ⟶ T),
    res ((J.overPullback CommRingCat.{max c v r} U).map ψ) ⋙
        res ((J.overPullback CommRingCat.{max c v r} U).map φ) ≅
      res ((J.overPullback CommRingCat.{max c v r} U).map (φ ≫ ψ))
  overComposition_section : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (ψ : S ⟶ T)
    (M : Mod.{max c v, v, max c v r} (J.over U) (T.over U)) (X : (Over U)ᵒᵖ),
    HEq (fun x ↦ ((overComposition φ ψ).hom.app M).val.app X x)
      (fun x : M.val.obj X ↦ x)
  comp : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (ψ : S ⟶ T)
    (M : Mod.{max c v, v, max c v r} (J.over U) (T.over U)),
    (SheafOfModules.localizedSystemExtension.{c, v, r} R U).map
        ((overComposition φ ψ).hom.app M) ≫ (comparison (φ ≫ ψ)).hom.app M =
      (comparison φ).hom.app
          ((res ((J.overPullback CommRingCat.{max c v r} U).map ψ)).obj M) ≫
        (res φ).map ((comparison ψ).hom.app M) ≫
        (composition φ ψ).hom.app
          ((SheafOfModules.localizedSystemExtension.{c, v, r} T U).obj M)
  identity : ∀ (R : Sheaf J CommRingCat.{max c v r})
    (M : Mod.{max c v, v, max c v r} (J.over U) (R.over U)) (X : Cᵒᵖ),
    HEq (fun x ↦ ((comparison (𝟙 R)).hom.app M).val.app X x)
      (fun x : ((SheafOfModules.localizedSystemExtension.{c, v, r} R U).obj M).val.obj X ↦ x)

variable (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The geometric localization and the actual levelwise extension/restriction adjunction.
The slice presentation uses the constant representable subterminal, never an invented
representing object of the sequence site.
Source: Stacks 04GZ, 0791, 04IE, 03DI and 03DJ
(blueprint: lem-pur-sequence-site-open-extension). -/
structure SequenceOpenOrdinary where
  coefficients : SequenceOpenCoefficientData.{c, v, r} J U
  geometric : RingedToposMorphismOfUniverses
    (ring.{max c v, v, max c v r} (coefficientSequenceTopology (J.over U))
      (systemRing.{max c v, v, max c v r} (J.over U) (openTower.{c, v, r} J U B)
    (openTowerMap.{c, v, r} J U B τ)))
    (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ))
  inverseUnderlying : geometric.inverse ⋙
      sheafToPresheaf (coefficientSequenceTopology (J.over U)) (Type (max c v r)) ≅
    sheafToPresheaf (coefficientSequenceTopology J) (Type (max c v r)) ⋙
      (Functor.whiskeringLeft (ℕ × Over U)ᵒᵖ (ℕ × C)ᵒᵖ (Type (max c v r))).obj
        ((𝟭 ℕ).prod (Over.forget U)).op
  ring_identity : ∀ (X : (ℕ × Over U)ᵒᵖ)
    (a : (systemRing.{max c v, v, max c v r} (J.over U) (openTower.{c, v, r} J U B)
    (openTowerMap.{c, v, r} J U B τ)).obj.obj X),
    geometric.ringMap.hom.app X
      ((inverseUnderlying.inv.app
        ((sheafCompose (coefficientSequenceTopology J) (forget RingCat.{max c v r})).obj
          (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J
    B τ)))).app X a) = a
  H : Sheaf (coefficientSequenceTopology J) (Type (max c v r))
  constantRepresentable : H.obj ≅ (CategoryTheory.Prod.snd ℕ C).op ⋙
    CategoryTheory.uliftYoneda.obj U
  subterminal : ∀ (T : Sheaf (coefficientSequenceTopology J) (Type (max c v r))),
    Subsingleton (T ⟶ H)
  slice : Sheaf (coefficientSequenceTopology (J.over U)) (Type (max c v r)) ≌ Over H
  localization : geometric.inverse ⋙ slice.functor ≅ Over.star H
  L : Systems.{c, v, max c v r} J B τ ⥤
    Systems.{max c v, v, max c v r} (J.over U) (openTower.{c, v, r} J U B) (openTowerMap.{c, v,
    r} J U B τ)
  L_obj : ∀ (M : Systems.{c, v, max c v r} J B τ) (X : (ℕ × Over U)ᵒᵖ),
    HEq ((L.obj M).val.obj X) (M.val.obj (op (X.unop.1, X.unop.2.left)))
  L_map : ∀ {M N : Systems.{c, v, max c v r} J B τ} (f : M ⟶ N) (X : (ℕ × Over U)ᵒᵖ),
    HEq (fun x ↦ (L.map f).val.app X x)
      (fun x : M.val.obj (op (X.unop.1, X.unop.2.left)) ↦
        f.val.app (op (X.unop.1, X.unop.2.left)) x)
  L_restrict : ∀ (M : Systems.{c, v, max c v r} J B τ)
    {X Y : (ℕ × Over U)ᵒᵖ} (f : X ⟶ Y),
    HEq (fun x ↦ (L.obj M).val.map f x)
      (fun x : M.val.obj (op (X.unop.1, X.unop.2.left)) ↦
        M.val.map (((𝟭 ℕ).prod (Over.forget U)).op.map f) x)
  moduleInverse : L ⊣ geometric.modules
  moduleUnderlying : L ⋙ completionUnderlying
      (coefficientSequenceTopology (J.over U))
      (systemRing.{max c v, v, max c v r} (J.over U)
        (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ)) ≅
    completionUnderlying (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) ⋙ geometric.inverse
  Jfun : Systems.{max c v, v, max c v r} (J.over U) (openTower.{c, v, r} J U B) (openTowerMap.{c,
    v, r} J U B τ) ⥤ Systems.{c, v, max c v r} J B τ
  adjunction : Jfun ⊣ L
  additive : Jfun.Additive
  limits : PreservesFiniteLimits Jfun
  colimits : PreservesFiniteColimits Jfun
  restrictionAdditive : L.Additive
  restrictionLimits : PreservesFiniteLimits L
  restrictionColimits : PreservesFiniteColimits L
  level : ∀ n : ℕ, Jfun ⋙ evaluation.{c, v, max c v r} J B τ n ≅
    evaluation.{max c v, v, max c v r} (J.over U) (openTower.{c, v, r} J U B) (openTowerMap.{c,
    v, r} J U B τ) n ⋙
      SheafOfModules.localizedSystemExtension.{c, v, r} (B n) U

  coefficientRestriction : ∀ {m n : ℕ} (h : n ≤ m),
    res (coefficientMap.{max c v, v, max c v r} (J.over U)
        (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) h) ≅
      res ((J.overPullback CommRingCat.{max c v r} U).map
        (coefficientMap.{c, v, max c v r} J B τ h))
  coefficientRestriction_section : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Mod.{max c v, v, max c v r} (J.over U) ((B n).over U))
    (X : (Over U)ᵒᵖ),
    HEq (fun x ↦ ((coefficientRestriction h).hom.app M).val.app X x)
      (fun x : M.val.obj X ↦ x)
  restrictionLevel : ∀ n : ℕ, L ⋙
      evaluation.{max c v, v, max c v r} (J.over U)
        (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n ≅
    evaluation.{c, v, max c v r} J B τ n ⋙
      SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U
  unit_level : ∀ (n : ℕ)
    (M : Systems.{max c v, v, max c v r} (J.over U)
      (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ)),
    (evaluation.{max c v, v, max c v r} (J.over U)
        (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n).map
          (adjunction.unit.app M) ≫
      (restrictionLevel n).hom.app (Jfun.obj M) ≫
      (SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U).map
        ((level n).hom.app M) =
    (SheafOfModules.localizedSystemAdjunction.{c, v, r} (B n) U).unit.app
      ((evaluation.{max c v, v, max c v r} (J.over U)
        (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n).obj M)
  counit_level : ∀ (n : ℕ) (N : Systems.{c, v, max c v r} J B τ),
    (SheafOfModules.localizedSystemExtension.{c, v, r} (B n) U).map
        ((restrictionLevel n).hom.app N) ≫
      (SheafOfModules.localizedSystemAdjunction.{c, v, r} (B n) U).counit.app
        ((evaluation.{c, v, max c v r} J B τ n).obj N) =
    (level n).inv.app (L.obj N) ≫
      (evaluation.{c, v, max c v r} J B τ n).map (adjunction.counit.app N)

attribute [instance] SequenceOpenOrdinary.additive SequenceOpenOrdinary.limits
  SequenceOpenOrdinary.colimits SequenceOpenOrdinary.restrictionAdditive
  SequenceOpenOrdinary.restrictionLimits SequenceOpenOrdinary.restrictionColimits

/-- The actual restriction-form transition, after the level comparisons.
Heterogeneous equality identifies only the identical underlying additive section groups
of the two composite scalar restrictions; no transition map is forgotten.
Source: Stacks 03DI and 03CY (blueprint: lem-pur-sequence-site-open-extension). -/
def SequenceOpenOrdinary.Transitions
    (O : SequenceOpenOrdinary.{c, v, r} J U B τ) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
    (M : Systems.{max c v, v, max c v r} (J.over U)
      (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ)),
    (WeilConjectures.SemilinearSections.transition.{c, v, max c v r}
        J B τ h).app (O.Jfun.obj M) ≫
      (res (coefficientMap.{c, v, max c v r} J B τ h)).map ((O.level n).hom.app M) =
    (O.level m).hom.app M ≫
      (SheafOfModules.localizedSystemExtension.{c, v, r} (B m) U).map
        ((WeilConjectures.SemilinearSections.transition.{max c v, v, max c v r}
          (J.over U) (openTower.{c, v, r} J U B)
            (openTowerMap.{c, v, r} J U B τ) h).app M) ≫
      (SheafOfModules.localizedSystemExtension.{c, v, r} (B m) U).map
        ((O.coefficientRestriction h).hom.app
          ((evaluation.{max c v, v, max c v r} (J.over U)
            (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n).obj M)) ≫
      (O.coefficients.comparison (coefficientMap.{c, v, max c v r} J B τ h)).hom.app
        ((evaluation.{max c v, v, max c v r} (J.over U)
          (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n).obj M)

/-- Preservation of the actual endomorphisms specified by compatible scalar sections.
The natural ring maps are precisely compatible maps from R to the global sections;
writing their restrictions makes the scalar action at every test object explicit.
Source: Stacks 03DI and 03CY (blueprint: lem-pur-sequence-site-open-extension). -/
def SequenceOpenOrdinary.Scalars
    (O : SequenceOpenOrdinary.{c, v, r} J U B τ) : Prop :=
  ∀ (R : Type s) [CommRing R]
    (a : ∀ (n : ℕ) (X : Cᵒᵖ), R →+* (B n).obj.obj X)
    (_ha : ∀ (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (t : R),
      (B n).obj.map f (a n X t) = a n Y t)
    (_hτ : ∀ {m n : ℕ} (h : n ≤ m) (X : Cᵒᵖ) (t : R),
      (coefficientMap.{c, v, max c v r} J B τ h).hom.app X (a m X t) = a n X t)
    (t : R) (M : Systems.{max c v, v, max c v r} (J.over U)
      (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ)),
    ∃ (f : M ⟶ M) (g : O.Jfun.obj M ⟶ O.Jfun.obj M),
      (∀ (X : (ℕ × Over U)ᵒᵖ) (x : M.val.obj X),
        f.val.app X x = a X.unop.1 (op X.unop.2.left) t • x) ∧
      (∀ (X : (ℕ × C)ᵒᵖ) (x : (O.Jfun.obj M).val.obj X),
        g.val.app X x = a X.unop.1 (op X.unop.2) t • x) ∧
      O.Jfun.map f = g

/-- The derived level comparison is the termwise localization of the ordinary one.
It is a natural isomorphism on the ordinary unbounded derived system categories.
Source: Stacks 05RU, 03DI and 03DJ
(blueprint: lem-pur-sequence-site-open-extension). -/
def SequenceOpenOrdinary.derivedLevel
    (O : SequenceOpenOrdinary.{c, v, r} J U B τ) (n : ℕ) :=
  letI := SheafOfModules.localizedSystemExtensionAdditive.{c, v, r} (B n) U
  letI := SheafOfModules.localizedSystemExtensionLimits.{c, v, r} (B n) U
  letI := SheafOfModules.localizedSystemExtensionColimits.{c, v, r} (B n) U
  letI := HasDerivedCategory.standard
    (SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J (B n)).over U))
  (Functor.mapDerivedCategoryCompIso O.Jfun
    (evaluation.{c, v, max c v r} J B τ n)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (O.level n) ≪≫
  Functor.mapDerivedCategoryCompIso
    (evaluation.{max c v, v, max c v r} (J.over U)
      (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n)
    (SheafOfModules.localizedSystemExtension.{c, v, r} (B n) U)

/-- The coefficient comparison on unbounded derived categories is the localization
of its prescribed ordinary comparison, including its action on derived morphisms.
Source: Stacks 05RU and 03CY (blueprint: lem-pur-sequence-site-open-extension). -/
def SequenceOpenCoefficientData.derivedComparison
    (A : SequenceOpenCoefficientData.{c, v, r} J U)
    {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) :=
  letI := SheafOfModules.localizedSystemExtensionAdditive.{c, v, r} R U
  letI := SheafOfModules.localizedSystemExtensionLimits.{c, v, r} R U
  letI := SheafOfModules.localizedSystemExtensionColimits.{c, v, r} R U
  letI := SheafOfModules.localizedSystemExtensionAdditive.{c, v, r} S U
  letI := SheafOfModules.localizedSystemExtensionLimits.{c, v, r} S U
  letI := SheafOfModules.localizedSystemExtensionColimits.{c, v, r} S U
  letI := HasDerivedCategory.standard
    (SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J R).over U))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J S).over U))
  (Functor.mapDerivedCategoryCompIso
    (res ((J.overPullback CommRingCat.{max c v r} U).map φ))
    (SheafOfModules.localizedSystemExtension.{c, v, r} R U)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (A.comparison φ) ≪≫
  Functor.mapDerivedCategoryCompIso
    (SheafOfModules.localizedSystemExtension.{c, v, r} S U) (res φ)

/-- Compatibility of the localized comparisons with the actual derived transitions.
These are natural-transformation equations on the derived category of systems itself.
Source: Stacks 05RU, 03DI and localization at quasi-isomorphisms
(blueprint: lem-pur-sequence-site-open-extension). -/
def SequenceOpenOrdinary.DerivedTransitions
    (O : SequenceOpenOrdinary.{c, v, r} J U B τ) : Prop :=
  letI (n : ℕ) := SheafOfModules.localizedSystemExtensionAdditive.{c, v, r} (B n) U
  letI (n : ℕ) := SheafOfModules.localizedSystemExtensionLimits.{c, v, r} (B n) U
  letI (n : ℕ) := SheafOfModules.localizedSystemExtensionColimits.{c, v, r} (B n) U
  letI (n : ℕ) := HasDerivedCategory.standard
    (SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J (B n)).over U))
  ∀ {m n : ℕ} (h : n ≤ m)
    (M : DS.{max c v, v, max c v r} (J.over U)
      (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ)),
    (derivedTransition.{c, v, max c v r} J B τ h).app
        (O.Jfun.mapDerivedCategory.obj M) ≫
      (resD (coefficientMap.{c, v, max c v r} J B τ h)).map
        ((SequenceOpenOrdinary.derivedLevel.{c, v, r} J U B τ O n).hom.app M) =
    (SequenceOpenOrdinary.derivedLevel.{c, v, r} J U B τ O m).hom.app M ≫
      (SheafOfModules.localizedSystemExtension.{c, v, r} (B m) U).mapDerivedCategory.map
        ((derivedTransition.{max c v, v, max c v r} (J.over U)
          (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) h).app M) ≫
      (SheafOfModules.localizedSystemExtension.{c, v, r} (B m) U).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso (O.coefficientRestriction h)).hom.app
          ((e.{max c v, v, max c v r} (J.over U)
            (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n).obj M)) ≫
      (SequenceOpenCoefficientData.derivedComparison.{c, v, r} J U O.coefficients
        (coefficientMap.{c, v, max c v r} J B τ h)).hom.app
        ((e.{max c v, v, max c v r} (J.over U)
          (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ) n).obj M)

/-- The ordinary unbounded derived adjunction has exactly the localized termwise
unit and counit. These equations specify the adjunction on all derived morphisms.
Source: Stacks 05RU, 03DI and localization of natural transformations
(blueprint: lem-pur-sequence-site-open-extension). -/
structure SequenceOpenDerivedAdjunction
    (O : SequenceOpenOrdinary.{c, v, r} J U B τ) where
  adjunction : O.Jfun.mapDerivedCategory ⊣ O.L.mapDerivedCategory
  unit : ∀ K : CochainComplex
    (Systems.{max c v, v, max c v r} (J.over U)
      (openTower.{c, v, r} J U B) (openTowerMap.{c, v, r} J U B τ)) ℤ,
    adjunction.unit.app (DerivedCategory.Q.obj K) ≫
      O.L.mapDerivedCategory.map (O.Jfun.mapDerivedCategoryFactors.hom.app K) ≫
      O.L.mapDerivedCategoryFactors.hom.app
        ((O.Jfun.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((O.adjunction.mapHomologicalComplex (.up ℤ)).unit.app K)
  counit : ∀ K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ,
    O.Jfun.mapDerivedCategory.map (O.L.mapDerivedCategoryFactors.inv.app K) ≫
      adjunction.counit.app (DerivedCategory.Q.obj K) =
    O.Jfun.mapDerivedCategoryFactors.hom.app
        ((O.L.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((O.adjunction.mapHomologicalComplex (.up ℤ)).counit.app K)

/-- Geometric and levelwise open extension on the ringed sequence site.
Source: Stacks 03DI, 03DJ, 03CY, 04GZ and 0791
(blueprint: lem-pur-sequence-site-open-extension).

Proof: identify the element site of the constant open subterminal with the product
of the localized base site and the index poset; covers are precisely vertical covers.
Its restricted ring is B_n on every object, giving the geometric localization and L.
Apply the ringed-sheaf slice adjunction, transporting chosen small presentations.
For every coefficient map the two extension presheaves have identical additive sums
and the same restricted action. Sheafification therefore gives the normalized comparison.
Identity and composition hold on every summand; the transpose formula gives the unit
and counit equations. Define the system transition by extension of the old transition
followed by this coefficient comparison. Naturality and composition give the strict
system laws. Transposing levelwise morphisms gives exactly the system morphism squares,
so the resulting J is left adjoint to L. Uniqueness of left adjoints identifies it,
with units and counits, with geometric extension; it is consequently additive and exact.
Finally localize these exact functors and all their comparisons termwise. The universal
property of localization preserves their equations and naturality on every derived
morphism. On each summand, a compatible scalar acts by its actual restricted section;
sheafification and then localization preserve this endomorphism. -/
theorem sequenceSiteOpenExtension (W : Scheme.{u}) (V : W.ProEt)
    [IsOpenImmersion V.hom]
    (B : ℕ → Sheaf (Scheme.ProEt.topology W) CommRingCat.{max (u + 1) r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) :
    ∃ O : SequenceOpenOrdinary.{u + 1, u, r} (Scheme.ProEt.topology W) V B τ,
      O.Transitions ∧ O.Scalars.{u + 1, u, r, s} ∧ O.DerivedTransitions ∧
        Nonempty (SequenceOpenDerivedAdjunction.{u + 1, u, r}
          (Scheme.ProEt.topology W) V B τ O) := by
  sorry

end WeilConjectures.SemilinearSections
