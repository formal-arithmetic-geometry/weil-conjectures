/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Derived direct images for subterminal slices

Source: Stacks Project, Tags 03CE, 08DG, 08FI and 09T5
(blueprint: lem-sp-subterminal-derived-image-calculus).

The auxiliary records package chosen derived functors with their localization comparisons.
Every functor on module sheaves is the existing Mathlib functor, including its scalar map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u r w a b va vb wa wb

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SubterminalImageCalculus

/-- Abelian sheafification on a small site in any coefficient universe containing it.
Source: Stacks 03CV (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance smallSheafify {C : Type a} [Category.{va} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{r} :=
  hasSheafifyEssentiallySmallSite J AddCommGrpCat.{r}

/-- The sheafification criterion transported from a small model.
Source: Stacks 03CV (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance smallLocalCriterion {C : Type a} [Category.{va} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  letI : ∀ X : Cᵒᵖ,
      HasLimitsOfShape
        (StructuredArrow X (equivSmallModel.{r} C).inverse.op) AddCommGrpCat.{r} :=
    fun _ ↦ HasLimitsOfShape.of_small.{r, r} AddCommGrpCat.{r} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
    (A := AddCommGrpCat.{r})

/-- Pushforward acts additively componentwise. Source: Stacks 03CE, module specialization
(blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance pushforwardAdditive
    {C : Type a} [Category.{va} C] {D : Type b} [Category.{vb} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    (SheafOfModules.pushforward.{w} φ).Additive where
  map_add := rfl

/-- Restriction is the additive pushforward along the forgetful functor.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance overAdditive {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (Z : C) :
    (SheafOfModules.overFunctor.{w} R Z).Additive := pushforwardAdditive (𝟙 _)

/-- Relocalization is additive on sectionwise maps.
Source: Stacks 03DH (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance overMapAdditive {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {X Y : C} (f : X ⟶ Y) :
    (SheafOfModules.overMap.{w} R f).Additive :=
  pushforwardAdditive (Sheaf.pushforwardOverMapIso R f).inv

/-- Slice direct image is additive on sectionwise maps.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
instance overPullbackAdditive {C : Type u} [SmallCategory C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {X Y : C} (f : X ⟶ Y) :
    (SheafOfModules.overPullback.{w} R f).Additive :=
  pushforwardAdditive (Sheaf.toPushforwardOverPullback R f)

/-- A chosen derived restriction/direct-image adjunction, normalized on complexes.
Source: Stacks 08FI, 070I, 070K and 09T5
(blueprint: lem-sp-subterminal-derived-image-calculus).
The two preservation fields and two resolution fields are assertions, not assumptions
on the site. The comparison `qG` computes direct image on K-injective complexes.
The last field fixes the derived adjunction to the ordinary chain-map transpose. -/
structure DerivedPair
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (ordinary : F ⊣ G) where
  left : DerivedCategory A ⥤ DerivedCategory B
  right : DerivedCategory B ⥤ DerivedCategory A
  adj : left ⊣ right
  qF : DerivedCategory.Q ⋙ left ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  qG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ right
  qG_iso : ∀ (I : CochainComplex B ℤ), I.IsKInjective → IsIso (qG.app I)
  restrict_injective : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
    CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I)
  direct_injective : ∀ (I : CochainComplex B ℤ), I.IsKInjective →
    CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I)
  resolutions_source : ∀ (M : CochainComplex A ℤ),
    ∃ (I : CochainComplex A ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective
  resolutions_target : ∀ (M : CochainComplex B ℤ),
    ∃ (I : CochainComplex B ℤ) (i : M ⟶ I), QuasiIso i ∧ I.IsKInjective
  transpose : ∀ (M : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I), I.IsKInjective →
    adj.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
        (qF.hom.app M ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((ordinary.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
        qG.app I

/-- The actual sectionwise right adjoint, evaluating at `Z × C → Z` (the product order
used by Mathlib's `Over.star`). The scalar map is restriction along the other projection.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev direct {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{max u r}) (Z : C) :=
  SheafOfModules.pushforward.{max u r} (SheafOfModules.pushforwardOver (R := R) Z)

/-- The overlap map is the transpose of the restricted counit.
Source: Stacks 08DG (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def overlap {A : Type a} [Category.{va} A]
    {B : Type b} [Category.{vb} B] {D : Type w} [Category.{r} D]
    {f : A ⥤ B} {g : B ⥤ A} {h : A ⥤ D} {k : D ⥤ A} {t : B ⥤ D}
    (adj : f ⊣ g) (adjW : h ⊣ k) (comp : h ≅ f ⋙ t) (X : B) :
    g.obj X ⟶ k.obj (t.obj X) :=
  adjW.homEquiv _ _ (comp.hom.app (g.obj X) ≫ t.map (adj.counit.app X))

/-- The forgetful change from commutative ring sheaves to ring sheaves.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev ring {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) : Sheaf J RingCat.{max u r} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

/-- The recorded module category, with coefficient and site universes both retained.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) := ringedSiteModules.{max u r} (ring R)

/-- The recorded module category on the localized ringed site.
Source: Stacks 03CE (blueprint: lem-sp-subterminal-derived-image-calculus). -/
abbrev sliceModules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u r}) (Z : C) :=
  ringedSiteModules.{max u r} ((ring R).over Z)

/-- The sectionwise identity for iterated restriction, on complexes.
Source: Stacks 03DH (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def restrictionComp {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max u r})
    {X Y : C} (f : X ⟶ Y) :=
  NatIso.mapHomologicalComplex
    (SheafOfModules.overFunctorMap.{max u r} (ring R) f).symm (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (SheafOfModules.overFunctor.{max u r} (ring R) Y ⋙
          SheafOfModules.overMap.{max u r} (ring R) f)) (.up ℤ)).symm

universe d vd wd

/-- Compatibility of iterated derived restriction with the termwise product comparison.
Source: Stacks 03DH and 08DG (blueprint: lem-sp-subterminal-derived-image-calculus). -/
def CompositionNormalization
    {A : Type a} [Category.{va} A] [Abelian A]
    {B : Type b} [Category.{vb} B] [Abelian B]
    {D : Type d} [Category.{vd} D] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B] [HasDerivedCategory.{wd} D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    {f : DerivedCategory A ⥤ DerivedCategory B}
    {g : DerivedCategory B ⥤ DerivedCategory D}
    {h : DerivedCategory A ⥤ DerivedCategory D}
    (qF : DerivedCategory.Q ⋙ f ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qG : DerivedCategory.Q ⋙ g ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qH : DerivedCategory.Q ⋙ h ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : h ≅ f ⋙ g)
    (t : H.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ M : CochainComplex A ℤ,
    c.hom.app (DerivedCategory.Q.obj M) ≫ g.map (qF.hom.app M) ≫
      qG.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
        qH.hom.app M ≫ DerivedCategory.Q.map (t.hom.app M)

universe q0 qU qV qW v0 vU vV vW

/-- The natural comparison isomorphisms and their canonical mate equations.
Source: Stacks 08DG and 03CE (blueprint: lem-sp-subterminal-derived-image-calculus).
This auxiliary record lists exactly the comparison and overlap assertions of the node.
The six final laws are the two unit identities, two cross identities and two W identities. -/
structure Comparisons
    {D0 : Type q0} [Category.{v0} D0] {DU : Type qU} [Category.{vU} DU]
    {DV : Type qV} [Category.{vV} DV] {DW : Type qW} [Category.{vW} DW]
    {rU : D0 ⥤ DU} {rV : D0 ⥤ DV} {rW : D0 ⥤ DW}
    {kU : DU ⥤ DW} {kV : DV ⥤ DW}
    {RU : DU ⥤ D0} {RV : DV ⥤ D0} {RW : DW ⥤ D0}
    {KU : DW ⥤ DU} {KV : DW ⥤ DV}
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (adjKU : kU ⊣ KU) (adjKV : kV ⊣ KV)
    (cU : rW ≅ rU ⋙ kU) (cV : rW ≅ rV ⋙ kV) where
  eU : RU ⋙ rU ≅ 𝟭 _
  eV : RV ⋙ rV ≅ 𝟭 _
  eW : RW ⋙ rW ≅ 𝟭 _
  eUV : RV ⋙ rU ≅ kV ⋙ KU
  eVU : RU ⋙ rV ≅ kU ⋙ KV
  eUW : RW ⋙ rU ≅ KU
  eVW : RW ⋙ rV ≅ KV
  dU : KU ⋙ RU ≅ RW
  dV : KV ⋙ RV ≅ RW
  selfU : eU.hom = adjU.counit
  selfV : eV.hom = adjV.counit
  selfW : eW.hom = adjW.counit
  crossUV : ∀ B, eUV.hom.app B = adjKU.unit.app (rU.obj (RV.obj B)) ≫
      KU.map (cU.inv.app (RV.obj B) ≫
        cV.hom.app (RV.obj B) ≫ kV.map (adjV.counit.app B))
  crossVU : ∀ B, eVU.hom.app B = adjKV.unit.app (rV.obj (RU.obj B)) ≫
      KV.map (cV.inv.app (RU.obj B) ≫
        cU.hom.app (RU.obj B) ≫ kU.map (adjU.counit.app B))
  toUW : ∀ D, eUW.hom.app D = adjKU.unit.app (rU.obj (RW.obj D)) ≫
      KU.map (cU.inv.app (RW.obj D) ≫ adjW.counit.app D)
  compositeU : ∀ D, dU.hom.app D = adjW.homEquiv _ _
      (cU.hom.app (RU.obj (KU.obj D)) ≫
        kU.map (adjU.counit.app (KU.obj D)) ≫ adjKU.counit.app D)
  toVW : ∀ D, eVW.hom.app D = adjKV.unit.app (rV.obj (RW.obj D)) ≫
      KV.map (cV.inv.app (RW.obj D) ≫ adjW.counit.app D)
  compositeV : ∀ D, dV.hom.app D = adjW.homEquiv _ _
      (cV.hom.app (RV.obj (KV.obj D)) ≫
        kV.map (adjV.counit.app (KV.obj D)) ≫ adjKV.counit.app D)
  overlapUnitU : ∀ A, rU.map (overlap adjU adjW cU A) ≫
      eUW.hom.app (kU.obj A) = eU.hom.app A ≫ adjKU.unit.app A
  overlapCrossU : ∀ B, rU.map (overlap adjV adjW cV B) ≫
      eUW.hom.app (kV.obj B) = eUV.hom.app B
  overlapWU : ∀ A, rW.map (overlap adjU adjW cU A) ≫
      eW.hom.app (kU.obj A) = cU.hom.app (RU.obj A) ≫ kU.map (eU.hom.app A)
  overlapUnitV : ∀ A, rV.map (overlap adjV adjW cV A) ≫
      eVW.hom.app (kV.obj A) = eV.hom.app A ≫ adjKV.unit.app A
  overlapCrossV : ∀ B, rV.map (overlap adjU adjW cU B) ≫
      eVW.hom.app (kU.obj B) = eVU.hom.app B
  overlapWV : ∀ A, rW.map (overlap adjV adjW cV A) ≫
      eW.hom.app (kV.obj A) = cV.hom.app (RV.obj A) ≫ kV.map (eV.hom.app A)

universe w0 wU wV wW

set_option maxHeartbeats 500000 in
-- Simultaneous elaboration of five adjunctions and their localization comparisons.
/-- Subterminal derived direct-image calculus, with comparisons normalized on representatives.
Source: Stacks 03CE, 08DG, 08FI and 09T5
(blueprint: lem-sp-subterminal-derived-image-calculus).

Proof:
1. Apply lem-trf-slice-subtopos-site-presentation to the underlying sheaf of F.
Give F(Z × C → Z) its addition and the scalar action via R(C) → R(Z × C).
The transpose restricts M(C) to M(Z × C), then applies the given map.
Its inverse restricts along the graph. Naturality and the graph/projection
identities give inverse linear operations. This is the ordinary module adjunction
used below; the same construction in each slice gives both k adjunctions.
2. All four sites are small. Apply prop-pur-kinjective-resolutions-exist to their
restricted rings. Exact extension by zero is left adjoint to restriction by
lem-pur-site-restriction-module-adjunction-exact. Apply
lem-weil-pbc-right-adjoint-preserves-kinjective to that adjunction and then to
restriction/direct image. Thus both functors preserve K-injectives in all pairs.
3. Exact restriction descends termwise by lem-weil-pbc-exact-functor-derived-factorization.
Apply lem-weil-pbc-kinjective-total-derived to additive termwise direct image
followed by Q on homotopy categories. Its cone and shift matrices are unchanged,
so it is triangulated and is computed on K-injectives without another resolution.
4. Combine lem-weil-pbc-kinjective-hom-derived on both sides of the ordinary
adjunction lem-weil-pbc-termwise-adjunction-homotopy. This gives the derived
adjunction with exactly the chain-transpose equation in DerivedPair.
It fixes counits, and units on K-injective source complexes since restriction
preserves K-injectives. Homotopy classes represent all maps between these models.
5. If T → U, subterminality identifies the graph T → U × T with the inverse
projection. Also T ×_U (U × V) ≅ T × V and T × W ≅ T ×_U W. These product
identifications respect scalar restriction and restriction arrows. Interchange U,V.
6. At C the composite direct image evaluates on (C × U) ×_U W ≅ C × W.
This gives the two composition comparisons. Iterated restriction is sectionwise
the identity, exactly overFunctorMap and its termwise comparison.
7. Apply steps 5 and 6 degreewise to K-injective representatives. Step 2 ensures
all intervening complexes remain K-injective. By lem-weil-pbc-kinjective-hom-derived
these natural chain comparisons descend naturally. Their adjunction-mate equations
below identify precisely those product comparisons. The self comparisons are counits.
8. The overlap transpose is represented at C by restriction
I(C × U/U) → I(C × W/U). Its W-transpose is the U graph counit restricted to W.
Both complexes are K-injective, so lem-weil-pbc-kinjective-hom-derived identifies
this calculation with overlap; the same calculation applies to V.
9. At T → U the first overlap is the k_U unit and the other overlap is the
identity on the common product. Interchange U,V. At T → W both overlap maps
are identities under graph counits. These give the six final equations.
No covering hypothesis is used at any step. -/
theorem subterminal_derived_image_calculus
    {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    (J : GrothendieckTopology C) [J.Subcanonical]
    (R : Sheaf J CommRingCat.{max u r}) (U V : C)
    (hU : IsSubterminal U) (hV : IsSubterminal V)
    [HasDerivedCategory.{w0} (modules R)]
    [HasDerivedCategory.{wU} (sliceModules R U)]
    [HasDerivedCategory.{wV} (sliceModules R V)]
    [HasDerivedCategory.{wW} (sliceModules R (U ⨯ V))] :
    ∃ (pU : DerivedPair (SheafOfModules.overFunctor.{max u r} (ring R) U)
        (direct (ring R) U) (SheafOfModules.overPushforwardOverAdj (R := ring R) U))
      (pV : DerivedPair (SheafOfModules.overFunctor.{max u r} (ring R) V)
        (direct (ring R) V) (SheafOfModules.overPushforwardOverAdj (R := ring R) V))
      (pW : DerivedPair (SheafOfModules.overFunctor.{max u r} (ring R) (U ⨯ V))
        (direct (ring R) (U ⨯ V)) (SheafOfModules.overPushforwardOverAdj (R := ring R) (U ⨯ V)))
      (pKU : DerivedPair (SheafOfModules.overMap.{max u r} (ring R) (Limits.prod.fst : U ⨯ V ⟶ U))
        (SheafOfModules.overPullback.{max u r} (ring R) (Limits.prod.fst : U ⨯ V ⟶ U))
        (SheafOfModules.overMapPushforwardAdj (ring R) (Limits.prod.fst : U ⨯ V ⟶ U)))
      (pKV : DerivedPair (SheafOfModules.overMap.{max u r} (ring R) (Limits.prod.snd : U ⨯ V ⟶ V))
        (SheafOfModules.overPullback.{max u r} (ring R) (Limits.prod.snd : U ⨯ V ⟶ V))
        (SheafOfModules.overMapPushforwardAdj (ring R) (Limits.prod.snd : U ⨯ V ⟶ V)))
      (cU : pW.left ≅ pU.left ⋙ pKU.left)
      (cV : pW.left ≅ pV.left ⋙ pKV.left),
      CompositionNormalization (A := modules R) (B := sliceModules R U)
        (D := sliceModules R (U ⨯ V)) pU.qF pKU.qF pW.qF cU
        (restrictionComp R (Limits.prod.fst : U ⨯ V ⟶ U)) ∧
      CompositionNormalization (A := modules R) (B := sliceModules R V)
        (D := sliceModules R (U ⨯ V)) pV.qF pKV.qF pW.qF cV
        (restrictionComp R (Limits.prod.snd : U ⨯ V ⟶ V)) ∧
      Nonempty (Comparisons pU.adj pV.adj pW.adj pKU.adj pKV.adj cU cV) := by
  sorry

end CategoryTheory.SubterminalImageCalculus
