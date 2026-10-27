/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.CategoryTheory.RingedSiteModules

import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Module derived restriction on injective section complexes

Source: Stacks Project, `sites-cohomology.tex`, Tag 08J6 and `cohomology.tex`, Tags
01F8, 01F9 and 01FB (blueprint: lem-trf-module-derived-restriction-resolution).

## Main definitions and statement

* `moduleInjectiveComplex`: the existing category of module-sheaf complexes.
* `moduleInjectiveComplexPlus`: bounded-below complexes of injective objects.
* `moduleInjectiveComplexUnderlying`: forget the injective-object wrapper.
* `moduleDerivedRestrictionResolution`: restriction computed on injective section complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The identity composition comparison has identity components on representatives.
private lemma module_compUnit_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (X : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app X =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
  have hi := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app X
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  simp [Functor.rightDerivedFunctorCompUnit, hi]

-- Normalize the canonical composition isomorphism against the derived units.
private lemma module_leray_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (X : HomotopyCategory C (.up ℤ)) :
    G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) ≫
        (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) ≫
        H.rightDerivedFunctorUnit.app X := by
  have hc := Functor.rightDerivedNatTrans_app
    (F ⋙ G).rightDerivedFunctor (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 _) X
  change (F ⋙ G).rightDerivedFunctorUnit.app X ≫
    (F.rightDerivedFunctorCompIso G).hom.app (DerivedCategory.Qh.obj X) = _ at hc
  simp only [NatTrans.id_app, Category.id_comp] at hc
  rw [← Category.assoc, ← module_compUnit_app F G X, ← hc]
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact Functor.rightDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh) X

-- Compute the derived transpose before inverting the comparison units.
private lemma module_restriction_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) (R : D ⥤ C) (G : C ⥤ E) (H : D ⥤ E)
    [L.Additive] [R.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.PreservesKInjectiveComplexes]
    (adj : L ⊣ R) (e : R ⋙ G ≅ H)
    (M : HomotopyCategory C (.up ℤ)) :
    G.rightDerivedFunctorUnit.app M ≫
        G.rightDerivedFunctor.map
          (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj M)) ≫
        (Functor.rightDerivedFunctorCompIso' R G e).hom.app
          (L.mapDerivedCategory.obj (DerivedCategory.Qh.obj M)) ≫
        H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (.up ℤ)).map
            ((adj.mapHomotopyCategory (.up ℤ)).unit.app M) ≫
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
            ((L.mapHomotopyCategory (.up ℤ)).obj M)) ≫
        H.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj M) := by
  let T := (L.mapHomotopyCategory (.up ℤ)).obj M
  have hu := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit M
  have hn := (Functor.rightDerivedFunctorCompIso' R G e).hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app M)
  have hg := G.rightDerivedFunctorUnit.naturality
    ((adj.mapHomotopyCategory (.up ℤ)).unit.app M)
  have hc := module_leray_fac R G H e T
  dsimp only [Functor.comp_map] at hn hg
  erw [← hn]
  erw [← Functor.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hg, hc, ← DerivedCategory.Qh.map_comp_assoc]

-- Evaluate the generic identity on K-injective representatives before specializing sites.
private theorem module_chain
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) (R : D ⥤ C) (G : C ⥤ E) (H : D ⥤ E)
    [L.Additive] [R.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.PreservesKInjectiveComplexes]
    (adj : L ⊣ R) (e : R ⋙ G ≅ H)
    (I : CochainComplex C ℤ)
    (J : CochainComplex D ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (j : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    (G.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
              (Functor.whiskerRight adj.unit G ≫ Functor.whiskerLeft L e.hom) (.up ℤ)).app I ≫
            (H.mapHomologicalComplex (.up ℤ)).map j) ≫
      (H.rightDerivedFunctorObjQIso J).inv =
    G.rightDerivedFunctor.map
        (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
          (DerivedCategory.Q.obj I)) ≫
      (Functor.rightDerivedFunctorCompIso' R G e).hom.app
        (L.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
      H.rightDerivedFunctor.map
        (L.mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map j) := by
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let U := (L.mapHomotopyCategory (.up ℤ)).obj K
  let v := (G.mapHomologicalComplex (.up ℤ)).map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
      ((L.mapHomologicalComplex (.up ℤ)).obj I)
  have hfactor : L.mapDerivedCategoryFactorsh.hom.app K =
      L.mapDerivedCategoryFactors.hom.app I := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [Category.comp_id]
    repeat erw [Category.id_comp]
  have hquotient : DerivedCategory.Qh.map
      (((G.mapHomotopyCategory (.up ℤ)).map
          ((adj.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app U) ≫
        (H.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient _ (.up ℤ)).map j)) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerRight adj.unit G ≫ Functor.whiskerLeft L e.hom) (.up ℤ)).app I ≫
          (H.mapHomologicalComplex (.up ℤ)).map j) := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      (v ≫ (H.mapHomologicalComplex (.up ℤ)).map j)) = _
    rfl
  have hc := module_restriction_fac L R G H adj e K
  rw [hfactor] at hc
  have hj := H.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map j)
  dsimp only [Functor.comp_map] at hj
  have hc' := congrArg (fun t ↦ t ≫ H.rightDerivedFunctor.map (DerivedCategory.Q.map j)) hc
  simp only [Category.assoc] at hc'
  erw [← hj, ← DerivedCategory.Qh.map_comp_assoc] at hc'
  erw [hquotient] at hc'
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, asIso_hom, asIso_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  rw [← cancel_epi (G.rightDerivedFunctorUnit.app K)]
  erw [IsIso.hom_inv_id_assoc]
  simp only [Functor.map_comp] at hc' ⊢
  exact hc'.symm

end CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Underlying module-sheaf complex over a scheme.
Source: Stacks, sites-cohomology.tex, Tag 08J6
(blueprint: lem-trf-module-derived-restriction-resolution). -/
abbrev moduleInjectiveComplex (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ

/-- Bounded-below complexes whose terms are injective module sheaves.
Source: Stacks, derived.tex, Tag 070J
(blueprint: lem-trf-module-derived-restriction-resolution). -/
abbrev moduleInjectiveComplexPlus (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  CochainComplex.Plus (InjectiveObject
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- Forget the injective-object wrapper to the underlying complex.
Source: Stacks, derived.tex, Tag 070J
(blueprint: lem-trf-module-derived-restriction-resolution). -/
abbrev moduleInjectiveComplexUnderlying {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (I : moduleInjectiveComplexPlus T Λ) : moduleInjectiveComplex T Λ :=
  (((InjectiveObject.ι _).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj)

/--
For a morphism of schemes and a commutative coefficient ring, the restriction map on
unbounded derived module sections is represented by the degreewise module adjunction
unit followed by an arbitrary map from the pulled-back injective complex to an injective
complex.  The proof is the five-step K-injective, derived-adjunction and Leray
calculation from Stacks Tags 08J6, 01F8, 01F9, 01FB and 015M.
(blueprint: lem-trf-module-derived-restriction-resolution)

Proof (postponed in stage 2).

1. Work throughout in the constant-coefficient module categories, which have enough
injectives by lem-weil-pbc-module-sheaves-enough-injectives. Exact inverse image and
lem-sp-right-adjoint-preserves-injectives imply that direct image preserves injectives.
Thus I, J and u_*J are bounded-below injective complexes, hence K-injective by
lem-weil-pbc-dplus-injective-representative. The direct-image and sections comparison
units are natural and invertible on them by lem-weil-pbc-right-derived-plus-injective.
These are also the unbounded comparisons of def-kun-rgamma-unbounded: the same
K-injective models compute morphisms by lem-sf-kinjective-derived-map-computation,
using prop-weil-pbc-kinjective-resolutions-exist.

2. Put t = u_*a composed with the ordinary unit I to u_*u-inverse(I).
By lem-weil-pbc-termwise-adjunction-homotopy this is a module-linear chain map and the
homotopy-category transpose of a. By def-weil-pbc-direct-image, evaluation of u_*a at
T is evaluation of a at T'. Thus sections of t are exactly e_(u,I) followed by sections
of a, degree by degree; naturality of the unit gives compatibility with differentials.
The parameter w with hw expresses this exact chain map, rather than a chosen replacement.

3. By lem-weil-pbc-exact-functor-derived-factorization, exact inverse image commutes
with localization. Since J and u_*J are K-injective, the localization Hom bijections of
lem-weil-pbc-kinjective-hom-derived and the homotopy adjunction of
lem-weil-pbc-termwise-adjunction-homotopy send Q(a) to Q(t). Their naturality and the
unit formula of lem-weil-pbc-adjunction-of-natural-bijection identify the derived
transpose: Ru_*(Q(a)) composed with the derived unit equals delta_J composed with Q(t),
where delta_J is the direct-image resolution comparison. No inverse to a is used.

4. Normalize Leray on the same models. Choose an injective representative of any
bounded-below derived object by lem-weil-pbc-dplus-injective-representative. Its direct
image is again bounded-below injective, so the equality of module section complexes
Gamma(T,u_*J) = Gamma(T',J) computes Leray without a second replacement. Naturality and
independence follow by lifting derived maps to homotopy classes with
lem-weil-pbc-kinjective-hom-derived; direct image followed by sections gives literally
the same chain map as sections on T'. The uniqueness of
lem-weil-pbc-right-derived-plus-injective identifies this with the canonical 08J6/015M
comparison. Consequently Leray composed with Rsections(delta_J) and the sections
comparison for u_*J is the sections comparison for J.

5. The definition of restriction, naturality of Leray at Q(a), and step 3 rewrite the
left side of the node's equation as Leray followed after Rsections(delta_J) and
Rsections(Q(t)). Naturality of the sections comparison at t and step 4 reduce this to
alpha_J composed with Q(Gamma(T,t)) and alpha_I inverse. Step 2 identifies Gamma(T,t)
with w. In the displayed Lean equation, rightDerivedFunctorObjQIso.hom is alpha_I
inverse and rightDerivedFunctorObjQIso.inv is alpha_J. This proves exactly the claimed
formula, with no quasi-isomorphism assumption on a and no finiteness assumptions.
-/
theorem moduleDerivedRestrictionResolution
    {T T' : Scheme.{u}} (u : T' ⟶ T) (Λ : Type (u + 1)) [CommRing Λ]
    (I : moduleInjectiveComplexPlus T Λ) (J : moduleInjectiveComplexPlus T' Λ)
    (a : ((upperStar (ModuleCat.{u + 1} Λ) u).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (moduleInjectiveComplexUnderlying I) ⟶
      moduleInjectiveComplexUnderlying J)
    (w : ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (moduleInjectiveComplexUnderlying I) ⟶
      ((Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (moduleInjectiveComplexUnderlying J))
    (hw : ∀ i : ℤ, w.f i =
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) u
          ((moduleInjectiveComplexUnderlying I).X i) ≫
        (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map (a.f i)) :
    ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorObjQIso
        (moduleInjectiveComplexUnderlying I)).hom ≫
      DerivedCategory.Q.map w ≫
      ((Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorObjQIso
        (moduleInjectiveComplexUnderlying J)).inv =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u).unit.app
            (DerivedCategory.Q.obj (moduleInjectiveComplexUnderlying I))) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) u).hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) u).mapDerivedCategory.obj
              (DerivedCategory.Q.obj (moduleInjectiveComplexUnderlying I))) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T').map
          ((upperStar (ModuleCat.{u + 1} Λ) u).mapDerivedCategoryFactors.hom.app
              (moduleInjectiveComplexUnderlying I) ≫
            DerivedCategory.Q.map a) := by
  let L := upperStar (ModuleCat.{u + 1} Λ) u
  let R := lowerStar (ModuleCat.{u + 1} Λ) u
  let G := Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let H := Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u
  let e := lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) u
  let I₀ := moduleInjectiveComplexUnderlying I
  let v := (G.mapHomologicalComplex (.up ℤ)).map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app I₀) ≫
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
      ((L.mapHomologicalComplex (.up ℤ)).obj I₀) ≫
    (H.mapHomologicalComplex (.up ℤ)).map a
  have hw' : w = v := by
    ext i : 1
    change w.f i = G.map (adj.unit.app (I₀.X i)) ≫
      e.hom.app (L.obj (I₀.X i)) ≫ H.map (a.f i)
    have hs : G.map (adj.unit.app (I₀.X i)) ≫
        e.hom.app (L.obj (I₀.X i)) =
        globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) u (I₀.X i) := by
      dsimp only [G, e, lowerStarCompGlobalSectionsIso, Functor.isoWhiskerLeft_hom,
        Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
      erw [← Category.assoc, (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
        (ModuleCat.{u + 1} Λ) terminalIsTerminal).hom.naturality
          (adj.unit.app (I₀.X i))]
      rfl
    rw [← Category.assoc, hs, hw i]
  have hc := CategoryTheory.module_chain L R G H adj e
    (moduleInjectiveComplexUnderlying I) (moduleInjectiveComplexUnderlying J) a
  dsimp only [rightDerivedGlobalSections, mapDerivedUpperStarLowerStarAdjunction,
    rightDerivedLowerStarCompRightDerivedGlobalSectionsIso]
  rw [hw']
  exact hc

end AlgebraicGeometry.Etale
