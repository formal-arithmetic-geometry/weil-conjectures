/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSectionLocalizationRing
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore
import Sheaf.CategoryTheory.ScalarLocalizationTelescopeLaws
import Sheaf.CategoryTheory.ScalarLocalizationUnitShift
import Sheaf.CategoryTheory.ScalarLocalizationUnitFactors

/-!
# The underlying telescope for scalar localization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2), with the telescope
model expanded using Stacks Project, Derived Categories, Lemma 0949 and Lemma 093W
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

universe u v w uD vD uT vT

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DirectSum
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The nth scalar-localization leg, for a specified adjunction and scalar action.
The theorem below supplies the canonical derived action and the normalized unit.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeLeg
    (A : Type v) [CommRing A] (t : A)
    {D : Type uD} [Category.{vD} D]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [Linear (Localization.Away t) T]
    (F : D ⥤ T) (U : T ⥤ D) (adj : F ⊣ U) (L : D) (n : ℕ) : L ⟶ U.obj (F.obj L) :=
  adj.unit.app L ≫ U.map
    (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) • 𝟙 (F.obj L))

/-- The derived unit is the class of the specified termwise unit on every complex,
after the canonical exact-functor factorization isomorphisms.
Source: Stacks Project, Derived Categories, Tags 05RU and 015F
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeDerivedUnit
    {B : Type uD} [Category.{vD} B] [Abelian B] [HasDerivedCategory.{w} B]
    {B' : Type uT} [Category.{vT} B'] [Abelian B'] [HasDerivedCategory.{w} B']
    (E : B ⥤ B') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : B' ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (unitComplex : ∀ (K : CochainComplex B ℤ),
      K ⟶ (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (adj : E.mapDerivedCategory ⊣ U.mapDerivedCategory) : Prop :=
  ∀ (K : CochainComplex B ℤ),
    adj.unit.app (DerivedCategory.Q.obj K) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Q.map (unitComplex K)

/-- The telescope triangle with all its specified legs, naturality and shift equations.
The predicate P records which source objects need the telescope comparison; the theorem
below substitutes the bounded-below predicate and the canonical derived scalar actions.
Source: Stacks Project, Derived Categories, Tags 093W, 0949 and 014A
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeProperty
    (A : Type v) [CommRing A] (t : A)
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ k : ℤ, (shiftFunctor D k).Additive] [Pretriangulated D] [Linear A D]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasShift T ℤ]
    [Linear (Localization.Away t) T]
    (F : D ⥤ T) [F.CommShift ℤ] (U : T ⥤ D) [U.CommShift ℤ]
    (adj : F ⊣ U) (P : D → Prop) : Prop :=
  ∀ (L : D), P L →
    ∃ (A₀ : D) (ι : ∀ _n : ℕ, L ⟶ A₀) (_hc : IsColimit (Cofan.mk A₀ ι))
      (s : A₀ ⟶ A₀) (_hs : ∀ n : ℕ, ι n ≫ s = (t • 𝟙 L) ≫ ι (n + 1))
      (H : D) (g : A₀ ⟶ H) (h : H ⟶ A₀⟦(1 : ℤ)⟧),
      (Triangle.mk (𝟙 A₀ - s) g h ∈ distTriang D ∧
        ∃ e : H ≅ U.obj (F.obj L),
          ∀ n : ℕ, ι n ≫ g ≫ e.hom = scalarLocalizationTelescopeLeg A t F U adj L n) ∧
      (∀ (K L : D) (f : K ⟶ L) (n : ℕ),
        f ≫ scalarLocalizationTelescopeLeg A t F U adj L n =
          scalarLocalizationTelescopeLeg A t F U adj K n ≫ U.map (F.map f)) ∧
      (∀ (L : D) (n : ℕ) (k : ℤ),
        scalarLocalizationTelescopeLeg A t F U adj (L⟦k⟧) n ≫
          ((F ⋙ U).commShiftIso k).hom.app L =
        (scalarLocalizationTelescopeLeg A t F U adj L n)⟦k⟧')

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem telescope_of_complexColimit
    (A : Type v) [CommRing A] (t : A)
    {B : Type uD} [Category.{vD} B] [Abelian B] [HasDerivedCategory.{w} B]
    {B' : Type uT} [Category.{vT} B'] [Abelian B'] [HasDerivedCategory.{w} B']
    [Linear A B] [Linear (Localization.Away t) B']
    [HasCountableCoproducts B] [HasFilteredColimitsOfSize.{0, 0} B] [AB5OfSize.{0, 0} B]
    (E : B ⥤ B') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U₀ : B' ⥤ B) [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    (unitComplex : ∀ K : CochainComplex B ℤ,
      K ⟶ (U₀.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K))
    (adj : E.mapDerivedCategory ⊣ U₀.mapDerivedCategory) [adj.CommShift ℤ]
    (derivedUnit : scalarLocalizationTelescopeDerivedUnit E U₀ unitComplex adj)
    (hcol : ∀ K : CochainComplex B ℤ,
      ∃ c : Cocone (Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K)),
        Nonempty (IsColimit c) ∧
        ∃ β : c.pt ≅ (U₀.mapHomologicalComplex (.up ℤ)).obj
            ((E.mapHomologicalComplex (.up ℤ)).obj K),
          ∀ n : ℕ, c.ι.app n ≫ β.hom = unitComplex K ≫
            (U₀.mapHomologicalComplex (.up ℤ)).map
              (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
                𝟙 ((E.mapHomologicalComplex (.up ℤ)).obj K)))
    (P : DerivedCategory B → Prop) :
    scalarLocalizationTelescopeProperty A t E.mapDerivedCategory U₀.mapDerivedCategory adj P := by
  classical
  obtain ⟨hnat, hshift⟩ :=
    scalarLocalizationTelescopeLegLaws A t E.mapDerivedCategory U₀.mapDerivedCategory adj
  intro L _hL
  let K : CochainComplex B ℤ := DerivedCategory.Q.objPreimage L
  let eK : DerivedCategory.Q.obj K ≅ L := DerivedCategory.Q.objObjPreimageIso L
  clear_value K eK
  obtain ⟨c, ⟨hc⟩, β, hβ⟩ :=
    hcol K
  let S := Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K)
  let b : Cofan (fun _n : ℕ ↦ K) :=
    HomologicalComplex.coconeOfHasColimitEval (Discrete.functor (fun _n : ℕ ↦ K))
  have hb : IsColimit b := HomologicalComplex.isColimitCoconeOfHasColimitEval _
  clear_value b
  let s : b.pt ⟶ b.pt := hb.desc (Cofan.mk b.pt
    (fun n : ℕ ↦ (t • 𝟙 K) ≫ b.inj (n + 1)))
  have hs (n : ℕ) : b.inj n ≫ s = (t • 𝟙 K) ≫ b.inj (n + 1) := hb.fac _ ⟨n⟩
  let q : b.pt ⟶ c.pt := hb.desc (Cofan.mk c.pt (fun n : ℕ ↦ c.ι.app n))
  have hq (n : ℕ) : b.inj n ≫ q = c.ι.app n := hb.fac _ ⟨n⟩
  clear_value s q
  have hu (n : ℕ) : b.inj n ≫ (𝟙 b.pt - s) =
      b.inj n - (t • 𝟙 K) ≫ b.inj (n + 1) := by
    simp only [Preadditive.comp_sub, Category.comp_id, hs]
  obtain ⟨p, hp, hp', hqi, ⟨hQB⟩, e, he, htri, htri', hrest⟩ :=
    complex_colimit_homotopyColimit S b hb c hc (𝟙 b.pt - s)
      (fun n ↦ by simpa only [S, Functor.ofSequence_map_homOfLE_succ] using hu n) q hq
  let δ : U₀.mapDerivedCategory.obj (E.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj
        ((U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    U₀.mapDerivedCategory.mapIso (E.mapDerivedCategoryFactors.app K) ≪≫
      U₀.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let eL : DerivedCategory.Q.obj c.pt ≅
      U₀.mapDerivedCategory.obj (E.mapDerivedCategory.obj L) :=
    DerivedCategory.Q.mapIso β ≪≫ δ.symm ≪≫
      (E.mapDerivedCategory ⋙ U₀.mapDerivedCategory).mapIso eK
  have hlegs (n : ℕ) : DerivedCategory.Q.map (c.ι.app n) ≫
      (DerivedCategory.Q.mapIso β ≪≫ δ.symm).hom =
      scalarLocalizationTelescopeLeg A t E.mapDerivedCategory U₀.mapDerivedCategory
        adj (DerivedCategory.Q.obj K) n := by
    apply (cancel_mono δ.hom).1
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Functor.mapIso_hom]
    rw [← Functor.map_comp, hβ, Functor.map_comp]
    have hh := scalarLocalization_unit_factors (Localization.Away t) E U₀ adj K
      (unitComplex K) (derivedUnit K) (IsLocalization.Away.invSelf t ^ n)
    simpa only [scalarLocalizationTelescopeLeg, Functor.map_comp, δ, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hh
  let ι : ∀ _n : ℕ, L ⟶ DerivedCategory.Q.obj b.pt :=
    fun n ↦ eK.inv ≫ DerivedCategory.Q.map (b.inj n)
  have hι : IsColimit (Cofan.mk (DerivedCategory.Q.obj b.pt) ι) := by
    let d : Discrete.functor (fun _n : ℕ ↦ DerivedCategory.Q.obj K) ≅
        Discrete.functor (fun _n : ℕ ↦ L) := Discrete.natIso (fun _n ↦ eK)
    exact (IsColimit.precomposeInvEquiv d _).symm hQB
  have hsQ (n : ℕ) : ι n ≫ DerivedCategory.Q.map s =
      (t • 𝟙 L) ≫ ι (n + 1) := by
    calc
      ι n ≫ DerivedCategory.Q.map s =
          eK.inv ≫ DerivedCategory.Q.map (b.inj n ≫ s) := by
        simp only [ι, Functor.map_comp, Category.assoc]
      _ = eK.inv ≫ DerivedCategory.Q.map ((t • 𝟙 K) ≫ b.inj (n + 1)) := by rw [hs]
      _ = (t • 𝟙 L) ≫ ι (n + 1) := by
        simp only [ι, Functor.map_smul, Linear.comp_smul, Linear.smul_comp,
          Category.id_comp]
  refine ⟨DerivedCategory.Q.obj b.pt, ι, hι, DerivedCategory.Q.map s, hsQ,
    DerivedCategory.Q.obj c.pt, DerivedCategory.Q.map q,
    e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      (𝟙 b.pt - s))).mor₃, ?_, hnat, hshift⟩
  constructor
  · simpa only [Functor.map_sub, Functor.map_id] using htri'
  · refine ⟨eL, ?_⟩
    intro n
    dsimp only [ι, eL, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, ← Functor.map_comp_assoc, hq]
    calc
      _ = eK.inv ≫ scalarLocalizationTelescopeLeg A t E.mapDerivedCategory
          U₀.mapDerivedCategory adj (DerivedCategory.Q.obj K) n ≫
            U₀.mapDerivedCategory.map (E.mapDerivedCategory.map eK.hom) := by
        simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Category.assoc]
          using congrArg (fun f ↦ eK.inv ≫ f ≫
            U₀.mapDerivedCategory.map (E.mapDerivedCategory.map eK.hom)) (hlegs n)
      _ = _ := by
        have hn := congrArg (fun f ↦ eK.inv ≫ f) (hnat _ _ eK.hom n)
        simpa only [scalarLocalizationTelescopeLeg, ← Category.assoc, eK.inv_hom_id,
          Category.id_comp] using hn.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- The tensor and derived coefficient structures require substantial elaboration.
/--
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2), and Stacks Project,
Derived Categories, Lemmas 0949 and 093W.
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope).

Proof: choose a complex representing L. The ordinary module fraction-colimit theorem,
assembled degreewise by scalarLocalization_complexColimit, identifies the sequential
colimit of its repeated-t diagram with restricted scalar extension. Grothendieck
exactness gives exact sequential colimits and countable coproducts. The general abelian
complex_colimit_homotopyColimit theorem then gives the actual mapped coprojections and
the distinguished triangle with second arrow induced by the colimit cocone.

The normalized derived-unit equation and scalarLocalization_unit_factors identify each
mapped colimit leg with the unit followed by the inverse power of t. Transport the
coproduct, successor map and legs along the chosen representative isomorphism to L.
The theorem asks for a telescope triangle, so this explicit cone supplies its witness.

Finally scalarLocalization_unit_commShift obtains shift coherence for the specified
normalized adjunction by sectionwise extensionality and descent through localization.
Apply scalarLocalizationTelescopeLegLaws to obtain naturality on every derived morphism
and the shift equation for every integer, and combine these with the constructed triangle.
-/
theorem scalarLocalization_underlyingTelescope
    (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (t : A)
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))]
    (E : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))
    (hE : ∀ M, E.obj M =
      SheafOfModules.changeOfRings (ringedLocalizationRingUnit R (a t)) M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHom (ringedLocalizationRingUnit R (a t)) M f ≫
        eqToHom (hE N).symm)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U₀ : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hU₀ : U₀ = SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnit R (a t))))
    [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    (unitComplex : ∀ (K : CochainComplex (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      K ⟶ (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (unitSections : ∀ (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (i : ℤ),
      scalarLocalizationTelescopeUnitSections (ringedLocalizationRingUnit R (a t))
        (K.X i) (E.obj (K.X i)) (hE (K.X i))
        ((unitComplex K).f i ≫
          eqToHom (congrArg (fun T ↦ T.obj (E.obj (K.X i))) hU₀)))
    (adj : E.mapDerivedCategory ⊣ U₀.mapDerivedCategory)
    (derivedUnit : scalarLocalizationTelescopeDerivedUnit E U₀ unitComplex adj) :
    (fun [_iA : Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))]
      [_iT : Linear (Localization.Away t) (DerivedCategory
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R (a t)))))] ↦
      scalarLocalizationTelescopeProperty A t E.mapDerivedCategory U₀.mapDerivedCategory adj
        (fun L ↦ ∃ b : ℤ, L.IsGE b))
      (_iA := scalarLocalizationDerivedLinear A R a)
      (_iT := scalarLocalizationDerivedLinear (Localization.Away t)
        (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)) := by
  classical
  let B := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let B' := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (ringedLocalizationRing R (a t)))
  let : Linear A B := scalarLocalizationCoefficientLinear A R a
  let : Linear (Localization.Away t) B' :=
    scalarLocalizationCoefficientLinear (Localization.Away t)
      (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)
  let : Linear A (DerivedCategory B) := scalarLocalizationDerivedLinear A R a
  let : Linear (Localization.Away t) (DerivedCategory B') :=
    scalarLocalizationDerivedLinear (Localization.Away t)
      (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)
  have : IsGrothendieckAbelian.{u} B :=
    (SheafOfModules.grothendieckAbelian_with_localized_generator J R).1
  have : HasFiniteBiproducts B := Abelian.hasFiniteBiproducts
  have : HasCoproducts.{0} B := hasCoproducts_of_finite_and_filtered
  have : HasCountableCoproducts B := hasCountableCoproducts_of_hasCoproducts B
  have : AB5OfSize.{0, 0} B := AB5OfSize_shrink B
  have : adj.CommShift ℤ := scalarLocalization_unit_commShift E U₀ adj unitComplex
    derivedUnit (by
    intro K k
    apply HomologicalComplex.hom_ext
    intro i
    simp only [Functor.commShiftIso_comp_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      CochainComplex.shiftFunctor_map_f']
    change (unitComplex (K⟦k⟧)).f i ≫ U₀.map (𝟙 (E.obj (K.X (i + k)))) ≫
      𝟙 (U₀.obj (E.obj (K.X (i + k)))) = (unitComplex K).f (i + k)
    simp only [Category.comp_id]
    have eU : U₀.obj (E.obj (K.X (i + k))) =
        (SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map
            (ringedLocalizationRingUnit R (a t)))).obj (E.obj (K.X (i + k))) :=
      congrArg (fun T ↦ T.obj (E.obj (K.X (i + k)))) hU₀
    erw [U₀.map_id]
    erw [Category.comp_id]
    let e := eqToIso eU ≪≫ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnit R (a t)))).mapIso (eqToIso (hE (K.X (i + k))))
    apply (Iso.cancel_iso_hom_right _ _ e).mp
    ext V x
    exact (unitSections (K⟦k⟧) i V x).trans (unitSections K (i + k) V x).symm
    )
  exact telescope_of_complexColimit A t E U₀ unitComplex adj derivedUnit
    (scalarLocalization_complexColimit A R a t E hE hmap U₀ hU₀ unitComplex unitSections)
    (fun L ↦ ∃ b : ℤ, L.IsGE b)

end CategoryTheory
