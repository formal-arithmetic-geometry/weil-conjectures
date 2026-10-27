/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.CategoryTheory.Sites.BinaryPresentationModuleData
public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.CategoryTheory.SheafSubcategoryComparison
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.Sites.BinaryPresentationSlices
import Sheaf.CategoryTheory.Sites.BinaryPresentationSliceNerve
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.RingedToposRingSquare
import Sheaf.CategoryTheory.GeometricModuleConstruction
import Sheaf.CategoryTheory.RingedEquivalenceModuleHom
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Sheaf.CategoryTheory.SheafSubcategoryComparison
import Sheaf.CategoryTheory.SmallSetOfCoveringFamilies
import Sheaf.CategoryTheory.RingedToposEquivalenceRingTransport

/-!
# A simultaneous site presentation for a binary subterminal cover

Source: Stacks Project, Sites, Tags 03A1, 03CI, 00Y1, 04GZ and 03EH;
Modules on Sites, Tags 03CR, 03D7, 04IE and 04J4
(blueprint: lem-sp-binary-cover-site-presentation).

The four indices are `0 = 1`, `1 = U`, `2 = V`, `3 = U × V`.
Internal commutative rings are encoded by their section-ring sheaves, as in the recorded
sectionwise reconstruction theorem. The source slice modules are encoded on the existing
category-of-elements site; the target slices use the actual localized topology `J.over`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- All witnesses for one small finite-limit-closed presenting subcategory and the four
simultaneous ringed slices. Full faithfulness realizes the small category as a full
subcategory, with chosen representatives of its objects.
Source: Stacks Sites, Tags 03A1, 03CI and 00Y1; Modules on Sites, 03CR
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryCoverSitePresentation
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U V : Sheaf J (Type u)) where
  E : Type u
  [category : SmallCategory E]
  [finiteLimits : HasFiniteLimits E]
  inclusion : E ⥤ Sheaf J (Type u)
  [full : inclusion.Full]
  [faithful : inclusion.Faithful]
  [preservesLimits : PreservesFiniteLimits inclusion]
  generators : ∀ X : C, ∃ Y : E,
    Nonempty (inclusion.obj Y ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj X))
  objects : Fin 4 → E
  terminal : inclusion.obj (objects 0) ≅ ⊤_ (Sheaf J (Type u))
  first : inclusion.obj (objects 1) ≅ U
  second : inclusion.obj (objects 2) ≅ V
  intersection : inclusion.obj (objects 3) ≅ U ⨯ V
  covers : Precoverage E
  site : covers.IsSiteForCoverings
  [subcanonical : covers.toGrothendieck.Subcanonical]
  epimorphic : ∀ (X : E) (P : PreZeroHypercover.{u} X),
    P.presieve₀ ∈ covers X ↔
      ⟨X, P⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} inclusion
  representatives : Set (Σ X : E, PreZeroHypercover.{u} X)
  smallRepresentatives : Small.{u} representatives
  coveringClass : PreZeroHypercover.IsCoveringClass representatives
  representativeCovers : ∀ (X : E) (P : PreZeroHypercover.{u} X),
    ⟨X, P⟩ ∈ representatives → P.presieve₀ ∈ covers X
  sameSupports : ∀ (X : E) (P : PreZeroHypercover.{u} X), P.presieve₀ ∈ covers X →
    ∃ Q : PreZeroHypercover.{u} X, ⟨X, Q⟩ ∈ representatives ∧ P.presieve₀ = Q.presieve₀
  binaryCover : ∀ X : E,
    Presieve.ofArrows (fun b : Bool ↦ X ⨯ objects (if b then 1 else 2))
      (fun _b ↦ prod.fst : ∀ b : Bool, X ⨯ objects (if b then 1 else 2) ⟶ X) ∈ covers X
  nerve : Sheaf J (Type u) ≌ Sheaf covers.toGrothendieck (Type u)
  nerveFormula : nerve.functor ⋙ sheafToPresheaf covers.toGrothendieck (Type u) ≅
    sheafSubcategoryNerve inclusion
  represented : ∀ X : E, Nonempty (nerve.functor.obj (inclusion.obj X) ≅
    covers.toGrothendieck.yoneda.obj X)
  ring : Sheaf covers.toGrothendieck CommRingCat.{u}
  ringed : RingedToposMorphism (localCoefficientRings ring) (localCoefficientRings R)
  inverseNerve : ringed.inverse = nerve.functor
  directNerve : ringed.direct = nerve.inverse
  ringIsIso : IsIso ringed.ringMap
  wholeModules : BinaryPresentationModules ringed
  sourceSlice : ∀ i : Fin 4,
    RingedSheafSliceAdjunctionData (localCoefficientRings R) (inclusion.obj (objects i))
  slice : ∀ i : Fin 4,
    Over (inclusion.obj (objects i)) ≌ Sheaf (covers.toGrothendieck.over (objects i)) (Type u)
  sliceFormula : ∀ i : Fin 4,
    (slice i).functor ⋙ sheafToPresheaf (covers.toGrothendieck.over (objects i)) (Type u) ≅
      yoneda ⋙ (Functor.whiskeringLeft (Over (objects i))ᵒᵖ
        (Over (inclusion.obj (objects i)))ᵒᵖ (Type u)).obj (Over.post inclusion).op
  sliceRinged : ∀ i : Fin 4,
    RingedToposMorphism (localCoefficientRings (ring.over (objects i)))
      (localCoefficientRings (presentationElementRing R (inclusion.obj (objects i))))
  sliceInverse : ∀ i : Fin 4, Nonempty ((sliceRinged i).inverse ≅
    (sourceSlice i).fibreEquivalence.functor ⋙ (slice i).functor)
  sliceRingIsIso : ∀ i : Fin 4, IsIso (sliceRinged i).ringMap
  sliceModules : ∀ i : Fin 4, BinaryPresentationModules (sliceRinged i)
  sourceContinuous : ∀ (i j : Fin 4) (f : objects i ⟶ objects j),
    Functor.IsContinuous (elementMap (inclusion.map f))
      (elementTopology (inclusion.obj (objects i)))
      (elementTopology (inclusion.obj (objects j)))
  restriction : ∀ i : Fin 4, BinaryPresentationAdjointSquare
    wholeModules.modules (sliceModules i).modules
    (elementModulePullback.{u, u} (localCoefficientRings R) (inclusion.obj (objects i)))
    (SheafOfModules.overFunctor.{u} (localCoefficientRings ring) (objects i))

  further : ∀ (i j : Fin 4) (f : objects i ⟶ objects j),
    BinaryPresentationAdjointSquare (sliceModules j).modules (sliceModules i).modules
      (elementModulePullbackOver.{u, u} (localCoefficientRings R) (inclusion.map f)
        (sourceContinuous i j f))
      (SheafOfModules.overMap.{u} (localCoefficientRings ring) f)

  restrictionComposition : ∀ (i j : Fin 4) (f : objects i ⟶ objects j)
      (M : PresentationModules R),
    HEq ((restriction i).comparison.hom.app M)
      ((further i j f).comparison.hom.app
          ((elementModulePullback.{u, u} (localCoefficientRings R)
            (inclusion.obj (objects j))).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((restriction j).comparison.hom.app M) ≫
        (SheafOfModules.overFunctorMap.{u} (localCoefficientRings ring) f).hom.app
          (wholeModules.modules.functor.obj M))
  furtherIdentity : ∀ (i : Fin 4)
      (M : PresentationModules (presentationElementRing R (inclusion.obj (objects i)))),
    HEq ((further i i (𝟙 (objects i))).comparison.hom.app M)
      (𝟙 ((sliceModules i).modules.functor.obj M))
  furtherComposition : ∀ (i j k : Fin 4) (f : objects i ⟶ objects j)
      (g : objects j ⟶ objects k)
      (M : PresentationModules (presentationElementRing R (inclusion.obj (objects k)))),
    HEq ((further i k (f ≫ g)).comparison.hom.app M)
      ((further i j f).comparison.hom.app
          ((elementModulePullbackOver.{u, u} (localCoefficientRings R) (inclusion.map g)
            (sourceContinuous j k g)).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings ring) f).map
          ((further j k g).comparison.hom.app M))

private def generatorShapes : Bool → Type
  | false => Discrete PEmpty
  | true => WalkingCospan

private instance (b : Bool) : SmallCategory (generatorShapes b) := by
  cases b <;> dsimp [generatorShapes] <;> infer_instance

private noncomputable instance (b : Bool) : FinCategory (generatorShapes b) := by
  cases b <;> dsimp [generatorShapes] <;> infer_instance

private theorem binaryGenerators
    {E : Type (u + 1)} [Category.{u} E] [HasFiniteLimits E]
    {I : Type u} (X : I → E) :
    ∃ (C : Type u) (_ : SmallCategory C) (_ : HasFiniteLimits C) (F : C ⥤ E),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧
      ∀ i, ∃ c, Nonempty (F.obj c ≅ X i) := by
  let P := (ObjectProperty.ofObj X).limitsClosure generatorShapes
  have hP (b : Bool) : P.IsClosedUnderLimitsOfShape (generatorShapes b) := inferInstance
  have : P.IsClosedUnderLimitsOfShape (Discrete PEmpty) := hP false
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := hP true
  have : HasFiniteLimits P.FullSubcategory :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits P.ι :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks P.ι
  have : ObjectProperty.EssentiallySmall.{u} P := inferInstance
  let e := equivSmallModel.{u} P.FullSubcategory
  let F := e.inverse ⋙ P.ι
  have : HasFiniteLimits (SmallModel.{u} P.FullSubcategory) :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  have : PreservesFiniteLimits F := by
    dsimp [F]
    exact comp_preservesFiniteLimits _ _
  refine ⟨SmallModel.{u} P.FullSubcategory, inferInstance, inferInstance, F,
    inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  let z : P.FullSubcategory := ⟨X i, ObjectProperty.le_limitsClosure _ _ _ ⟨i⟩⟩
  exact ⟨e.functor.obj z, ⟨P.ι.mapIso (e.unitIso.app z).symm⟩⟩


private def identityRingData {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J RingCat.{u}) :
    RingedToposMorphism.RingData A A where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := 𝟙 _
  ring_zero _ _ h := h
  ring_one _ _ h := h
  ring_add _ _ _ _ h := h
  ring_mul _ _ _ _ h := h

private theorem binaryModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R))
    [g.inverse.IsEquivalence] [IsIso g.ringMap] :
    Nonempty (BinaryPresentationModules g) := by
  obtain ⟨T, ⟨p⟩, a, ha⟩ := ringed_equivalence_module_hom g
  let h := Functor.additive_of_preserves_binary_products T.modules.functor
  let k := Functor.additive_of_preserves_binary_products T.modules.inverse
  let := HasDerivedCategory.standard (PresentationModules R)
  let := HasDerivedCategory.standard (PresentationModules S)
  let := h
  let := k
  exact ⟨{
    modules := T.modules
    additive := h
    inverseAdditive := k
    finiteLimits := inferInstance
    finiteColimits := inferInstance
    inverseFiniteLimits := inferInstance
    inverseFiniteColimits := inferInstance
    underlying := a
    unit := T.forwardUnit
    structural := ha
    pushforward := p
    derived := T.modules.mapDerivedCategory
    derivedFunctor := rfl
    derivedInverse := rfl }⟩

private theorem binarySieveComparison {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C)
    {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g))
    (Cov₀ : Set (Σ A : E, PreZeroHypercover.{max u v w} A))
    (hsmall : Small.{max u v w} Cov₀)
    (hsub : Cov₀ ⊆ sheafSubcategoryEpimorphicFamilies F) :
    (∀ (A : E) (R : PreZeroHypercover.{max u v w} A),
      (⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F ↔
        ∀ (U : C) (a : (F.obj A).obj.obj (op U)),
          Sieve.generate (fun (V : C) (f : V ⟶ U) ↦
            ∃ (i : R.I₀) (b : (F.obj (R.X i)).obj.obj (op V)),
              (F.map (R.f i)).hom.app (op V) b = (F.obj A).obj.map f.op a)
            ∈ J U)) ∧
    ∃ (Cov' : Set (Σ A : E, PreZeroHypercover.{max u v w} A))
      (K : Precoverage E) (hK : K.toGrothendieck.Subcanonical)
      (e : Sheaf J (Type u) ≌ Sheaf K.toGrothendieck (Type u)),
      Small.{max u v w} Cov' ∧ Cov₀ ⊆ Cov' ∧
      Cov' ⊆ sheafSubcategoryEpimorphicFamilies F ∧
      PreZeroHypercover.IsCoveringClass Cov' ∧ K.IsSiteForCoverings ∧
      (∀ (A : E) (R : PreZeroHypercover.{max u v w} A),
        ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F →
          ∃ R' : PreZeroHypercover.{max u v w} A,
            ⟨A, R'⟩ ∈ Cov' ∧ R.presieve₀ = R'.presieve₀) ∧
      (∀ (A : E) (S : Presieve A),
        S ∈ K A ↔ ∃ R : PreZeroHypercover.{max u v w} A,
          ⟨A, R⟩ ∈ Cov' ∧ S = R.presieve₀) ∧
      Nonempty (e.functor ⋙ sheafToPresheaf K.toGrothendieck (Type u) ≅
        sheafSubcategoryNerve F) ∧
      Nonempty (F ⋙ e.functor ⋙ sheafToPresheaf K.toGrothendieck (Type u) ≅ yoneda) ∧
      Nonempty ((@GrothendieckTopology.yoneda E _ K.toGrothendieck hK) ⋙ e.inverse ≅ F) := by
  classical
  -- The argument works directly with the associated Grothendieck topology.
  refine ⟨fun A R ↦ family_epi_iff_local F A R, ?_⟩
  obtain ⟨Cov', hsmall', h₀, hsub', hclass', hcover⟩ :=
    PreZeroHypercover.exists_small_coveringFamilies
      (sheafSubcategoryEpimorphicFamilies F) (family_isCoveringClass F hpb) Cov₀ hsmall hsub
  let K := epiPrecoverage F
  let hK := epiPrecoverage_subcanonical F hpb
  let := nerveToSheaf_isEquivalence F hrep hpb
  let e := (nerveToSheaf F hpb).asEquivalence
  refine ⟨Cov', K, hK, e, hsmall', h₀, hsub', hclass', epiPrecoverage_site F hpb,
    hcover, ?_, ⟨Iso.refl _⟩, ⟨nerve_representable_iso F⟩, ?_⟩
  · intro A S
    constructor
    · intro hS
      let R := presieveFamily.{u, v, w} A S
      have hR : ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F := by
        rw [family_epi_iff_cover, presieveFamily_support]
        exact hS
      obtain ⟨R', hR', heq⟩ := hcover A R hR
      exact ⟨R', hR', (presieveFamily_support A S).symm.trans heq⟩
    · rintro ⟨R, hR, rfl⟩
      exact (family_epi_iff_cover F A R).mp (hsub' hR)
  · exact ⟨Functor.isoWhiskerRight (nerve_representable_sheaf_iso F hpb).symm e.inverse ≪≫
      Functor.associator F e.functor e.inverse ≪≫
      Functor.isoWhiskerLeft F e.unitIso.symm ≪≫ Functor.rightUnitor F⟩



/-- A binary subterminal cover has one simultaneous small subcanonical site presentation,
with the nerve, its four slice nerves, exact module equivalences and ordinary derived
comparisons, preserving the adjunctions by their canonical mates.

Source: Stacks Sites, Tags 03A1 and 03CI, with the simultaneous ringed extension described
in the node; Tags 00Y1, 04GZ and 03EH for slices
(blueprint: lem-sp-binary-cover-site-presentation).

Proof:
1. Close the original sheafified representables and 1,U,V,U×V under terminal
   objects and pullbacks using Mathlib's small limits closure and a small model.
2. Apply the existing comparison proof directly to the original Grothendieck
   topology. Its proof already works with sheafified representables on an arbitrary site.
3. Use the local union hypothesis to lift each generalized element through one
   product projection. This proves that the binary family covers. Choose small
   covering-family representatives preserving the supports of all covers.
4. Transport the coefficient ring along the nerve equivalence, and invert its
   structural map using the ring-data square. Construct its induced module direct
   image and obtain the exact module and termwise derived equivalences.
5. Identify the actual localized sites with the represented slices. Full
   faithfulness and the nerve formula give their displayed Hom formulas.
6. The product/fibre bijection identifies the restricted ring with ring.over Z.
   Naturality for ring operations constructs each localized ringed equivalence.
7. Assemble the localized module equivalences and their coherent restrictions.
8. The two adjunction mates induce bijections on Hom sets: compose the
   equivalences' Hom bijections with the adjunction Hom bijections. Yoneda
   therefore proves their invertibility.
-/
theorem exists_binaryCoverSitePresentation
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U V : Sheaf J (Type u))
    (hU : IsSubterminal U) (hV : IsSubterminal V)
    (hcover : ∀ X : C,
      Sieve.generate (fun (Y : C) (_ : Y ⟶ X) ↦
        Nonempty (U.obj.obj (op Y)) ∨ Nonempty (V.obj.obj (op Y))) ∈ J X) :
    Nonempty (BinaryCoverSitePresentation J R U V) := by
  classical
  let Z : Fin 4 → Sheaf J (Type u) := ![⊤_ _, U, V, U ⨯ V]
  let X : C ⊕ Fin 4 → Sheaf J (Type u) := Sum.elim
    (fun A ↦ (presheafToSheaf J (Type u)).obj (yoneda.obj A)) Z
  obtain ⟨E, hE, hlimE, F, hfull, hfaith, hlimF, hX⟩ := binaryGenerators X
  have hrep : ∀ A : C, ∃ B : E,
      Nonempty (F.obj B ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj A)) :=
    fun A ↦ hX (.inl A)
  choose objects hobjects using fun i : Fin 4 ↦ hX (.inr i)
  let e : ∀ i : Fin 4, F.obj (objects i) ≅ Z i := fun i ↦ (hobjects i).some
  have hZ : ∀ i : Fin 4, IsSubterminal (Z i) := by
    intro i
    fin_cases i
    · exact isSubterminal_of_terminal
    · exact hU
    · exact hV
    · intro A f g
      apply prod.hom_ext
      · exact hU _ _
      · exact hV _ _
  have hobj : ∀ i : Fin 4, IsSubterminal (F.obj (objects i)) := by
    intro i A f g
    apply (cancel_mono (e i).hom).mp
    exact hZ i _ _
  have hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g) := by
    intro A B T f g
    exact ⟨pullback f g, pullback.fst f g, pullback.snd f g,
      (IsPullback.of_hasPullback f g).map F⟩
  obtain ⟨hlocal, Cov, K, hK, N, hsmall, _, hsub, hclass, hsite,
      hsupp, hmem, ⟨hnerve⟩, ⟨hrepresented⟩, _⟩ :=
    binarySieveComparison.{u, u, 0} J F hrep hpb ∅ (by infer_instance) (by simp)
  have hepi : ∀ (A : E) (P : PreZeroHypercover.{u} A),
      P.presieve₀ ∈ K A ↔ ⟨A, P⟩ ∈ sheafSubcategoryEpimorphicFamilies.{u, u, 0} F := by
    intro A P
    constructor
    · intro h
      obtain ⟨Q, hQ, hPQ⟩ := (hmem A _).mp h
      intro B f g hfg
      apply hsub hQ B f g
      intro i
      have hi : P.presieve₀ (Q.f i) := hPQ ▸ Q.presieve₀_f i
      rw [hi.eq_eqToHom_comp_hom_idx, F.map_comp, Category.assoc, hfg hi.idx]
      simp only [Category.assoc]
    · intro h
      obtain ⟨Q, hQ, hPQ⟩ := hsupp A P h
      exact (hmem A _).mpr ⟨Q, hQ, hPQ⟩
  have hbinary (A : E) :
      Presieve.ofArrows (fun b : Bool ↦ A ⨯ objects (if b then 1 else 2))
        (fun _b ↦ prod.fst : ∀ b : Bool, A ⨯ objects (if b then 1 else 2) ⟶ A) ∈ K A := by
    let P : PreZeroHypercover.{u} A :=
      { I₀ := ULift.{u} Bool
        X := fun b ↦ A ⨯ objects (if b.down then 1 else 2)
        f := fun _ ↦ prod.fst }
    have hs : P.presieve₀ = Presieve.ofArrows
        (fun b : Bool ↦ A ⨯ objects (if b then 1 else 2))
        (fun _b ↦ prod.fst : ∀ b : Bool, A ⨯ objects (if b then 1 else 2) ⟶ A) := by
      funext B f
      apply propext
      constructor
      · rintro ⟨b⟩
        exact Presieve.ofArrows.mk b.down
      · rintro ⟨b⟩
        exact Presieve.ofArrows.mk (ULift.up b)
    rw [← hs]
    apply (hepi A P).mpr
    apply (hlocal A P).mpr
    intro T a
    apply J.superset_covering (Sieve.generate_mono ?_) (hcover T)
    intro S f hf
    rcases hf with hf
    have lift (i : Fin 4) (z : (F.obj (objects i)).obj.obj (op S)) :
        ∃ b : (F.obj (A ⨯ objects i)).obj.obj (op S),
          (F.map (prod.fst : A ⨯ objects i ⟶ A)).hom.app (op S) b =
            (F.obj A).obj.map f.op a := by
      let G := F ⋙ sheafToPresheaf J (Type u) ⋙
        (evaluation Cᵒᵖ (Type u)).obj (op S)
      let q := prodComparison G A (objects i) ≫
        (Types.binaryProductIso (G.obj A) (G.obj (objects i))).hom
      obtain ⟨b, hb⟩ := surjective_of_epi q ((F.obj A).obj.map f.op a, z)
      refine ⟨b, ?_⟩
      have hq : q ≫ ↾_root_.Prod.fst = G.map prod.fst := by
        dsimp only [q]
        rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
      change G.map prod.fst b = _
      rw [← hq]
      exact congrArg _root_.Prod.fst hb
    rcases hf with ⟨⟨z⟩⟩ | ⟨⟨z⟩⟩
    · obtain ⟨b, hb⟩ := lift 1 ((e 1).inv.hom.app (op S) z)
      exact ⟨ULift.up true, b, hb⟩
    · obtain ⟨b, hb⟩ := lift 2 ((e 2).inv.hom.app (op S) z)
      exact ⟨ULift.up false, b, hb⟩
  obtain ⟨ring, d, a, hi, hd, hr, hiso⟩ := ringedTopos_equivalenceRingTransport R N
  let := show d.inverse.Full from hi ▸ inferInstance
  let := show d.inverse.Faithful from hi ▸ inferInstance
  let hdiso : IsIso d.ringMap := hiso
  let idR := identityRingData (localCoefficientRings R)
  let α : idR.inverse ⋙ idR.inverse ≅ N.functor ⋙ d.inverse :=
    (Functor.leftUnitor _).trans (N.unitIso.trans (eqToIso (by rw [hi])))
  let invd := RingedToposMorphism.RingData.square idR d idR N.functor α
    N.inverse N.toAdjunction (inferInstance)
  have hinvd : IsIso invd.ringMap := by
    have hm : IsIso (d.inverse.map invd.ringMap) := by
      change IsIso (d.inverse.map (d.inverse.preimage _))
      rw [Functor.map_preimage]
      have hId : IsIso idR.ringMap := by
        change IsIso (𝟙 _)
        infer_instance
      infer_instance
    exact isIso_of_reflects_iso _ d.inverse
  obtain ⟨md⟩ := SheafOfModules.ringData_inducedModules ring R invd
  let g := invd.withModules md
  have : g.inverse.IsEquivalence := by
    change N.functor.IsEquivalence
    infer_instance
  have : IsIso g.ringMap := hinvd
  obtain ⟨whole⟩ := binaryModules g
  choose slice hslice using fun i : Fin 4 ↦
    exists_binaryPresentationSliceNerve F N hnerve (objects i)
  let sliceFormula := fun i : Fin 4 ↦ (hslice i).some
  have hs0 (i : Fin 4) :=
    ringed_sheaf_slice_adjunction (localCoefficientRings R) (F.obj (objects i))
  let sourceSlice := fun i : Fin 4 ↦ (hs0 i).some
  obtain ⟨slices⟩ := exists_binaryPresentationSlices R ring F objects hobj N hnerve g rfl rfl
    hinvd whole sourceSlice slice sliceFormula
  refine ⟨{
    E := E
    inclusion := F
    generators := hrep
    objects := objects
    terminal := e 0
    first := e 1
    second := e 2
    intersection := e 3
    covers := K
    site := hsite
    epimorphic := hepi
    representatives := Cov
    smallRepresentatives := hsmall
    coveringClass := hclass
    representativeCovers := fun A P hP ↦ (hmem A _).mpr ⟨P, hP, rfl⟩
    sameSupports := fun A P hP ↦ hsupp A P ((hepi A P).mp hP)
    binaryCover := hbinary
    nerve := N
    nerveFormula := hnerve
    represented := ?_
    ring := ring
    ringed := g
    inverseNerve := rfl
    directNerve := rfl
    ringIsIso := hinvd
    wholeModules := whole
    sourceSlice := sourceSlice
    slice := slice
    sliceFormula := sliceFormula
    sliceRinged := slices.sliceRinged
    sliceInverse := slices.sliceInverse
    sliceRingIsIso := slices.sliceRingIsIso
    sliceModules := slices.sliceModules
    sourceContinuous := slices.sourceContinuous
    restriction := slices.restriction
    further := slices.further
    restrictionComposition := slices.restrictionComposition
    furtherIdentity := slices.furtherIdentity
    furtherComposition := slices.furtherComposition }⟩
  intro A
  exact ⟨(fullyFaithfulSheafToPresheaf K.toGrothendieck (Type u)).preimageIso
    (hrepresented.app A)⟩

end CategoryTheory
