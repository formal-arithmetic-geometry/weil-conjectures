/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.AmbientIndDerivedSums
import Sheaf.Paper.FiniteProperLocalizing
import Sheaf.Paper.IntegralProperDirectSums
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.ProperUnboundedCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.Paper.CondensedCoefficientIsoConstructible
import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
import Sheaf.Paper.IntegralConstantModelHeartClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# Proper direct image on localizing categories

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-proper-image-localizing/sk-prop-proper-image-localizing-proper.md and its proof
(blueprint: det-proper-image-localizing-proper).

The coefficient list uses bundled ring objects, so membership identifies both the
underlying condensed abelian sheaf and its multiplication. The two auxiliary predicates
spell out the hypotheses and conclusion of this node, using the recorded ambient
module-object derived category and localizing closure. Coproduct indices have universe
`u + 2`, exactly the indexing universe in the recorded closure of this ambient category.
-/

@[expose] public section

set_option autoImplicit false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject CategoryTheory.Obj

-- Existing coproducts have only Hom-universe many nonzero summands.
private theorem small_coproduct_support
    {C : Type u} [Category.{v} C] [Preadditive C]
    {I : Type w} (G : I → C) (t : Cofan G) (ht : IsColimit t) :
    Small.{v} {i // ¬ IsZero (G i)} := by
  classical
  let p (i : I) : t.pt ⟶ G i := ht.desc (Cofan.mk (G i) (Pi.single i (𝟙 (G i))))
  have hp (i j : I) :
      t.inj j ≫ p i = Pi.single (M := fun j ↦ G j ⟶ G i) i (𝟙 (G i)) j :=
    ht.fac (Cofan.mk (G i) (Pi.single i (𝟙 (G i)))) (Discrete.mk j)
  let q : {i // ¬ IsZero (G i)} → (t.pt ⟶ t.pt) := fun i ↦ p i.val ≫ t.inj i.val
  apply small_of_injective.{v, v, w} (f := q)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (G i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (G i.val) = 0 := by
    simpa only [q, ← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

-- Preservation at the Hom universe implies preservation of every existing coproduct.
private theorem preserves_large_coproducts
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F) (I : Type w) :
    PreservesColimitsOfShape (Discrete I) F := by
  classical
  constructor
  intro K
  let G : I → C := fun i ↦ K.obj ⟨i⟩
  suffices h : PreservesColimit (Discrete.functor G) F by
    let := h
    exact preservesColimit_of_iso_diagram (K₁ := Discrete.functor G) (K₂ := K)
      F (Discrete.natIsoFunctor (F := K)).symm
  constructor
  intro t ht
  let t : Cofan G := t
  have : Small.{v} {i // ¬ IsZero (G i)} := small_coproduct_support G t ht
  let N := {i // ¬ IsZero (G i)}
  let B := Shrink.{v} N
  let e : N ≃ B := equivShrink N
  let r : B → I := fun b ↦ (e.symm b).val
  let U : N → C := fun i ↦ G i.val
  let tN : Cofan U := Cofan.mk t.pt (fun i ↦ t.inj i.val)
  have htN : IsColimit tN := by
    refine Cofan.IsColimit.mk tN (fun s ↦ ht.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (G i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change t.ι.app (Discrete.mk i) ≫ _ = _
      rw [ht.fac]
      simp only [Cofan.mk_ι_app, dif_pos hi]
    · intro s m hm
      apply ht.hom_ext
      intro ⟨i⟩
      rw [ht.fac]
      by_cases hi : ¬ IsZero (G i)
      · simpa only [tN, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let V : B → C := fun b ↦ U (e.symm b)
  let tB : Cofan V := Cofan.mk t.pt (fun b ↦ tN.inj (e.symm b))
  have htB : IsColimit tB :=
    (Cofan.isColimitEquivOfEquiv e.symm tN) htN
  let := hF B
  have hmapped : IsColimit (Cofan.mk (F.obj t.pt) (fun b ↦ F.map (tB.inj b))) :=
    (Cofan.isColimitMapCoconeEquiv F V tB) (isColimitOfPreserves F htB)
  refine ⟨(isColimitMapCoconeCofanMkEquiv F G t.inj).symm ?_⟩
  refine Cofan.IsColimit.mk _
    (fun s ↦ hmapped.desc (Cofan.mk s.pt (fun b ↦ s.inj (r b)))) ?_ ?_
  · intro s i
    by_cases hi : ¬ IsZero (G i)
    · have hh := hmapped.fac (Cofan.mk s.pt (fun b ↦ s.inj (r b)))
        (Discrete.mk (e ⟨i, hi⟩))
      change F.map (t.inj (r (e ⟨i, hi⟩))) ≫ _ = s.inj (r (e ⟨i, hi⟩)) at hh
      have hr : r (e ⟨i, hi⟩) = i := congrArg Subtype.val (e.symm_apply_apply _)
      rw [hr] at hh
      exact hh
    · exact (F.map_isZero (not_not.mp hi)).eq_of_src _ _
  · intro s m hm
    apply hmapped.hom_ext
    intro ⟨b⟩
    rw [hmapped.fac]
    exact hm (r b)

private theorem preserves_large_coproducts_on
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (P : ObjectProperty C)
    (hF : ∀ (I : Type v) (G : I → C), (∀ i, P (G i)) →
      ∃ c : Cofan G, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)))
    (I : Type w) (K : Discrete I ⥤ C) (hK : ∀ i : I, P (K.obj ⟨i⟩)) :
    PreservesColimit K F := by
  classical
  let G : I → C := fun i ↦ K.obj ⟨i⟩
  suffices h : PreservesColimit (Discrete.functor G) F by
    let := h
    exact preservesColimit_of_iso_diagram (K₁ := Discrete.functor G) (K₂ := K)
      F (Discrete.natIsoFunctor (F := K)).symm
  constructor
  intro t ht
  let t : Cofan G := t
  have : Small.{v} {i // ¬ IsZero (G i)} := small_coproduct_support G t ht
  let N := {i // ¬ IsZero (G i)}
  let B := Shrink.{v} N
  let e : N ≃ B := equivShrink N
  let r : B → I := fun b ↦ (e.symm b).val
  let U : N → C := fun i ↦ G i.val
  let tN : Cofan U := Cofan.mk t.pt (fun i ↦ t.inj i.val)
  have htN : IsColimit tN := by
    refine Cofan.IsColimit.mk tN (fun s ↦ ht.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (G i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change t.ι.app (Discrete.mk i) ≫ _ = _
      rw [ht.fac]
      simp only [Cofan.mk_ι_app, dif_pos hi]
    · intro s m hm
      apply ht.hom_ext
      intro ⟨i⟩
      rw [ht.fac]
      by_cases hi : ¬ IsZero (G i)
      · simpa only [tN, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let V : B → C := fun b ↦ U (e.symm b)
  let tB : Cofan V := Cofan.mk t.pt (fun b ↦ tN.inj (e.symm b))
  have htB : IsColimit tB :=
    (Cofan.isColimitEquivOfEquiv e.symm tN) htN
  obtain ⟨c, ⟨hc⟩, ⟨hFc⟩⟩ := hF B V (fun b ↦ hK (r b))
  have : PreservesColimit (Discrete.functor V) F :=
    preservesColimit_of_preserves_colimit_cocone hc hFc
  have hmapped : IsColimit (Cofan.mk (F.obj t.pt) (fun b ↦ F.map (tB.inj b))) :=
    (Cofan.isColimitMapCoconeEquiv F V tB) (isColimitOfPreserves F htB)
  refine ⟨(isColimitMapCoconeCofanMkEquiv F G t.inj).symm ?_⟩
  refine Cofan.IsColimit.mk _
    (fun s ↦ hmapped.desc (Cofan.mk s.pt (fun b ↦ s.inj (r b)))) ?_ ?_
  · intro s i
    by_cases hi : ¬ IsZero (G i)
    · have hh := hmapped.fac (Cofan.mk s.pt (fun b ↦ s.inj (r b)))
        (Discrete.mk (e ⟨i, hi⟩))
      change F.map (t.inj (r (e ⟨i, hi⟩))) ≫ _ = s.inj (r (e ⟨i, hi⟩)) at hh
      have hr : r (e ⟨i, hi⟩) = i := congrArg Subtype.val (e.symm_apply_apply _)
      rw [hr] at hh
      exact hh
    · exact (F.map_isZero (not_not.mp hi)).eq_of_src _ _
  · intro s m hm
    apply hmapped.hom_ext
    intro ⟨b⟩
    rw [hmapped.fac]
    exact hm (r b)

private theorem localizingClosure_isLocalizing
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) : IsLocalizingSubcategory (localizingClosure S) := by
  let L := localizingClosure S
  have hIso : L.IsClosedUnderIsomorphisms := ⟨by
    intro K K' e hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)⟩
  let := hIso
  have hZero : L.ContainsZero := ⟨⟨0, isZero_zero C, by
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.prop_zero⟩⟩
  have hShift : L.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro K hK P hP hS
    let := hP.1
    exact P.le_shift n K (hK P hP hS)⟩⟩
  have hTri : L.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃ P hP hS
    let := hP.1
    let := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hS) (h₃ P hP hS))
  refine ⟨?_, hIso, ?_⟩
  · exact
      { toContainsZero := hZero
        toIsStableUnderShift := hShift
        toIsTriangulatedClosed₂ := hTri }
  · intro I F hF h
    change ∀ P, IsLocalizingSubcategory P → (∀ K, S K → P K) → P (colimit F)
    intro P hP hS
    exact hP.2.2 F hF (fun i ↦ h i P hP hS)

private theorem localizingClosure_map
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hS : ∀ K, S K → T (F.obj K))
    (hF : ∀ (I : Type u) (G : Discrete I ⥤ (localizingClosure S).FullSubcategory),
      PreservesColimit (G ⋙ (localizingClosure S).ι) F) :
    ∀ K, localizingClosure S K → localizingClosure T (F.obj K) := by
  let L := localizingClosure S
  let M := localizingClosure T
  have hL := localizingClosure_isLocalizing S
  have hM := localizingClosure_isLocalizing T
  let := hL.1
  let := hL.2.1
  let := hM.1
  let := hM.2.1
  let P := L ⊓ M.inverseImage F
  have hP : IsLocalizingSubcategory P := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I G hG h
    let := hG
    have hLG : L (colimit G) := hL.2.2 G hG (fun i ↦ (h i).1)
    refine ⟨hLG, ?_⟩
    let G' := L.lift G (fun i ↦ (h i.as).1)
    have : PreservesColimit G F := hF I G'
    have hMG : M (colimit (G ⋙ F)) :=
      hM.2.2 (G ⋙ F) inferInstance (fun i ↦ (h i).2)
    exact M.prop_of_iso (preservesColimitIso F G).symm hMG
  intro K hK
  exact (hK P hP (fun K hK ↦ ⟨fun Q hQ hSQ ↦ hSQ K hK,
    fun Q hQ hTQ ↦ hTQ _ (hS K hK)⟩)).2

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The two hypotheses in the proper localizing-image statement: preservation of
bounded constructible finite-Tor objects and of ambient sums of localizing objects.
Source: blueprint det-proper-image-localizing-proper, first paragraph
(blueprint: det-proper-image-localizing-proper). -/
def ProperLocalizingHypotheses
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  (∀ K : ConstantModelConstructibleFiniteTor Λ X,
    (constantModelBoundedConstructible Λ Y ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L)
        ((lowerStar Λ p).rightDerivedFunctor.obj K.obj)) ∧
  ∀ (I : Type (u + 2)) (F : Discrete I ⥤ (localizingClosureProEtale Λ X).FullSubcategory),
    PreservesColimit (F ⋙ (localizingClosureProEtale Λ X).ι)
      (lowerStar Λ p).rightDerivedFunctor

/-- The canonical restriction of the total derived pushforward is triangulated
and preserves every small coproduct. The subcategory structures are the induced
ones from the ambient derived categories, and the functor is the standard lift of
inclusion followed by the total derived pushforward, with its induced shift structure.
Source: blueprint det-proper-image-localizing-proper, first paragraph
(blueprint: det-proper-image-localizing-proper). -/
def ProperLocalizingRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  ObjectProperty.IsTriangulated (localizingClosureProEtale Λ X) ∧
  ObjectProperty.IsTriangulated (localizingClosureProEtale Λ Y) ∧
  ∀ [ObjectProperty.IsTriangulated (localizingClosureProEtale Λ X)]
    [ObjectProperty.IsTriangulated (localizingClosureProEtale Λ Y)],
  ∃ h : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ Y ((lowerStar Λ p).rightDerivedFunctor.obj K.obj),
    (ObjectProperty.lift (localizingClosureProEtale Λ Y)
      ((localizingClosureProEtale Λ X).ι ⋙ (lowerStar Λ p).rightDerivedFunctor)
      h).IsTriangulated ∧
    ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I)
      (ObjectProperty.lift (localizingClosureProEtale Λ Y)
        ((localizingClosureProEtale Λ X).ι ⋙ (lowerStar Λ p).rightDerivedFunctor) h)

/-- Proper direct image restricts to an exact, sum-preserving functor on the
localizing categories, provided it preserves the generators and ambient sums of
localizing objects. The coefficient list is exactly the admissible list, with the
finite ring discrete, finite subfield E, and finite-subextension condensed Qbar.

Source: blueprint det-proper-image-localizing-proper, first paragraph and first
proof paragraph (blueprint: det-proper-image-localizing-proper).

Proof: lowerStar is additive, so its total right derived functor is triangulated
(lem-pc-right-derived-functor-triangulated). Inside the source localizing closure,
take the objects whose image belongs to the target localizing closure. Exactness
makes this subcategory replete and triangulated. The first hypothesis puts all
Dctf generators in it. For a family in it, the second hypothesis identifies the
image of its ambient sum with the sum of its images, so this subcategory is
closed under sums. Minimality of sk-def-localizing-closure makes it the entire
source closure. ObjectProperty.isTriangulated_lift gives exactness of the lift
(lem-weil-pbc-triangulated-functor-restriction). Fullness and closure under sums
identify subcategory coproducts with ambient coproducts, giving preservation of
sums by that same lift. Only sums of localizing objects were used. -/
theorem proper_image_localizing_proper
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (_hΛ : Λ ∈ [Mon.mk (Profinite.continuousMapRingObj A),
      Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ]),
      Mon.mk (Profinite.padicIntegersRingObj ℓ E.val),
      Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]),
      Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj ℓ)])
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] :
    ProperLocalizingHypotheses Λ.X p → ProperLocalizingRestriction Λ.X p := by
  intro h
  let S := constantModelBoundedConstructible Λ.X X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let T := constantModelBoundedConstructible Λ.X Y ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosure S
  let M := localizingClosure T
  let F := (lowerStar Λ.X p).rightDerivedFunctor
  have hL := localizingClosure_isLocalizing S
  have hM := localizingClosure_isLocalizing T
  refine ⟨hL.1, hM.1, ?_⟩
  intro instL instM
  let := hL.2.1
  let := hM.2.1
  have hmap : ∀ K : L.FullSubcategory, M (F.obj K.obj) := fun K ↦
    localizingClosure_map S T F (fun K hK ↦ h.1 ⟨K, hK⟩) h.2 K.obj K.property
  refine ⟨hmap, inferInstance, ?_⟩
  let C := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ.X X)
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C :=
    fun I ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} C (Discrete I)
  have : HasCoproducts.{u + 1}
      (DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ.X X))) := derived_hasCoproducts
  have hι (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) L.ι := by
    have hclosed : L.IsClosedUnderColimitsOfShape (Discrete (ULift.{u + 2} I)) :=
      .mk' (by
        rintro K ⟨G, hG⟩
        exact hL.2.2 G inferInstance (fun i ↦ hG ⟨i⟩))
    let := hclosed
    have : L.IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
        (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))
    let := createsColimitsOfShapeFullSubcategoryInclusion (Discrete I) L
    infer_instance
  intro I
  have : PreservesColimitsOfShape (Discrete I) L.ι :=
    preserves_large_coproducts L.ι hι I
  constructor
  intro G
  have : PreservesColimit (G ⋙ L.ι) F := h.2 I G
  have : PreservesColimit G (L.ι ⋙ F) := inferInstance
  have : PreservesColimit G (M.lift (L.ι ⋙ F) hmap ⋙ M.ι) :=
    preservesColimit_of_natIso G (M.liftCompιIso (L.ι ⋙ F) hmap).symm
  exact preservesColimit_of_reflects_of_preserves (M.lift (L.ι ⋙ F) hmap) M.ι



private theorem bounded_mem_of_single
    {A : Type u'} [Category.{v'} A] [Abelian A] [HasDerivedCategory.{v'} A]
    (Q : ObjectProperty A) [Q.IsClosedUnderIsomorphisms]
    (P : ObjectProperty (DerivedCategory A)) [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulated]
    (hs : ∀ M, Q M → P ((DerivedCategory.singleFunctor A 0).obj M))
    (K : DerivedCategory A) (hK : DerivedCategory.TStructure.t.bounded K)
    (hQ : ∀ q : ℤ, Q ((DerivedCategory.homologyFunctor A q).obj K)) : P K := by
  have hsingle (M : A) (hM : Q M) (b : ℤ) :
      P ((DerivedCategory.singleFunctor A b).obj M) := by
    exact P.prop_of_iso
      ((((DerivedCategory.singleFunctors A).shiftIso (-b) b 0 (by simp)).app M))
      (P.le_shift (-b) _ (hs M hM))
  suffices H : ∀ (n : ℕ) (K : DerivedCategory A) (a b : ℤ), b - a ≤ n →
      K.IsGE a → K.IsLE b →
      (∀ q : ℤ, a ≤ q → q ≤ b →
        Q ((DerivedCategory.homologyFunctor A q).obj K)) → P K by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
    exact H (b - a).toNat K a b (by omega) ha hb (fun q _ _ ↦ hQ q)
  intro n
  induction n with
  | zero =>
    intro K a b hab _ _ hQ
    by_cases hlt : b < a
    · exact P.prop_of_isZero (DerivedCategory.TStructure.t.isZero K b a hlt)
    · have : K.IsGE b := DerivedCategory.TStructure.t.isGE_of_ge K b a (by omega)
      obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K b
      have hM := Q.prop_of_iso
        ((DerivedCategory.homologyFunctor A b).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app M) (hQ b (by omega) le_rfl)
      exact P.prop_of_iso e.symm (hsingle M hM b)
  | succ n ih =>
    intro K a b hab _ _ hQ
    by_cases hba : b < a
    · exact P.prop_of_isZero (DerivedCategory.TStructure.t.isZero K b a hba)
    have hab' : a ≤ b := by omega
    let t := DerivedCategory.TStructure.t (C := A)
    let T := (t.triangleLTGE b).obj K
    have hT := t.triangleLTGE_distinguished b K
    have h₁ : P T.obj₁ := by
      apply ih T.obj₁ a (b - 1) (by omega)
        (inferInstanceAs (t.IsGE ((t.truncLT b).obj K) a))
        (t.isLE_truncLT_obj K b (b - 1) (by omega))
      intro q hqa hqb
      have := DerivedCategory.isIso_homologyMap_mor₁ T hT (q - 1) q (by omega)
        (DerivedCategory.isZero_of_isGE _ b _ (by omega))
        (DerivedCategory.isZero_of_isGE _ b _ (by omega))
      exact Q.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A q).map T.mor₁)).symm
        (hQ q hqa (by omega))
    have h₃ : P T.obj₃ := by
      apply ih T.obj₃ b b (by omega)
        (inferInstanceAs (t.IsGE ((t.truncGE b).obj K) b))
        (inferInstanceAs (t.IsLE ((t.truncGE b).obj K) b))
      intro q hqa hqb
      have := DerivedCategory.isIso_homologyMap_mor₂ T hT q (q + 1) rfl
        (DerivedCategory.isZero_of_isLE _ (b - 1) _ (by omega))
        (DerivedCategory.isZero_of_isLE _ (b - 1) _ (by omega))
      exact Q.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A q).map T.mor₂))
        (hQ q (by omega) hqb)
    exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

private noncomputable def continuousCoefficientMonIso
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let h := Profinite.continuousMapRingSheafMap e.toRingHom he
  let k := Profinite.continuousMapRingSheafMap e.symm.toRingHom hei
  let q : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := h
      inv := k
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply (x.down t)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply (x.down t) }
  let F := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  have _ : IsMonHom (F.mapIso q).hom :=
    inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat Ab)).map h))
  exact Mon.mkIso' (F.mapIso q)

private noncomputable def bottomCoefficientIsos (ℓ : ℕ) [Fact ℓ.Prime] :
    (Mon.mk (Profinite.continuousMapRingObj.{u} ℚ_[ℓ]) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u}
        (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ℓ))) ×
    (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ℓ]) ≅
      Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ
        (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ℓ))) := by
  let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let e : ℚ_[ℓ] ≃+* E :=
    (IntermediateField.botEquiv ℚ_[ℓ] (PadicAlgCl ℓ)).symm.toRingEquiv
  have hn (x : ℚ_[ℓ]) : ‖e x‖ = ‖x‖ := by
    change ‖algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) x‖ = ‖x‖
    exact PadicAlgCl.norm_extends ℓ x
  have he : Isometry e := (AddMonoidHomClass.isometry_iff_norm e).2 hn
  have hei : Continuous e.symm := (show ℚ_[ℓ] ≃ᵢ E from ⟨e.toEquiv, he⟩).symm.continuous
  refine ⟨continuousCoefficientMonIso e he.continuous hei, ?_⟩
  let φ := padicIntToIntegers ℓ E
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val h
    · intro x
      obtain ⟨q, hq⟩ := e.surjective x.val
      have hq' : ‖q‖ ≤ 1 := by
        rw [← hn, hq]
        exact_mod_cast x.property
      refine ⟨⟨q, hq'⟩, ?_⟩
      apply Subtype.ext
      exact hq
  let ez := RingEquiv.ofBijective φ hφ
  have hnz (x : ℤ_[ℓ]) : ‖ez x‖ = ‖x‖ := by
    change ‖e (x : ℚ_[ℓ])‖ = ‖(x : ℚ_[ℓ])‖
    exact hn _
  have hez : Isometry ez := (AddMonoidHomClass.isometry_iff_norm ez).2 hnz
  exact continuousCoefficientMonIso ez hez.continuous
    (show ℤ_[ℓ] ≃ᵢ PadicAlgCl.integers ℓ E from ⟨ez.toEquiv, hez⟩).symm.continuous

private theorem ctf_iso_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _
      ).IsClosedUnderIsomorphisms := by
  have h := constantModelConstructibleFiniteTor_wellDefined Λ X
  let := h.2.1
  let := h.2.2.2.1
  infer_instance

private noncomputable def coefficient_roundtrip
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u}) :
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStarFromPoint X).map e.inv.hom)).mapDerivedCategory ⋙
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStarFromPoint X).map e.hom.hom)).mapDerivedCategory ≅ 𝟭 _ := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  refine (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp _ _).symm ≪≫ Mod.comapCongr ?_ ≪≫ Mod.comapId _) ≪≫
    Functor.mapDerivedCategoryIdIso _
  rw [← Functor.map_comp]
  change (upperStarFromPoint X).map (((Mon.forget _).map e.hom) ≫
    ((Mon.forget _).map e.inv)) = 𝟙 _
  rw [← Functor.map_comp, e.hom_inv_id]
  change (upperStarFromPoint X).map (𝟙 Λ) = 𝟙 _
  exact (upperStarFromPoint X).map_id Λ

private theorem proper_hypotheses_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : ProperLocalizingHypotheses Λ' p) : ProperLocalizingHypotheses Λ p := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  let H (Z : Scheme.{u}) :=
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      ((upperStarFromPoint Z).map e.inv.hom)).mapDerivedCategory
  have hH (Z : Scheme.{u}) : (H Z).IsEquivalence := by
    have : (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      ((upperStarFromPoint Z).map e.inv.hom)).IsEquivalence :=
      inferInstanceAs (Mod.comapEquivalenceOfIsIso
        ((upperStarFromPoint Z).map e.inv.hom)).functor.IsEquivalence
    infer_instance
  have : (H X).IsEquivalence := hH X
  have : (H Y).IsEquivalence := hH Y
  have hpres (J : Type (u + 2))
      (D : Discrete J ⥤ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) : PreservesColimit D (H X) := by
    have hshape : PreservesColimitsOfShape (Discrete J) (H X) :=
      (CategoryTheory.Adjunction.isEquivalence_preservesColimits (H X)).preservesColimitsOfShape
    exact hshape.preservesColimit
  have : ∀ Z : Scheme.{u},
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom Z)) := by
    intro Z
    exact preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (coefficientMap e.inv.hom Z)).symm
  let cmp : (lowerStar Λ p).rightDerivedFunctor ⋙ H Y ≅
      H X ⋙ (lowerStar Λ' p).rightDerivedFunctor :=
    derivedComapLowerStarIso e.inv.hom p
  have hclosed (Z : Scheme.{u}) := ctf_iso_closed Λ Z
  have hclosed' (Z : Scheme.{u}) := ctf_iso_closed Λ' Z
  constructor
  · intro K
    have hK := constantModelCtf_coefficientIso e X K
    have hP := h.1 ⟨(H X).obj K.obj, hK⟩
    have hP' := (hclosed' Y).of_iso ((cmp.app K.obj).symm) hP
    have hB := constantModelCtf_coefficientIso e.symm Y
      ⟨(H Y).obj ((lowerStar Λ p).rightDerivedFunctor.obj K.obj), hP'⟩
    exact (hclosed Y).of_iso ((coefficient_roundtrip e Y).app _) hB
  · intro I K
    let S := constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _
    let T := constantModelBoundedConstructible Λ' X ⊓ DerivedCategory.finiteTorAmplitude _
    have hm : ∀ M, localizingClosure S M → localizingClosure T ((H X).obj M) :=
      localizingClosure_map S T (H X)
        (fun M hM ↦ constantModelCtf_coefficientIso e X ⟨M, by simpa [S] using hM⟩)
        (fun J D ↦ hpres J (D ⋙ (localizingClosure S).ι))
    let G := K ⋙ (localizingClosureProEtale Λ X).ι
    let G' := (localizingClosureProEtale Λ' X).lift (G ⋙ H X)
      (fun i ↦ hm _ (show localizingClosure S (K.obj i).obj
        from (K.obj i).property))
    have : PreservesColimit (G ⋙ H X) (lowerStar Λ' p).rightDerivedFunctor := h.2 I G'
    have : PreservesColimit G (H X) := hpres I G
    have : PreservesColimit G (H X ⋙ (lowerStar Λ' p).rightDerivedFunctor) := inferInstance
    have : PreservesColimit G ((lowerStar Λ p).rightDerivedFunctor ⋙ H Y) :=
      preservesColimit_of_natIso G cmp.symm
    exact preservesColimit_of_reflects_of_preserves (lowerStar Λ p).rightDerivedFunctor (H Y)

private theorem geometric_fibre_bound
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] [CompactSpace Y] :
    ∃ d : ℕ, ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound p
  refine ⟨d, fun y ↦ ?_⟩
  let a : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Spec (Y.residueField y) :=
    Spec.map (CommRingCat.ofHom
    (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y))))
  have : LocallyOfFiniteType (p.fiberToSpecResidueField y) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    exact MorphismProperty.pullback_snd _ _ inferInstance
  calc
    _ = topologicalKrullDim
        (pullback (p.fiberToSpecResidueField y) a : Scheme.{u}) := by
      exact (IsHomeomorph.topologicalKrullDim_eq _
        (pullbackLeftPullbackSndIso p (Y.fromSpecResidueField y) a).hom.homeomorph.isHomeomorph
        ).symm
    _ ≤ topologicalKrullDim (p.fiber y) :=
      topologicalKrullDim_pullback_le_of_field (p.fiberToSpecResidueField y) a
    _ ≤ (d : WithBot ℕ∞) := hd y

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]

include k

private theorem rational_hypotheses
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ)) : ProperLocalizingHypotheses Λ.X p := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have hcoef :
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hΛ with ⟨E, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  have eqT := (localizingClosure_ctf_equals_bc ℓ Y Λ.X hcoef).1.2.2.1
  have eqL := (localizingClosure_ctf_equals_bc ℓ X Λ.X hcoef).1.2.2.2.1
  have hEq (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
      [QuasiCompact (T ↘ Spec (.of k))] :
      constantModelBoundedConstructible Λ.X T = boundedConstructible (condensedRingObj Λ.X T) := by
    have h := (finiteCoefficientDescentTwoColimit k (ringChar k) ℓ
      (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) T).2.2.2
    rcases hΛ with ⟨E, rfl⟩ | rfl
    · exact (h.1 E).1
    · exact h.2.1.1
  constructor
  · intro K
    rw [eqT]
    let XO := Over.mk (X ↘ Spec (.of k))
    let YO := Over.mk (Y ↘ Spec (.of k))
    have : LocallyOfFiniteType XO.hom := inferInstanceAs (LocallyOfFiniteType (X ↘ _))
    have : QuasiCompact XO.hom := inferInstanceAs (QuasiCompact (X ↘ _))
    have : IsSeparated XO.hom := inferInstanceAs (IsSeparated (X ↘ _))
    have : LocallyOfFiniteType YO.hom := inferInstanceAs (LocallyOfFiniteType (Y ↘ _))
    have : QuasiCompact YO.hom := inferInstanceAs (QuasiCompact (Y ↘ _))
    have : IsSeparated YO.hom := inferInstanceAs (IsSeparated (Y ↘ _))
    let po : XO ⟶ YO := Over.homMk p
    have : IsProper po.left := inferInstanceAs (IsProper p)
    exact (congrFun (hEq Y) _).mpr
      (properPushforward_boundedConstructible_rational ℓ (k := k) po Λ hΛ K.obj
        ((congrFun (hEq X) _).mp K.property.1))
  · obtain ⟨d, hd⟩ := geometric_fibre_bound p
    have hs : ProperUnboundedCoproductAssertions Λ.X p := by
      rcases hΛ with ⟨E, rfl⟩ | rfl
      · exact properUnbounded_preservesCoproducts ℓ E k (ringChar k)
          (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) X Y p d hd
      · exact properUnbounded_preservesCoproducts_padicAlgCl ℓ k (ringChar k)
          (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) X Y p d hd
    have hDic : localizingClosure (constantModelBoundedConstructible Λ.X X) ≤
        fun K ↦ ∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ.X X)
          ((DerivedCategory.homologyFunctor _ n).obj K) := by
      rcases hΛ with ⟨E, rfl⟩ | rfl
      · exact (indConstructibleDerived_sums_and_truncations ℓ E k (ringChar k)
          (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) X).2.2.2.2
      · exact (indConstructibleDerived_sums_and_truncations_padicAlgCl ℓ k (ringChar k)
          (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) X).2.2.2.2
    intro I G
    apply preserves_large_coproducts_on _
      (fun K ↦ ∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ.X X)
        ((DerivedCategory.homologyFunctor _ n).obj K)) ?_ I _
      (fun i ↦ hDic _ (eqL ▸ (G.obj ⟨i⟩).property))
    intro J K hK
    obtain ⟨c, hc, c', hc', _, _, hi⟩ := hs.2 J K hK
    have := hi
    refine ⟨c, ⟨hc⟩, ?_⟩
    exact ⟨(Cofan.isColimitMapCoconeEquiv _ K c).symm hc'.ofPointIso⟩

private theorem integral_hypotheses (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ProperLocalizingHypotheses (Profinite.padicIntegersRingObj ℓ E) p := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : IsNoetherian X := {}
  let : IsNoetherian Y := {}
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  let Λ := Profinite.padicIntegersRingObj ℓ E
  have hcoef :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
    Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩))
  have eqT := (localizingClosure_ctf_equals_bc ℓ Y Λ hcoef).1.2.2.1
  have eqL := (localizingClosure_ctf_equals_bc ℓ X Λ hcoef).1.2.2.2.1
  obtain ⟨d, hd⟩ := geometric_fibre_bound p
  have h := integralProperDirectSums ℓ E k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) X Y p d hd
  constructor
  · intro K
    rw [eqT]
    let Q : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := IsConstantModelConstructible Λ X
    let R : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) := IsConstantModelConstructible Λ Y
    have : Q.IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined Λ X).1
    have : R.IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined Λ Y).1
    have : R.ContainsZero := by
      refine ⟨⟨0, isZero_zero _, ?_⟩⟩
      change IsConstantModelConstructible Λ Y 0
      rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
      -- A one-stratum zero model also covers the empty scheme.
      let S : Scheme.Stratification Y :=
        { n := 1
          stratum := fun _ ↦ Set.univ
          isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
          isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
          iUnion_stratum_eq_univ := Set.iUnion_const _
          pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
          domain := fun _ ↦ Y
          immersion := fun _ ↦ 𝟙 Y
          range_immersion := fun _ ↦ Set.range_id' }
      refine ⟨S, fun a ↦ ?_⟩
      refine ⟨.singleton (𝟙 (S.domain a)) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
      refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
      · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
      · exact ((CondensedRing.upperStar Λ _).map_isZero
          ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero (isZero_zero _))).iso
            (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))
    have hc := isConstantModelConstructible_serre_padicIntegers Y ℓ E
    have : R.IsClosedUnderKernels := ⟨by
      rintro _ ⟨f, c, hlim, h⟩
      exact R.prop_of_iso (hlim.conePointUniqueUpToIso (kernelIsKernel f)).symm
        (hc.1 _ _ f h.1 h.2).1⟩
    have : R.IsClosedUnderCokernels := ⟨by
      rintro _ ⟨f, c, hcolim, h⟩
      exact R.prop_of_iso (hcolim.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm
        (hc.1 _ _ f h.1 h.2).2⟩
    have : R.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦ hc.2 _ hS h₁ h₃⟩
    have : (DerivedCategory.homologyProperty R).IsTriangulated := inferInstance
    have : (constantModelBoundedConstructible Λ Y).IsTriangulated :=
      inferInstanceAs (DerivedCategory.TStructure.t.bounded ⊓
        DerivedCategory.homologyProperty R).IsTriangulated
    have : (constantModelBoundedConstructible Λ Y).IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined Λ Y).2.1
    exact bounded_mem_of_single Q
      ((constantModelBoundedConstructible Λ Y).inverseImage (lowerStar Λ p).rightDerivedFunctor)
      (fun M hM ↦ (h.1 M hM).1) K.obj K.property.1.1 K.property.1.2
  · intro I G
    apply preserves_large_coproducts_on _
      (localizingClosure (constantModelBoundedConstructible Λ X))
      h.2.2.2.2.2 I _ (fun i ↦ eqL ▸ (G.obj ⟨i⟩).property)

private noncomputable def finite_coefficient_iso
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (finiteDiscreteCondensedCoefficient (ULift.{u} A)) := by
  let B := ULift.{u} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let h : Profinite.continuousMapRingSheaf.{u} A ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((ULift.ringEquiv.symm.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheafOfUniverse.{u, u} B ⟶
      Profinite.continuousMapRingSheaf.{u} A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((ULift.ringEquiv.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let e : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u} B :=
    { hom := h
      inv := v
      hom_inv_id := by ext S f; rfl
      inv_hom_id := by ext S f; rfl }
  let e' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso e
  letI : IsMonHom e'.hom := Sheaf.isMonHom_sheafCompose_map _ e.hom
  exact Mon.mkIso' e'

private theorem finite_hypotheses
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ n : ℕ, (ℓ ^ n : A) = 0) :
    ProperLocalizingHypotheses (Profinite.continuousMapRingObj A) p := by
  apply proper_hypotheses_coefficientIso (finite_coefficient_iso A) p
  have hA' : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : ULift.{u} A) = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n + 1, Nat.succ_pos _, ?_⟩
    apply ULift.ext
    change (ℓ ^ (n + 1) : ℕ) • (1 : A) = 0
    simp only [nsmul_eq_mul, Nat.cast_pow, mul_one, pow_succ, Nat.cast_mul, hn, zero_mul]
  have h := finiteProperLocalizing ℓ (ringChar k) (Fact.out : ℓ.Prime)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) k (ULift.{u} A) hA' p
  exact ⟨fun K ↦ h.1 K.obj K.property,
    fun I G ↦ h.2.2.2 I (G ⋙ (localizingClosureProEtale _ X).ι)
      (fun i ↦ (G.obj ⟨i⟩).property)⟩

end Coefficients

attribute [local irreducible] Functor.rightDerivedFunctor upperStarFromPoint

/-- In the standing separated finite-type positive-characteristic field setting,
both hypotheses of proper_image_localizing_proper hold for every admissible coefficient.
The list includes Q_ell and Z_ell explicitly, as the E = Q_ell specializations.

Source: blueprint det-proper-image-localizing-proper, coefficient assertions and
second proof paragraph (blueprint: det-proper-image-localizing-proper).

Proof: for E and Qbar, the schemes are qcqs by lem-weil-pbc-qcqs-over-affine.
By det-def-localizing-closure-ctf-equals-bc, Dctf equals Dbc, and the rational
proper base-change theorem det-thm-sfb-proper-base-change-rational preserves Dbc.
By det-ambient-ind-derived-sums their localizing closure lies in Dic;
sk-lem-proper-unbounded-window-ii therefore supplies exactly the required sums.
For finite A, det-ctf-finite-proper-localizing gives preservation of Dctf and
an exact sum-preserving restriction; its sums are ambient by fullness and sum
closure. No identification Dctf = Dbc for arbitrary finite A is used.
For O_E, qcqs again gives Dctf = Dbc; det-thm-sfb-proper-base-change-integral
preserves Dbc. Properness and quasi-compactness of the target give a uniform
fibre-dimension bound by lem-fin-finite-type-fibre-dimension-bound, and
det-prop-int-compactness-direct-sums gives preservation of sums on that closure.
Taking E = Q_ell yields the Q_ell and Z_ell cases. -/
theorem proper_image_localizing_proper_coefficients
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (_hΛ : Λ ∈ [Mon.mk (Profinite.continuousMapRingObj A),
      Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ]),
      Mon.mk (Profinite.padicIntegersRingObj ℓ E.val),
      Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]),
      Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj ℓ)])
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    ProperLocalizingHypotheses Λ.X p := by
  classical
  simp only [List.mem_cons, List.not_mem_nil, or_false] at _hΛ
  rcases _hΛ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact finite_hypotheses ℓ k p A _hA
  · let F : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
    exact proper_hypotheses_coefficientIso (bottomCoefficientIsos.{u} ℓ).2 p
      (integral_hypotheses ℓ k p F)
  · exact integral_hypotheses ℓ k p E
  · let F : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
    exact proper_hypotheses_coefficientIso (bottomCoefficientIsos.{u} ℓ).1 p
      (rational_hypotheses ℓ k p _ (Or.inl ⟨F, rfl⟩))
  · exact rational_hypotheses ℓ k p _ (Or.inl ⟨E, rfl⟩)
  · exact rational_hypotheses ℓ k p _ (Or.inr rfl)

end AlgebraicGeometry.ProEtale.CondensedRing
