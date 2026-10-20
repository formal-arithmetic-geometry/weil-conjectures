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
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.FiniteProperLocalizing
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.IntegralProperDirectSums
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.ProperUnboundedCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts

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
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
