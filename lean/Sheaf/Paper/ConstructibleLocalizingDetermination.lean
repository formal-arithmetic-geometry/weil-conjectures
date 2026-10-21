/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.LocalizingClosureExistence
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Checking isomorphisms on constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-sf-determination,
statement and proof (blueprint: sk-lem-sf-determination).

The functors are defined on the actual localizing full subcategories, with the
triangulations inherited from the unbounded derived categories of module objects.
No extension to the ambient derived categories is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The localizing full subcategory inherits its triangulation from the ambient
unbounded derived category. This is the triangulated-closure projection of
`localizingClosure_exists`, specialized to the recorded constructible finite-Tor
class; it introduces no new triangulation or assumption.

Source: blueprint main-20261015, sk-lem-sf-determination, proof step 1, using
sk-def-localizing-closure and det-def-localizing-closure-existence, clause 2
(blueprint: sk-lem-sf-determination). -/
instance localizingClosureProEtale_isTriangulated
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (localizingClosureProEtale Λ X).IsTriangulated :=
  (localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X ⊓ fun K ↦
      DerivedCategory.finiteTorAmplitude _ K)).2.2.2.1.1

-- The existing universe-extension criterion is recorded as
-- lem-exc-coproduct-preservation-universe-extension. Its source declarations are private,
-- so reproduce their proved small-support argument here, without importing their consumers.
private theorem coproduct_small_support.{w, v, u₂, v₂}
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [LocallySmall.{w} D]
    {I : Type v} (K : I → D) (t : Cofan K) (ht : IsColimit t) :
    Small.{w} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : t.pt ⟶ K i := ht.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : t.inj j ≫ p i = Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    ht.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

/-- Shrinking nonzero support extends preservation to every indexing universe. -/
private theorem preservesCoproducts_of_small.{w, v, u₁, u₂, v₁, v₂}
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [LocallySmall.{w} D]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (c : D ⥤ C) [c.PreservesZeroMorphisms]
    (hsmall : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) c)
    (I : Type v) : PreservesColimitsOfShape (Discrete I) c := by
  classical
  have hpres (K : I → D) : PreservesColimit (Discrete.functor K) c := by
    refine ⟨fun {t} ht ↦ ⟨?_⟩⟩
    let t₀ : Cofan K := t
    have hsupport : Small.{w} {i // ¬ IsZero (K i)} := coproduct_small_support K t₀ ht
    let J := {i // ¬ IsZero (K i)}
    have : PreservesColimitsOfShape (Discrete (Shrink.{w} J)) c := hsmall _
    have : PreservesColimitsOfShape (Discrete J) c :=
      preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink J)).symm c
    let U : J → D := fun i ↦ K i.val
    let r : Cofan U := Cofan.mk t.pt (fun i ↦ t₀.inj i.val)
    have hr : IsColimit r := by
      refine Cofan.IsColimit.mk r (fun s ↦ ht.desc (Cofan.mk s.pt
        (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
      · intro s i
        obtain ⟨i, hi⟩ := i
        change t.ι.app (Discrete.mk i) ≫ _ = _
        rw [ht.fac]
        simp only [Cofan.mk_ι_app, dif_pos hi]
      · intro s m hm
        apply ht.hom_ext
        intro ⟨i⟩
        rw [ht.fac]
        by_cases hi : ¬ IsZero (K i)
        · simpa only [r, cofan_mk_inj, t₀, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
            using hm ⟨i, hi⟩
        · exact (not_not.mp hi).eq_of_src _ _
    let q : Cofan (fun i ↦ c.obj (U i)) :=
      Cofan.mk (c.obj t.pt) (fun i ↦ c.map (t₀.inj i.val))
    have hq : IsColimit q := isColimitCofanMkObjOfIsColimit c U _ hr
    refine { desc := fun s ↦ hq.desc (Cofan.mk s.pt
        (fun i ↦ s.ι.app (Discrete.mk i.val))), fac := ?_, uniq := ?_ }
    · intro s ⟨i⟩
      by_cases hi : ¬ IsZero (K i)
      · exact hq.fac (Cofan.mk s.pt (fun i ↦ s.ι.app (Discrete.mk i.val)))
          (Discrete.mk ⟨i, hi⟩)
      · exact (c.map_isZero (not_not.mp hi)).eq_of_src _ _
    · intro s m hm
      apply Cofan.IsColimit.hom_ext hq
      intro i
      exact (hm (Discrete.mk i.val)).trans
        (hq.fac (Cofan.mk s.pt (fun i ↦ s.ι.app (Discrete.mk i.val)))
          (Discrete.mk i)).symm
  exact preservesColimitsOfShape_of_discrete c

/-- A shift-compatible transformation between exact, coproduct-preserving functors
on the localizing categories is invertible everywhere if it is invertible on
bounded constructible finite-Tor complexes.

The generator hypothesis is expressed on objects of the source full subcategory:
every ambient generator belongs to that subcategory by the defining intersection.
The ambient derived categories use the recorded canonical Grothendieck-category
localizations in the fixed Hom universe.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-sf-determination,
statement and proof (blueprint: sk-lem-sf-determination).

Proof:
1. Use localizingClosure_exists to obtain repleteness, triangulated structure and
closure under existing ambient coproducts for the source localizing intersection.
2. Extend preservation from the Hom universe u + 1 to the object universe u + 2.
For any existing coproduct, its nonzero summands embed in its endomorphism set
by their coordinate idempotents. Shrink that support, apply the assumed small
coproduct preservation, and add back the zero summands. The two private helpers
reproduce the proved criterion lem-exc-coproduct-preservation-universe-extension,
whose source declarations are private.
3. The existing upstream isoLocus instances give triangulated structure and
repleteness, using shift compatibility and triangle two-out-of-three. Map the
locus along the fully faithful exact inclusion into the ambient derived category.
For any existing ambient coproduct of its objects, lift its diagram to the source
full subcategory. The inclusion creates this coproduct; preservation by both
functors and isIso_app_coconePt_of_preservesColimit give invertibility there.
Thus the ambient image of the locus is localizing.
4. Every generator belongs to the closure and satisfies hη. The defining
intersection places every source object in the ambient image of the locus.
Lift its witnessing isomorphism through the fully faithful inclusion and use
repleteness of isoLocus to obtain the required component isomorphism.
No extension of either functor to the ambient category is needed. -/
theorem isIso_app_of_constructibleFiniteTor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) (X Y : Scheme.{u})
    (F₁ F₂ : (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Y).FullSubcategory)
    [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₁.IsTriangulated] [F₂.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F₁]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F₂]
    (η : F₁ ⟶ F₂) [NatTrans.CommShift η ℤ]
    (hη : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      (constantModelBoundedConstructible Λ X K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) → IsIso (η.app K)) :
    ∀ K : (localizingClosureProEtale Λ X).FullSubcategory, IsIso (η.app K) := by
  have _ := hΛ
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let P := localizingClosureProEtale Λ X
  have hP : IsLocalizingSubcategory P := (localizingClosure_exists Λ X S).2.2.2.1
  let : P.IsClosedUnderIsomorphisms := hP.2.1
  let (I : Type (u + 2)) : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
      rintro _ ⟨D, hD⟩
      exact hP.2.2 D inferInstance (fun i ↦ hD ⟨i⟩))
  let : ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I) F₁ :=
    fun I ↦ preservesCoproducts_of_small F₁ (fun _ ↦ inferInstance) I
  let : ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I) F₂ :=
    fun I ↦ preservesCoproducts_of_small F₂ (fun _ ↦ inferInstance) I
  let Q := η.isoLocus.map P.ι
  have hQ : IsLocalizingSubcategory Q := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I D hD hmem
    let := hD
    have hDP : ∀ i, P (D.obj i) := by
      rintro ⟨i⟩
      obtain ⟨K, _, ⟨e⟩⟩ := hmem i
      exact P.prop_of_iso e K.property
    let E := P.lift D hDP
    have : HasColimit (E ⋙ P.ι) := by change HasColimit D; infer_instance
    let : CreatesColimit E P.ι :=
      createsColimitFullSubcategoryInclusionOfClosed (Discrete I) P E
    let : HasColimit E := hasColimit_of_created E P.ι
    have hE : ∀ i, η.isoLocus (E.obj i) := by
      rintro ⟨i⟩
      obtain ⟨K, hK, ⟨e⟩⟩ := hmem i
      exact η.isoLocus.prop_of_iso (P.fullyFaithfulι.preimageIso e) hK
    have : ∀ i, IsIso ((Functor.whiskerLeft E η).app i) := hE
    have : IsIso (Functor.whiskerLeft E η) :=
      NatIso.isIso_of_isIso_app _
    have hcolim : η.isoLocus (colimit E) :=
      isIso_app_coconePt_of_preservesColimit E η _ (colimit.isColimit E)
    exact ⟨colimit E, hcolim,
      ⟨(isColimitOfPreserves P.ι (colimit.isColimit E)).coconePointUniqueUpToIso
        (colimit.isColimit D)⟩⟩
  have hSQ : S ≤ Q := by
    intro K hK
    let K' : P.FullSubcategory := ⟨K, (localizingClosure_exists Λ X S).2.2.2.2.1 K hK⟩
    exact ⟨K', hη K' hK, ⟨Iso.refl _⟩⟩
  intro K
  obtain ⟨L, hL, ⟨e⟩⟩ := K.property Q hQ hSQ
  exact η.isoLocus.prop_of_iso (P.fullyFaithfulι.preimageIso e) hL

end AlgebraicGeometry.ProEtale
