module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.Triangulated.FullyFaithfulGenerator

/-!
# Adjunction-unit defects on finite triangulated generators

Source: the proper coefficient-change obligation in paragraph (3) of
`sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md` in the 2026-10-15 blueprint;
Stacks Project, Tags 0149, 014A, 05QB and 02C3.
(blueprint: lem-sfb-adjunction-generator-defect-criterion)

The finite triangulated closure is specified by its least-subcategory universal property:
`T₀` is replete, triangulated, contains `G`, and is contained in every such subcategory.
These are finitary closure operations, so this is precisely the closure by finite
constructions. No coproduct or retract closure is imposed.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open Limits Pretriangulated

set_option backward.isDefEq.respectTransparency false in
/-- The unit-cone orthogonality criterion for an exact adjunction on finite generators.

Source: paragraph (3), proper coefficient-change obligation, in the 2026-10-15 blueprint
`sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md`; Stacks Tags 0149, 014A, 05QB and 02C3.
(blueprint: lem-sfb-adjunction-generator-defect-criterion)

Proof:
1. Naturality of the adjunction identifies the adjunct of `F.map f` with
   `f ≫ adj.unit.app _`. Undoing the specified shift comparison gives the displayed formula.
   Compatibility of the adjunction with shifts identifies shifted units with units of shifts.
2. For generators `G₁,G₂`, complete the unit of `G₂` to a distinguished triangle.
   Apply representable Hom exactness to all shifts and rotations (Tag 0149). The two
   adjacent Hom groups into its cone vanish, so composition with the shifted unit is
   bijective. The adjunction identifies this with the shifted map induced by `F`.
3. For a fixed first generator, the objects in the second variable for which every
   shifted map is bijective form a replete triangulated class. Zero and shift closure
   follow from exactness. For an extension, use the exact five-term Hom rows and the
   five lemma (Tag 05QB). Minimality of `T₀` gives the assertion for all its objects.
4. Fix an object of `T₀` in the second variable and repeat with contravariant Hom.
   Reindex shifts to handle shifts in the first variable. The second five-lemma
   induction gives all pairs in `T₀`; at shift zero this is full faithfulness.
5. Lift any arrow between image objects by fullness, after conjugating by the given
   isomorphisms. Complete its lift to a source triangle. Its third vertex lies in `T₀`.
   Exactness maps it to a distinguished triangle. TR3 compares this triangle with any
   specified target cone triangle; the third component is invertible by Tag 014A.
6. The replete essential image contains zero and is shift closed. The preceding cone
   assertion, applied also after rotation, gives extension closure, hence triangulatedness.
7. When the essential image is `U₀`, corestrict `F` to `U₀`. Full faithfulness and
   essential surjectivity give an equivalence (Tag 02C3).
8. Lift the inverse shift comparisons through the fully faithful functor, using the
   counit of this equivalence. Faithfulness checks naturality and coherence. For any
   distinguished target triangle, complete the first arrow of its inverse image to a
   source triangle. Apply TR3 and Tag 014A after applying `F`, and lift the resulting
   triangle isomorphism back by full faithfulness. Thus the inverse is exact. The
   equivalence and its comparison with the specified restriction commute with shifts.
   Both inductions start at zero even for an empty class or only zero generators.
-/
theorem Adjunction.generator_defect_criterion
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    [CategoryTheory.IsTriangulated C] [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) (U : D ⥤ C) [F.CommShift ℤ] [U.CommShift ℤ]
    [F.IsTriangulated] [U.IsTriangulated] (adj : F ⊣ U) [adj.CommShift ℤ]
    (G T₀ : ObjectProperty C) [T₀.IsTriangulated] [T₀.IsClosedUnderIsomorphisms]
    (hG : G ≤ T₀)
    (hT₀ : ∀ (S : ObjectProperty C) [S.IsTriangulated] [S.IsClosedUnderIsomorphisms],
      G ≤ S → T₀ ≤ S)
    (hdefect : ∀ (G₁ G₂ : C), G G₁ → G G₂ →
      ∀ (R : C) (g : U.obj (F.obj G₂) ⟶ R) (h : R ⟶ G₂⟦(1 : ℤ)⟧),
        Triangle.mk (adj.unit.app G₂) g h ∈ distTriang C →
        ∀ n : ℤ, Subsingleton (G₁ ⟶ R⟦n⟧)) :
    (∀ (P Q : C), T₀ P → T₀ Q → ∀ n : ℤ,
      Function.Bijective (fun f : P ⟶ Q⟦n⟧ ↦
        F.map f ≫ (F.commShiftIso n).hom.app Q)) ∧
    (∀ (P Q : C) (n : ℤ) (f : P ⟶ Q⟦n⟧),
      adj.homEquiv P (F.obj (Q⟦n⟧))
          ((F.map f ≫ (F.commShiftIso n).hom.app Q) ≫ (F.commShiftIso n).inv.app Q) =
        f ≫ adj.unit.app (Q⟦n⟧)) ∧
    Nonempty (T₀.ι ⋙ F).FullyFaithful ∧
    (T₀.ι ⋙ F).essImage.IsTriangulated ∧
    (∀ (P Q : C), T₀ P → T₀ Q → ∀ (A B Z : D)
      (eP : F.obj P ≅ A) (eQ : F.obj Q ≅ B)
      (a : A ⟶ B) (b : B ⟶ Z) (c : Z ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang D →
      ∃ (f : P ⟶ Q) (R : C) (g : Q ⟶ R) (h : R ⟶ P⟦(1 : ℤ)⟧),
        T₀ R ∧ F.map f ≫ eQ.hom = eP.hom ≫ a ∧
        Triangle.mk f g h ∈ distTriang C ∧
        Nonempty (F.mapTriangle.obj (Triangle.mk f g h) ≅ Triangle.mk a b c)) ∧
    (∀ (U₀ : ObjectProperty D) [U₀.IsTriangulated] [U₀.IsClosedUnderIsomorphisms],
      (T₀.ι ⋙ F).essImage = U₀ →
      ∃ (E : T₀.FullSubcategory ≌ U₀.FullSubcategory)
        (_ : E.functor.CommShift ℤ) (_ : E.inverse.CommShift ℤ),
        E.CommShift ℤ ∧ E.functor.IsTriangulated ∧ E.inverse.IsTriangulated ∧
        ∃ e : E.functor ⋙ U₀.ι ≅ T₀.ι ⋙ F, NatTrans.CommShift e.hom ℤ) := by
  classical
  have _ := hG
  have hgen : ∀ X Y : C, G X → G Y → F.HomBijectiveShifts X Y := by
    intro X Y hX hY
    apply F.homBijectiveShifts_of_forall
    intro n
    obtain ⟨R, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app Y)
    let T := Triangle.mk (adj.unit.app Y) g h
    have hz (m : ℤ) (f : X ⟶ R⟦m⟧) : f = 0 :=
      (hdefect X Y hX hY R g h hT m).elim _ _
    have hTn := Triangle.shift_distinguished T hT n
    have hu : Function.Bijective (fun f : X ⟶ Y⟦n⟧ ↦
        f ≫ (adj.unit.app Y)⟦n⟧') := by
      constructor
      · intro a b hab
        dsimp only at hab
        have hab' : (a - b) ≫ (T⟦n⟧).mor₁ = 0 := by
          change (a - b) ≫ (n.negOnePow • (adj.unit.app Y)⟦n⟧') = 0
          rw [Linear.comp_units_smul, Preadditive.sub_comp, hab, sub_self, smul_zero]
        obtain ⟨c, hc⟩ := Triangle.coyoneda_exact₂ _
          (inv_rot_of_distTriang _ hTn) (a - b) hab'
        have hc0 : c = 0 := by
          let e := (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).app R
          have he := hz (n - 1) (c ≫ e.inv)
          simpa using congrArg (fun k ↦ k ≫ e.hom) he
        simpa [hc0, sub_eq_zero] using hc
      · intro a
        obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ _ hTn (n.negOnePow • a) (by
          change (n.negOnePow • a) ≫ (n.negOnePow • g⟦n⟧') = 0
          rw [Linear.comp_units_smul, Linear.units_smul_comp,
            hz n (a ≫ g⟦n⟧'), smul_zero, smul_zero])
        refine ⟨b, ?_⟩
        change n.negOnePow • a = b ≫ (n.negOnePow • (adj.unit.app Y)⟦n⟧') at hb
        rw [Linear.comp_units_smul] at hb
        exact (smul_left_cancel n.negOnePow hb).symm
    have hunit : Function.Bijective (fun f : X ⟶ Y⟦n⟧ ↦
        f ≫ adj.unit.app (Y⟦n⟧)) := by
      have he := (Iso.homCongr (Iso.refl X) (((F ⋙ U).commShiftIso n).app Y).symm).bijective
      have hh := he.comp hu
      simpa only [Function.comp_def, Iso.homCongr_apply, Iso.refl_inv,
        Category.id_comp, Category.assoc, Iso.symm_hom, Iso.app_inv,
        adj.unit_app_shift_commShiftIso_inv_app] using hh
    let e := adj.homEquiv X (F.obj (Y⟦n⟧))
    have hh : Function.Bijective (e ∘ F.map) := by
      simpa only [Function.comp_def, e, Adjunction.homEquiv_unit,
        adj.unit_naturality, Functor.comp_obj] using hunit
    exact hh.of_comp_left e.injective
  have hall : ∀ P Q : C, T₀ P → T₀ Q → F.HomBijectiveShifts P Q := by
    intro P Q hP hQ
    apply hT₀ (F.homBijectiveShiftsLeft Q) _ P hP
    intro X hX
    exact hT₀ (F.homBijectiveShiftsRight X) (fun Y hY ↦ hgen X Y hX hY) Q hQ
  have hb : ∀ P Q : C, T₀ P → T₀ Q → F.HomBijective P Q :=
    fun P Q hP hQ ↦ (hall P Q hP hQ).homBijective
  have hff : (T₀.ι ⋙ F).FullyFaithful := by
    let : (T₀.ι ⋙ F).Full :=
      ⟨fun {X Y} f ↦ by
        obtain ⟨g, hg⟩ := (hb X.obj Y.obj X.property Y.property).2 f
        exact ⟨T₀.homMk g, hg⟩⟩
    let : (T₀.ι ⋙ F).Faithful :=
      ⟨fun {X Y} f g h ↦ T₀.ι.map_injective
        ((hb X.obj Y.obj X.property Y.property).1 h)⟩
    exact .ofFullyFaithful _
  let := hff.full
  let := hff.faithful
  refine ⟨?_, ?_, ⟨hff⟩, inferInstance, ?_, ?_⟩
  · intro P Q hP hQ n
    have hn := (hall P Q hP hQ).shift_right n |>.homBijective
    simpa only [Function.comp_def, Iso.homCongr_apply, Iso.refl_inv,
      Category.id_comp, Iso.app_hom]
      using ((Iso.homCongr (Iso.refl (F.obj P)) ((F.commShiftIso n).app Q)).bijective).comp hn
  · intro P Q n f
    simp [Adjunction.homEquiv_unit]
  · intro P Q hP hQ A B Z eP eQ a b c hT
    obtain ⟨f, hf⟩ := (hb P Q hP hQ).2 (eP.hom ≫ a ≫ eQ.inv)
    obtain ⟨R, g, h, hS⟩ := distinguished_cocone_triangle f
    have hR := T₀.ext_of_isTriangulatedClosed₃ _ hS hP hQ
    have hf' : F.map f ≫ eQ.hom = eP.hom ≫ a := by simp [hf]
    exact ⟨f, R, g, h, hR, hf', hS,
      ⟨isoTriangleOfIso₁₂ _ _ (F.map_distinguished _ hS) hT eP eQ hf'⟩⟩
  · intro U₀ _ _ hU₀
    let L := U₀.lift (T₀.ι ⋙ F) (fun X ↦ by
      rw [← hU₀]
      exact (T₀.ι ⋙ F).obj_mem_essImage X)
    let : L.EssSurj := ⟨fun Y ↦ by
      have hY : (T₀.ι ⋙ F).essImage Y.obj := by rw [hU₀]; exact Y.property
      obtain ⟨X, ⟨e⟩⟩ := hY
      exact ⟨X, ⟨U₀.isoMk e⟩⟩⟩
    let : L.IsEquivalence := {}
    let E := L.asEquivalence
    let : E.functor.CommShift ℤ := by
      change L.CommShift ℤ
      infer_instance
    let := E.commShiftInverse ℤ
    let : E.CommShift ℤ := E.commShift_of_functor ℤ
    let : E.functor.IsTriangulated := by
      change L.IsTriangulated
      infer_instance
    let : E.inverse.IsTriangulated := E.toAdjunction.isTriangulated_rightAdjoint
    exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      U₀.liftCompιIso _ _, inferInstance⟩

end CategoryTheory
