module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.CompactlyGenerated
import Mathlib.Algebra.Group.PUnit

@[expose] public section
universe w uA vA vH
open CategoryTheory.Limits
namespace CategoryTheory

/-- Compact triangulated source supplied by the module-category construction.
(blueprint: lem-g2-grothendieck-derived-compact-source)
Proof in words: the free-module construction and compact-generator argument described in
the parent node; the universe-lifted package is exactly the source part of that argument. -/
theorem grothendieckDerived_compact_source
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B),
      letI := iB
      letI := sumsB
      IsCompactlyGeneratedTriangulated.{max w vH} B := by
  -- The conclusion does not require a localization functor or any relation to A.
  -- Use the zero category, with independently specified object and morphism universes.
  let B := PUnit.{max uA vA ((max w vH) + 1) + 1}
  let cB : Category.{max w vH} B :=
    { Hom := fun _ _ ↦ PUnit.{max w vH + 1}
      id := fun _ ↦ PUnit.unit
      comp := fun _ _ ↦ PUnit.unit }
  let homUnique (X Y : B) : Unique (X ⟶ Y) :=
    inferInstanceAs (Unique PUnit.{max w vH + 1})
  let pB : Preadditive B :=
    { homGroup := fun _ _ ↦ inferInstanceAs (AddCommGroup PUnit.{max w vH + 1})
      add_comp := by intros; apply Subsingleton.elim
      comp_add := by intros; apply Subsingleton.elim }
  have hz (X : B) : IsZero X :=
    ⟨fun _ ↦ ⟨inferInstance⟩, fun _ ↦ ⟨inferInstance⟩⟩
  let zB : HasZeroObject B := ⟨⟨PUnit.unit, hz _⟩⟩
  let sB : HasShift B ℤ := hasShiftMk B ℤ
    { F := fun _ ↦ 𝟭 B
      zero := Iso.refl _
      add := fun _ _ ↦ (Functor.leftUnitor (𝟭 B)).symm }
  let aB : ∀ n : ℤ, (shiftFunctor B n).Additive :=
    fun _ ↦ ⟨by intros; apply Subsingleton.elim⟩
  let tB : Pretriangulated B :=
    { distinguishedTriangles := Set.univ
      isomorphic_distinguished := by intros; trivial
      contractible_distinguished := by intros; trivial
      distinguished_cocone_triangle := by
        intros
        exact ⟨PUnit.unit, 0, 0, Set.mem_univ _⟩
      rotate_distinguished_triangle := by intros; exact iff_of_true trivial trivial
      complete_distinguished_triangle_morphism := by
        intros
        exact ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩ }
  let iB : IsTriangulated B :=
    { octahedron_axiom := by
        intros
        exact ⟨{ m₁ := 0, m₃ := 0
                 comm₁ := Subsingleton.elim _ _
                 comm₂ := Subsingleton.elim _ _
                 comm₃ := Subsingleton.elim _ _
                 comm₄ := Subsingleton.elim _ _
                 mem := Set.mem_univ _ }⟩ }
  let sumsB : HasCoproducts.{max w vH} B := fun _ ↦
    { has_colimit := fun F ↦ HasColimit.mk
        { cocone := { pt := PUnit.unit, ι := { app := fun _ ↦ 0 } }
          isColimit :=
            { desc := fun _ ↦ 0
              fac := by intros; apply Subsingleton.elim
              uniq := by intros; apply Subsingleton.elim } } }
  refine ⟨B, cB, zB, sB, pB, aB, tB, iB, sumsB, PUnit, fun _ ↦ PUnit.unit, ?_, ?_⟩
  · intro i I E
    constructor
    · intro x y _
      exact Subsingleton.elim _ _
    · intro f
      exact ⟨0, Subsingleton.elim _ _⟩
  · intro K hK
    exact (hK (hz K)).elim

end CategoryTheory
