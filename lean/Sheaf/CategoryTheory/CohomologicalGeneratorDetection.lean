/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CompactObject
public import Sheaf.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import Sheaf.CategoryTheory.CompactGeneratorsBuildObjects
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-! Detection of cohomological isomorphisms on compact generators.

Source: Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`
(blueprint: lem-pc-cohomological-generator-detection).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{v} C]

/-- A map from a representable cohomological functor to H is invertible everywhere
if it is invertible on every shift of the compact generators.

Source: Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`, final paragraph.
(blueprint: lem-pc-cohomological-generator-detection).

Proof: let D' consist of objects Y for which α is invertible at every shift of Y.
Naturality and the two cohomological long exact sequences give closure under
triangles by the five lemma. Shift composition gives closure under shifts, and
naturality gives closure under isomorphisms. Both functors carry coproducts to
products, so D' is closed under coproducts. Applying triangle closure to telescope
triangles gives closure under sequential homotopy colimits. The hypotheses put all
generators and their shifts in D'. The compact-generator construction of every
object from these shifts, coproducts, cones and a telescope then puts every object
in D'. At shift zero this gives the claimed invertibility. -/
theorem cohomologicalGeneratorDetection
    {I : Type v} (E : I → C) (hcompact : ∀ i : I, IsCompactObject (E i))
    (hgenerate : IsTriangulatedGeneratingFamily E)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H)
    (G : C) (α : preadditiveYoneda.obj G ⟶ H)
    (hα : ∀ (i : I) (n : ℤ), IsIso (α.app (Opposite.op ((E i)⟦n⟧)))) :
    ∀ X : Cᵒᵖ, IsIso (α.app X) := by
  have cohomological_five_exact
      (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [F.IsHomological]
      (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) :
      (ComposableArrows.mk₄ (F.map T.mor₃.op) (F.map T.mor₂.op)
        (F.map T.mor₁.op) (F.map T.invRotate.mor₁.op)).Exact := by
    apply ComposableArrows.exact_of_δ₀
    · exact (F.map_distinguished_op_exact T.rotate
        (Pretriangulated.rot_of_distTriang T hT)).exact_toComposableArrows
    · apply ComposableArrows.exact_of_δ₀
      · exact (F.map_distinguished_op_exact T hT).exact_toComposableArrows
      · exact (F.map_distinguished_op_exact T.invRotate
          (Pretriangulated.inv_rot_of_distTriang T hT)).exact_toComposableArrows
  -- Naturality gives the morphism of five-term exact rows.
  have cohomological_iso_middle
      (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
      (G : C) (α : preadditiveYoneda.obj G ⟶ H)
      (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C)
      (h₀ : IsIso (α.app (Opposite.op (T.obj₁⟦(1 : ℤ)⟧))))
      (h₁ : IsIso (α.app (Opposite.op T.obj₃)))
      (h₃ : IsIso (α.app (Opposite.op T.obj₁)))
      (h₄ : IsIso (α.app (Opposite.op (T.obj₃⟦(-1 : ℤ)⟧)))) :
      IsIso (α.app (Opposite.op T.obj₂)) := by
    have : IsIso (α.app (Opposite.op T.invRotate.obj₁)) := h₄
    let φ : ComposableArrows.mk₄
        ((preadditiveYoneda.obj G).map T.mor₃.op)
        ((preadditiveYoneda.obj G).map T.mor₂.op)
        ((preadditiveYoneda.obj G).map T.mor₁.op)
        ((preadditiveYoneda.obj G).map T.invRotate.mor₁.op) ⟶
        ComposableArrows.mk₄ (H.map T.mor₃.op) (H.map T.mor₂.op)
          (H.map T.mor₁.op) (H.map T.invRotate.mor₁.op) :=
      ComposableArrows.homMk₄ (α.app _) (α.app _) (α.app _) (α.app _) (α.app _)
        (α.naturality _) (α.naturality _) (α.naturality _) (α.naturality _)
    exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
      (cohomological_five_exact _ T hT) (cohomological_five_exact H T hT) φ
      (by dsimp [φ]; infer_instance) h₁ h₃ (by dsimp [φ]; infer_instance)
  -- Read the coproduct universal property as a limiting fan in the opposite category.
  have cohomological_iso_coproduct
      (H : Cᵒᵖ ⥤ AddCommGrpCat.{v})
      (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H)
      (G : C) (α : preadditiveYoneda.obj G ⟶ H)
      (J : Type v) (F : J → C) (hF : ∀ j, IsIso (α.app (Opposite.op (F j)))) :
      IsIso (α.app (Opposite.op (∐ F))) := by
    let c : Fan (fun j ↦ Opposite.op (F j)) :=
      Fan.mk (Opposite.op (∐ F)) (fun j ↦ (Sigma.ι F j).op)
    have hc : IsLimit c := Fan.IsLimit.mk _
      (fun s ↦ (Sigma.desc (fun j ↦ (s.proj j).unop)).op)
      (by intro s j; apply Quiver.Hom.unop_inj; simp [c])
      (by intro s m hm; apply Quiver.Hom.unop_inj
          apply Sigma.hom_ext; intro j
          simpa [c] using congrArg Quiver.Hom.unop (hm j))
    have := hH J
    let L := preadditiveYoneda.obj G
    let β := Functor.whiskerLeft (Discrete.functor (fun j ↦ Opposite.op (F j))) α
    have : ∀ j, IsIso (β.app j) := fun j ↦ hF j.as
    have : IsIso β := NatIso.isIso_of_isIso_app β
    let e := IsLimit.conePointsIsoOfNatIso
      (isLimitOfPreserves L hc) (isLimitOfPreserves H hc) (asIso β)
    have he : e.hom = α.app c.pt := by
      apply (isLimitOfPreserves H hc).hom_ext
      intro j
      rw [IsLimit.conePointsIsoOfNatIso_hom_comp]
      exact α.naturality (c.π.app j)
    change IsIso (α.app c.pt)
    rw [← he]
    infer_instance
  let P : C → Prop := fun Y ↦ ∀ n : ℤ, IsIso (α.app (Opposite.op (Y⟦n⟧)))
  have hiso {Y Z : C} (e : Y ≅ Z) (hZ : P Z) : P Y := by
    intro n
    exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctor C n).mapIso e).op).mp (hZ n)
  have hshift {Y : C} (hY : P Y) (m : ℤ) : P (Y⟦m⟧) := by
    intro n
    exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorAdd C m n).app Y).op).mpr
      (hY (m + n))
  have hcoprod (J : Type v) (F : J → C) (hF : ∀ j, P (F j)) : P (∐ F) := by
    intro n
    have h := cohomological_iso_coproduct H hH G α J (fun j ↦ (F j)⟦n⟧)
      (fun j ↦ hF j n)
    exact (NatTrans.isIso_app_iff_of_iso α
      (PreservesCoproduct.iso (shiftFunctor C n) F).op).mp h
  have htri (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C)
      (h₁ : P T.obj₁) (h₃ : P T.obj₃) : P T.obj₂ := by
    intro n
    exact cohomological_iso_middle H G α (T⟦n⟧)
      (Pretriangulated.Triangle.shift_distinguished T hT n)
      (hshift h₁ n 1) (h₃ n) (h₁ n) (hshift h₃ n (-1))
  intro Y
  obtain ⟨X, t, ⟨J₀, i₀, m₀, ⟨e₀⟩⟩, ⟨Z, a, b, hZ, hT⟩, q, r, htel⟩ :=
    compactGenerators_buildObjects E hcompact hgenerate Y.unop
  have hZE : ∀ n, P (Z n) := by
    intro n
    obtain ⟨J, i, m, ⟨e⟩⟩ := hZ n
    exact hiso e (hcoprod J _ (fun j ↦ hshift (hα (i j)) (m j)))
  have hX : ∀ n, P (X n) := by
    intro n
    induction n with
    | zero => exact hiso e₀ (hcoprod J₀ _ (fun j ↦ hshift (hα (i₀ j)) (m₀ j)))
    | succ n ih =>
      exact htri (Pretriangulated.Triangle.mk (a n) (t n) (b n)).rotate
        (Pretriangulated.rot_of_distTriang _ (hT n)) ih (hshift (hZE n) 1)
  have hsum := hcoprod (ULift.{v} ℕ) (fun n ↦ X n.down) (fun n ↦ hX n.down)
  have hY : P Y.unop := htri _ (Pretriangulated.rot_of_distTriang _ htel)
    hsum (hshift hsum 1)
  exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorZero C ℤ).app Y.unop).op).mpr
    (hY 0)

end CategoryTheory
