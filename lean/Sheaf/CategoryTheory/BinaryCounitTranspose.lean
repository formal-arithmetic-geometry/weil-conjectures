module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! # Binary counit substitution and comparison transpose

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-compatibility/fix-prop-coherence.proof.md, coefficient-comparison paragraph
(blueprint: lem-pur-binary-counit-transpose).
The auxiliary definitions expand exactly the maps named in the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory
open scoped CategoryTheory.Prod
namespace BinaryCounitTranspose

variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
variable {C₂ : Type u₃} [Category.{v₃} C₂] {D₂ : Type u₄} [Category.{v₄} D₂]
variable {C₃ : Type u₅} [Category.{v₅} C₃] {D₃ : Type u₆} [Category.{v₆} D₃]

/-- The specified binary comparison r. Source: blueprint fix-prop-coherence,
coefficient comparisons (blueprint: lem-pur-binary-counit-transpose). -/
def comparison {R₁ : C₁ ⥤ D₁} {R₂ : C₂ ⥤ D₂}
    {R₃ : C₃ ⥤ D₃} {L₃ : D₃ ⥤ C₃} (adj₃ : R₃ ⊣ L₃)
    (B : (D₁ × D₂) ⥤ D₃) (barB : (C₁ × C₂) ⥤ C₃)
    (d : R₁.prod R₂ ⋙ B ⋙ L₃ ≅ barB) (I : C₁) (J : C₂) :
    R₃.obj (barB.obj (I, J)) ⟶ B.obj (R₁.obj I, R₂.obj J) :=
  R₃.map (d.inv.app (I, J)) ≫ adj₃.counit.app (B.obj (R₁.obj I, R₂.obj J))

/-- The map E on two counits. Source: blueprint fix-prop-coherence, coefficient comparisons
(blueprint: lem-pur-binary-counit-transpose). -/
def evaluation {R₁ : C₁ ⥤ D₁} {L₁ : D₁ ⥤ C₁} (adj₁ : R₁ ⊣ L₁)
    {R₂ : C₂ ⥤ D₂} {L₂ : D₂ ⥤ C₂} (adj₂ : R₂ ⊣ L₂)
    (B : (D₁ × D₂) ⥤ D₃) (L₃ : D₃ ⥤ C₃) (M : D₁) (N : D₂) :
    L₃.obj (B.obj (R₁.obj (L₁.obj M), R₂.obj (L₂.obj N))) ⟶ L₃.obj (B.obj (M, N)) :=
  L₃.map (B.map (adj₁.counit.app M ×ₘ adj₂.counit.app N))

/-- The map a, using the inverse obtained by functorially mapping the two inverse counits.
Source: blueprint fix-prop-coherence, coefficient comparisons
(blueprint: lem-pur-binary-counit-transpose). -/
def inverseComparison {R₁ : C₁ ⥤ D₁} {L₁ : D₁ ⥤ C₁} (adj₁ : R₁ ⊣ L₁)
    {R₂ : C₂ ⥤ D₂} {L₂ : D₂ ⥤ C₂} (adj₂ : R₂ ⊣ L₂)
    (B : (D₁ × D₂) ⥤ D₃) (L₃ : D₃ ⥤ C₃) (barB : (C₁ × C₂) ⥤ C₃)
    (d : R₁.prod R₂ ⋙ B ⋙ L₃ ≅ barB) (M : D₁) (N : D₂)
    [IsIso (adj₁.counit.app M)] [IsIso (adj₂.counit.app N)] :
    L₃.obj (B.obj (M, N)) ⟶ barB.obj (L₁.obj M, L₂.obj N) :=
  L₃.map (B.map (inv (adj₁.counit.app M) ×ₘ inv (adj₂.counit.app N))) ≫
    d.hom.app (L₁.obj M, L₂.obj N)

end BinaryCounitTranspose

open BinaryCounitTranspose

/-- All binary counit substitution, transpose, inverse, and naturality formulas.
Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-compatibility/fix-prop-coherence.proof.md, coefficient-comparison paragraph
(blueprint: lem-pur-binary-counit-transpose).

Proof:
1. Counit naturality and the left triangle identity give q = R(b) followed by e,
and the same equation independently for q'.
2. Unit naturality at d inverse and the right triangle identity show that the
transpose of r is d inverse.
3. Functoriality gives the first b_B formula and the factorization of B(q,q').
4. Naturality of d at (b,b') gives the second b_B factorization.
5. Map the inverses of the two input counits and the two input transposes;
reverse the three factors in step 4. This gives the claimed inverse and
invertibility of each factor.
6. Apply L₃ B to counit naturality in each coordinate. Compose with the two
inverse E maps to obtain the first naturality equation.
7. Naturality of d at (L₁ f,L₂ g), followed by step 6, gives naturality of a.
These computations allow coincident objects and identity maps. -/
theorem binaryCounitTranspose
    {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
    {C₂ : Type u₃} [Category.{v₃} C₂] {D₂ : Type u₄} [Category.{v₄} D₂]
    {C₃ : Type u₅} [Category.{v₅} C₃] {D₃ : Type u₆} [Category.{v₆} D₃]
    (R₁ : C₁ ⥤ D₁) (L₁ : D₁ ⥤ C₁) (adj₁ : R₁ ⊣ L₁)
    (R₂ : C₂ ⥤ D₂) (L₂ : D₂ ⥤ C₂) (adj₂ : R₂ ⊣ L₂)
    (R₃ : C₃ ⥤ D₃) (L₃ : D₃ ⥤ C₃) (adj₃ : R₃ ⊣ L₃)
    (B : (D₁ × D₂) ⥤ D₃) (barB : (C₁ × C₂) ⥤ C₃)
    (d : R₁.prod R₂ ⋙ B ⋙ L₃ ≅ barB) :
    (∀ (I : C₁) (J : C₂) (M : D₁) (N : D₂)
      (q : R₁.obj I ⟶ M) (q' : R₂.obj J ⟶ N),
      q = R₁.map (adj₁.homEquiv _ _ q) ≫ adj₁.counit.app M ∧
      q' = R₂.map (adj₂.homEquiv _ _ q') ≫ adj₂.counit.app N ∧
      adj₃.homEquiv _ _ (comparison adj₃ B barB d I J) = d.inv.app (I, J) ∧
      adj₃.homEquiv _ _ (comparison adj₃ B barB d I J ≫ B.map (q ×ₘ q')) =
        d.inv.app (I, J) ≫ L₃.map (B.map (q ×ₘ q')) ∧
      adj₃.homEquiv _ _ (comparison adj₃ B barB d I J ≫ B.map (q ×ₘ q')) =
        barB.map (adj₁.homEquiv _ _ q ×ₘ adj₂.homEquiv _ _ q') ≫
          d.inv.app (L₁.obj M, L₂.obj N) ≫ BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N ∧
      B.map (q ×ₘ q') =
        B.map (R₁.map (adj₁.homEquiv _ _ q) ×ₘ R₂.map (adj₂.homEquiv _ _ q')) ≫
          B.map (adj₁.counit.app M ×ₘ adj₂.counit.app N) ∧
      (∀ [IsIso (adj₁.homEquiv _ _ q)] [IsIso (adj₂.homEquiv _ _ q')]
        [IsIso (adj₁.counit.app M)] [IsIso (adj₂.counit.app N)],
        IsIso (barB.map (adj₁.homEquiv _ _ q ×ₘ adj₂.homEquiv _ _ q')) ∧
        IsIso (d.inv.app (L₁.obj M, L₂.obj N)) ∧
        IsIso (BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N) ∧
        (∀ [IsIso (BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N)],
          inverseComparison adj₁ adj₂ B L₃ barB d M N =
            inv (BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N) ≫
              d.hom.app (L₁.obj M, L₂.obj N)) ∧
        IsIso (adj₃.homEquiv _ _ (comparison adj₃ B barB d I J ≫ B.map (q ×ₘ q'))) ∧
        (∀ [IsIso (adj₃.homEquiv _ _ (comparison adj₃ B barB d I J ≫ B.map (q ×ₘ q')))],
          inv (adj₃.homEquiv _ _ (comparison adj₃ B barB d I J ≫ B.map (q ×ₘ q'))) =
            inverseComparison adj₁ adj₂ B L₃ barB d M N ≫
              barB.map (inv (adj₁.homEquiv _ _ q) ×ₘ inv (adj₂.homEquiv _ _ q'))))) ∧
    (∀ (M M' : D₁) (N N' : D₂) (f : M ⟶ M') (g : N ⟶ N')
      [IsIso (adj₁.counit.app M)] [IsIso (adj₁.counit.app M')]
      [IsIso (adj₂.counit.app N)] [IsIso (adj₂.counit.app N')],
      L₃.map (B.map (f ×ₘ g)) ≫
          L₃.map (B.map (inv (adj₁.counit.app M') ×ₘ inv (adj₂.counit.app N'))) =
        L₃.map (B.map (inv (adj₁.counit.app M) ×ₘ inv (adj₂.counit.app N))) ≫
          L₃.map (B.map (R₁.map (L₁.map f) ×ₘ R₂.map (L₂.map g))) ∧
      L₃.map (B.map (f ×ₘ g)) ≫ inverseComparison adj₁ adj₂ B L₃ barB d M' N' =
        inverseComparison adj₁ adj₂ B L₃ barB d M N ≫
          barB.map (L₁.map f ×ₘ L₂.map g)) := by
  constructor
  · intro I J M N q q'
    have hq : q = R₁.map (adj₁.homEquiv _ _ q) ≫ adj₁.counit.app M := by
      simpa only [adj₁.homEquiv_counit] using
        ((adj₁.homEquiv I M).symm_apply_apply q).symm
    have hq' : q' = R₂.map (adj₂.homEquiv _ _ q') ≫ adj₂.counit.app N := by
      simpa only [adj₂.homEquiv_counit] using
        ((adj₂.homEquiv J N).symm_apply_apply q').symm
    have hr : adj₃.homEquiv _ _ (comparison adj₃ B barB d I J) =
        d.inv.app (I, J) := by
      rw [comparison, ← adj₃.homEquiv_counit, Equiv.apply_symm_apply]
    have ht : adj₃.homEquiv _ _
        (comparison adj₃ B barB d I J ≫ B.map (q ×ₘ q')) =
        d.inv.app (I, J) ≫ L₃.map (B.map (q ×ₘ q')) := by
      rw [adj₃.homEquiv_naturality_right, hr]
    have hB : B.map (q ×ₘ q') =
        B.map (R₁.map (adj₁.homEquiv _ _ q) ×ₘ R₂.map (adj₂.homEquiv _ _ q')) ≫
          B.map (adj₁.counit.app M ×ₘ adj₂.counit.app N) := by
      rw [← B.map_comp]
      simp only [prod_comp, ← hq, ← hq']
    have ht' : adj₃.homEquiv _ _
        (comparison adj₃ B barB d I J ≫ B.map (q ×ₘ q')) =
        barB.map (adj₁.homEquiv _ _ q ×ₘ adj₂.homEquiv _ _ q') ≫
          d.inv.app (L₁.obj M, L₂.obj N) ≫
            BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N := by
      rw [ht, hB, L₃.map_comp, ← Category.assoc]
      simpa only [Category.assoc, Functor.comp_map, Functor.prod_map,
        BinaryCounitTranspose.evaluation] using
        congrArg (· ≫ BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N)
        (d.inv.naturality (adj₁.homEquiv _ _ q ×ₘ adj₂.homEquiv _ _ q')).symm
    refine ⟨hq, hq', hr, ht, ht', hB, ?_⟩
    intro hb hb' he he'
    let : IsIso (adj₁.homEquiv _ _ q ×ₘ adj₂.homEquiv _ _ q') :=
      (isIso_prod_iff _ _).2 ⟨hb, hb'⟩
    let : IsIso (adj₁.counit.app M ×ₘ adj₂.counit.app N) :=
      (isIso_prod_iff _ _).2 ⟨he, he'⟩
    have hE : IsIso (BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N) := by
      unfold BinaryCounitTranspose.evaluation
      infer_instance
    have hEinv : ∀ [IsIso (BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N)],
        inverseComparison adj₁ adj₂ B L₃ barB d M N =
          inv (BinaryCounitTranspose.evaluation adj₁ adj₂ B L₃ M N) ≫
            d.hom.app (L₁.obj M, L₂.obj N) := by
      intro _
      unfold inverseComparison
      congr 1
      apply IsIso.eq_inv_of_hom_inv_id
      simp only [BinaryCounitTranspose.evaluation, ← L₃.map_comp, ← B.map_comp,
        prod_comp, IsIso.hom_inv_id, ← prod_id,
        B.map_id, L₃.map_id]
      rfl
    have htiso : IsIso (adj₃.homEquiv _ _
        (comparison adj₃ B barB d I J ≫ B.map (q ×ₘ q'))) := by
      rw [ht']
      infer_instance
    refine ⟨inferInstance, inferInstance, hE, hEinv, htiso, ?_⟩
    intro _
    apply IsIso.inv_eq_of_hom_inv_id
    rw [ht', hEinv]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
      ← barB.map_comp, prod_comp, IsIso.hom_inv_id, ← prod_id, barB.map_id]
  · intro M M' N N' f g he he' hn hn'
    have hf : f ≫ inv (adj₁.counit.app M') =
        inv (adj₁.counit.app M) ≫ R₁.map (L₁.map f) := by
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact (adj₁.counit.naturality f).symm
    have hg : g ≫ inv (adj₂.counit.app N') =
        inv (adj₂.counit.app N) ≫ R₂.map (L₂.map g) := by
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact (adj₂.counit.naturality g).symm
    have hnat : L₃.map (B.map (f ×ₘ g)) ≫
        L₃.map (B.map (inv (adj₁.counit.app M') ×ₘ inv (adj₂.counit.app N'))) =
        L₃.map (B.map (inv (adj₁.counit.app M) ×ₘ inv (adj₂.counit.app N))) ≫
          L₃.map (B.map (R₁.map (L₁.map f) ×ₘ R₂.map (L₂.map g))) := by
      simp only [← L₃.map_comp, ← B.map_comp, prod_comp,
        hf, hg]
    refine ⟨hnat, ?_⟩
    unfold inverseComparison
    rw [← Category.assoc, hnat, Category.assoc]
    simpa only [Category.assoc, Functor.comp_map, Functor.prod_map,
        BinaryCounitTranspose.evaluation] using congrArg
      (L₃.map (B.map (inv (adj₁.counit.app M) ×ₘ inv (adj₂.counit.app N))) ≫ ·)
      (d.hom.naturality (L₁.map f ×ₘ L₂.map g))

end CategoryTheory
