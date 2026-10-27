module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-! # Descent of the support of local open representatives

Source: literature/stacks-project/spaces-descent.tex, Tag 041X, support argument;
literature/stacks-project/descent.tex, Tag 03N0.
(blueprint: lem-trf-local-open-representatives-support-descent)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- The open representatives of an arbitrary presheaf on an etale covering agree on
all overlaps and descend to a unique open subscheme of the base.

Source: literature/stacks-project/spaces-descent.tex, Tag 041X, support argument,
and literature/stacks-project/descent.tex, Tag 03N0.
(blueprint: lem-trf-local-open-representatives-support-descent)

Proof:
1. For i,j put R = T_i ×_T T_j. Base change of open immersions
   (lem-weil-pbc-open-immersion-base-change) identifies the two inverse-image opens
   A and B with their open subschemes of R, using def-pc-fibre-product and
   def-weil-open-immersion.
2. Evaluate alpha_i on the projection A -> W_i to obtain an element of F(A -> T).
   Its inverse image under alpha_j gives a T_j-morphism A -> W_j. The fibre-product
   universal property factors A -> R through B, proving A is contained in B.
   Interchanging i and j proves equality. The two maps R -> T agree, so these
   evaluations use the same value of F. No compatibility or sheaf axiom is needed.
3. Each q_i is flat and locally of finite presentation by def-weil-etale-morphism;
   joint surjectivity makes this an fppf covering (def-pc-fppf-site).
   Apply lem-trf-fppf-covering-is-fpqc to the same set-indexed family.
4. Apply lem-weil-pbc-open-subscheme-fpqc-descent to the compatible opens from
   step 2 to obtain the unique descended open. This includes the empty cover
   of the empty scheme.
-/
theorem localOpenRepresentatives_support_descent
    {T : Scheme.{u}} (F : (Over T)ᵒᵖ ⥤ Type (max u w))
    {I : Type v} {T' : I → Scheme.{u}} (q : ∀ i, T' i ⟶ T)
    [∀ i, Etale (q i)]
    (hq : ∀ t : T, ∃ (i : I) (x : T' i), q i x = t)
    (W : ∀ i, (T' i).Opens)
    (α : ∀ i, uliftYoneda.{w}.obj (Over.mk (W i).ι) ≅ (Over.map (q i)).op ⋙ F) :
    (∀ i j : I, (pullback.fst (q i) (q j) ⁻¹ᵁ W i) =
      (pullback.snd (q i) (q j) ⁻¹ᵁ W j)) ∧
    (∃! U : T.Opens, ∀ i, (q i ⁻¹ᵁ U) = W i) := by
  have hle {R : Scheme.{u}} (i j : I) (a : R ⟶ T' i) (b : R ⟶ T' j)
      (hab : a ≫ q i = b ≫ q j) : a ⁻¹ᵁ W i ≤ b ⁻¹ᵁ W j := by
    let A := a ⁻¹ᵁ W i
    let f : A.toScheme ⟶ (W i).toScheme :=
      IsOpenImmersion.lift (W i).ι (A.ι ≫ a) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨x, rfl⟩
        exact x.property)
    let f' : Over.mk (A.ι ≫ a) ⟶ Over.mk (W i).ι :=
      Over.homMk f (IsOpenImmersion.lift_fac _ _ _)
    have hcomp : (A.ι ≫ a) ≫ q i = (A.ι ≫ b) ≫ q j := by
      simp only [Category.assoc, hab]
    have s : F.obj (Opposite.op (Over.mk ((A.ι ≫ b) ≫ q j))) := by
      rw [← hcomp]
      exact (α i).hom.app (Opposite.op (Over.mk (A.ι ≫ a))) ⟨f'⟩
    let g : Over.mk (A.ι ≫ b) ⟶ Over.mk (W j).ι :=
      ((α j).inv.app (Opposite.op (Over.mk (A.ι ≫ b))) s).down
    intro x hx
    have hg := congrArg (fun k : A.toScheme ⟶ T' j ↦ k ⟨x, hx⟩) (Over.w g)
    change (W j).ι (g.left ⟨x, hx⟩) = b x at hg
    change b x ∈ W j
    rw [← hg]
    exact (g.left ⟨x, hx⟩).property
  have hW : ∀ i j : I, (pullback.fst (q i) (q j) ⁻¹ᵁ W i) =
      (pullback.snd (q i) (q j) ⁻¹ᵁ W j) := by
    intro i j
    apply le_antisymm
    · exact hle i j _ _ pullback.condition
    · exact hle j i _ _ pullback.condition.symm
  refine ⟨hW, openSubscheme_existsUnique_of_fpqc q ?_ W hW⟩
  apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨hq, fun i ↦ ⟨inferInstance, inferInstance⟩⟩

end AlgebraicGeometry
