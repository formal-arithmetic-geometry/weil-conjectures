module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.DescendClosedImmersion

/-!
# Descent of a fixed Chow diagram

Source: Stacks Project, Limits, Tag 081F, the base-changed Chow diagram and Tag 01ZP.
(blueprint: lem-weil-pbc-closed-chow-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A given Chow immersion at a separated stage is closed at a later stage.
The source at that later stage is the base change of the given Chow modification,
not an arbitrary witness for properness of the original morphism.

Source: Stacks Project, Limits, Tag 081F, proof after choosing the Chow diagram;
Tag 01ZP for descent of the closed immersion.
(blueprint: lem-weil-pbc-closed-chow-stage).

Proof:
1. Restrict the directed system to indices above i₁. This subsystem has the same limit:
   every index has a common upper bound with i₁, so compatible cones extend uniquely.
   Affine transitions make its base at i₁ and the base-changed X₀ and Y₀ qcqs.
   Pasting pullback squares identifies the pullback of f₁ to the limit with that of f₀.
2. Base change the given π₁ and j₁ to the limit. The former remains proper and surjective,
   and the latter remains an immersion. The composite π ≫ f is proper by composition.
   Projective space is proper, hence separated, over the limit target. The commutative
   triangle therefore makes j proper (properness over a separated target), and a proper
   immersion is a closed immersion.
3. At i₁, T₁ is qcqs because it is proper over the qcqs source. Projective space is qcqs
   because it is proper over the qcqs target. The immersion j₁ is locally of finite type.
   Apply exists_isClosedImmersion_stage_of_locallyOfFiniteType to j₁ over Sᵢ₁ and the
   restricted system. It yields an index i above i₁ with jᵢ a closed immersion.
4. The pullback of T₁ over Sᵢ₁ is the source displayed below. Pasting squares and the
   projective-space base-change isomorphism give π and j with the displayed triangle.
   Surjectivity of π follows from base change and transport by the source comparison
   isomorphism. Separatedness of fᵢ follows from that of f₁ by the same comparison.
   The transition Sᵢ → Sᵢ₀ is Sᵢ → Sᵢ₁ → Sᵢ₀ by functoriality. -/
theorem exists_closed_chow_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left]
    (hf : IsProper (((Over.pullback (c.π.app (op i₀))).map f₀).left))
    (i₁ : I) (h₁ : i₀ ≤ i₁)
    (hsep : IsSeparated (((Over.pullback (D.map (homOfLE h₁).op)).map f₀).left))
    (n : ℕ) (T₁ : Scheme.{u})
    (π₁ : T₁ ⟶ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).left)
    (j₁ : T₁ ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1)))
      ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left)
    (hπ₁ : IsProper π₁) (hsurj₁ : Surjective π₁) (hj₁ : IsImmersion j₁)
    (hw₁ : j₁ ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1)))
      ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left ↘
        ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left =
      π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).map f₀).left) :
    ∃ (i : I) (h₁i : i₁ ≤ i)
      (π : pullback (π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).hom)
          (D.map (homOfLE h₁i).op) ⟶
        ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj X₀).left)
      (j : pullback (π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).hom)
          (D.map (homOfLE h₁i).op) ⟶
        ProjectiveSpace (ULift.{u} (Fin (n + 1)))
          ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left),
      Surjective π ∧ IsClosedImmersion j ∧
        j ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1)))
          ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left ↘
            ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left =
          π ≫ ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).map f₀).left ∧
        IsSeparated (((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).map f₀).left) := by
  sorry

end AlgebraicGeometry
