module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Descent of separatedness to an affine stage

Source: Stacks Project, spaces-limits.tex, Tag 0851 (lemma-descend-separated-morphism),
in Situation 084W; spaces-morphisms.tex, Tag 03KL (lemma-base-change-separated)
(blueprint: lem-sfb-space-descend-separated).

Schemes are considered over Spec Z. Base changes are the actual presheaf pullbacks;
separatedness tests their relative diagonals on schemes. The atlas predicate for
quasi-compactness is the existing affine-test formulation of the universal
algebraic-space test convention (Stacks Tag 03KG).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finitely presented space over an affine stage is separated at every sufficiently
late stage if its base change to the limit is separated.
Source: Stacks Project, spaces-limits.tex, Tags 084W and 0851;
spaces-morphisms.tex, Tag 03KL (blueprint: lem-sfb-space-descend-separated).

Proof:
1. Put D₀ = X₀ ×_{T₀} X₀. The affine base T₀ is qcqs by
   [lem-weil-pbc-affine-scheme-qcqs]. Its identity is a quasi-compact scheme atlas;
   its absolute diagonal is the closed immersion induced by multiplication of rings.
   Base changing this diagonal to a quasi-compact atlas, using
   [lem-weil-pbc-closed-immersion-base-change] and
   [lem-trf-space-fibre-products-etale-covers], verifies absolute quasi-separatedness
   as a space. Finite presentation and [lem-sfb-space-qcqs-source-products] then
   make X₀ and D₀ qcqs. By [lem-sfb-space-diagonal-locally-finite-type], the relative
   diagonal δ₀ : X₀ → D₀ is representable and locally of finite type.
2. For any T₀-space B, the sheaf pullback identification sends ((x₁,x₂),b) to
   ((x₁,b),(x₂,b)); its inverse forgets the repeated b. It identifies the base
   change of δ₀ with the relative diagonal over B. At the limit that diagonal
   is a closed immersion by the separatedness hypothesis.
3. Apply [lem-sfb-space-descend-closed-immersion] to δ₀ over the tail starting at i₀.
   Its source and target are qcqs and it is locally of finite type by step 1.
   Its limit base change is closed by step 2, so it is closed at some i ≥ i₀.
   Step 2 identifies that map with the diagonal of fᵢ, hence fᵢ is separated.
4. For every j ≥ i, pullback transitivity identifies fⱼ with the base change of fᵢ.
   The arbitrary base-change clause of [lem-sfb-space-separated-fp-composition]
   makes fⱼ separated. No transition map is required to be surjective. -/
theorem eventually_separated_of_affine_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    (haff : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (c : Cone D)
    (hc : IsLimit ((Over.forget (Spec (.of (ULift.{u} ℤ)))).mapCone c))
    (i₀ : I) (X₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f₀ : X₀.obj.obj ⟶ yoneda.obj (D.obj (op i₀)))
    (hfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X₀ (D.obj (op i₀)) f₀ ∧
      IsQuasiCompactPresheafMap f₀ ∧
      IsQuasiCompactPresheafMap (pullback.diagonal f₀))
    (hsep : IsSeparatedPresheafMap
      (pullback.snd f₀ (yoneda.map (c.π.app (op i₀))))) :
    ∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hj : i ≤ j),
      IsSeparatedPresheafMap
        (pullback.snd f₀ (yoneda.map (D.map (homOfLE (le_trans hi hj)).op))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
