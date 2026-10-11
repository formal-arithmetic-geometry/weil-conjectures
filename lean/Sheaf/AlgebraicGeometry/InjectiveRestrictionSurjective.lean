module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Injective sheaves have surjective restriction maps

Source: Stacks Project, Cohomology, Lemma 01EA
(blueprint: lem-sc-ringed-space-injective-restriction-surjective).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

noncomputable section
namespace AlgebraicGeometry

/-- Injective sheaves of modules have surjective restriction maps on sections.
Source: Stacks Project, Cohomology, Lemma 01EA
(blueprint: lem-sc-ringed-space-injective-restriction-surjective).
Proof: let `j_!O_U` be the module sheafification of the presheaf equal to `O_X` on opens
inside `U` and `0` elsewhere (def-weil-presheaf-modules-sheafification); its universal
property gives `Hom(j_!O_U, F) ≅ F(U)`, `ψ ↦ ψ(1)`, and likewise for `U'`. The map
`α : j'_!O_{U'} ⟶ j_!O_U` induced by the identity on opens inside `U'` is injective on every
stalk, hence a monomorphism. As `I` is injective, precomposition with `α` is surjective, and
under the bijections it is the restriction `I(U) → I(U')`. For the second clause, given
`c ∈ I(V ⊓ W)` lift it to `a ∈ I(V)` along `V ⊓ W ≤ V` and take `b = 0`; then
`(a, b) ↦ c`.
-/
theorem injective_restriction_surjective (X : RingedSpace.{u})
    {U' U : Opens X} (hU : U' ≤ U)
    (I : SheafOfModules.{u} (moduleRings X))
    [Injective I] :
    Function.Surjective (fun s : I.val.obj (Opposite.op U) =>
      (I.val.map (homOfLE hU).op).hom s) ∧
      ∀ (V W : Opens X), Function.Surjective
        (fun p : I.val.obj (Opposite.op V) × I.val.obj (Opposite.op W) =>
          (show I.val.obj (Opposite.op (V ⊓ W)) from
            (I.val.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op).hom p.1) -
          (show I.val.obj (Opposite.op (V ⊓ W)) from
            (I.val.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op).hom p.2)) := by
  sorry

end AlgebraicGeometry
