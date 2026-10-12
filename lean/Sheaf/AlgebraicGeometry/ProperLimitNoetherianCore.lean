module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Core inverse-system construction for a proper morphism.
Source: Stacks limits.tex, Tag 0A0P, proof steps 1--8.
(blueprint: lem-weil-pbc-proper-limit-noetherian-core)
The construction descends a proper finitely presented envelope, forms scheme-theoretic
images, and verifies the two limit cones, affine transitions, proper stage maps, and
finite-type base stages. -/
theorem exists_proper_limit_noetherian_core
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
      (πX : (Functor.const Λᵒᵖ).obj X ⟶ Xs)
      (πS : (Functor.const Λᵒᵖ).obj S ⟶ Ss),
      Nonempty (IsLimit (Cone.mk X πX)) ∧ Nonempty (IsLimit (Cone.mk S πS)) ∧
      (∀ (i j : Λᵒᵖ) (a : i ⟶ j),
        IsAffineHom (Xs.map a) ∧ IsAffineHom (Ss.map a)) ∧
      (∀ i : Λᵒᵖ, IsProper (fs.app i)) ∧
      (∀ i : Λᵒᵖ,
        LocallyOfFiniteType (specULiftZIsTerminal.from (Ss.obj i)) ∧
          QuasiCompact (specULiftZIsTerminal.from (Ss.obj i))) ∧
      (∀ i : Λᵒᵖ, πX.app i ≫ fs.app i = f ≫ πS.app i) := by
  sorry

/-- Affine-base refinement of the core inverse-system construction.
Source: Stacks limits.tex, Tag 0A0P, affine clause of the proof.
(blueprint: lem-weil-pbc-proper-limit-noetherian-affine-clause)
For a core system over an affine base, the stages are affine finite-type schemes and
the global-section cocone is a colimit. -/
theorem proper_limit_noetherian_affine_clause
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S]
    (hS : IsAffine S)
    (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
    (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
    (πX : (Functor.const Λᵒᵖ).obj X ⟶ Xs)
    (πS : (Functor.const Λᵒᵖ).obj S ⟶ Ss)
    (hlimX : Nonempty (IsLimit (Cone.mk X πX)))
    (hlimS : Nonempty (IsLimit (Cone.mk S πS))) :
    (∀ i : Λᵒᵖ, IsAffine (Ss.obj i) ∧
      RingHom.FiniteType (algebraMap ℤ (Scheme.Γ.obj (Opposite.op (Ss.obj i))))) ∧
      Nonempty (IsColimit (Scheme.Γ.mapCocone (Cone.mk S πS).op)) := by
  sorry

end AlgebraicGeometry
