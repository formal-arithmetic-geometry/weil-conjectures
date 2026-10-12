module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! The proper finitely presented closed envelope clause of Lemma 09ZR.
(blueprint: lem-weil-pbc-proper-closed-in-proper-fp-envelope-part)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A proper scheme over a qcqs base embeds as a closed subscheme of a proper
finitely presented scheme over that base.

Source: Stacks Project, Limits, Lemma 09ZR
(blueprint: lem-weil-pbc-proper-closed-in-proper-fp-envelope-part).

Proof:
1. Properness gives finite type and separatedness. By
   prop-nagata-finite-type-closed-in-fp (01ZJ), embed X into a separated finitely
   presented S-scheme Y. Both X and Y are qcqs by
   lem-weil-pbc-qcqs-morphism-permanence.
2. Apply lem-weil-pbc-chow-finite-type (0202) to Y: obtain a proper surjective
   Y' → Y and an immersion Y' → projective space over S. The latter space is proper
   over S by lemma-nagata-projective-space-base-change-proper.
3. By lemma-nagata-closed-subscheme-fp-system (09ZP), express X as the inverse limit
   of the closed subschemes Xᵢ of Y defined by finite-type subideals of its ideal.
   Zero and sums make this a nonempty directed set. Every Xᵢ is finitely presented
   over S by lem-weil-pbc-proper-fp-permanence, and all transitions and projections
   are closed immersions. They are affine by lem-weil-pbc-closed-immersion-finite,
   so this is the limit of lem-weil-pbc-limit-affine-transition.
4. Pull back Xᵢ and X to Y', obtaining X'ᵢ and X'. Base change preserves closed
   immersions by lem-weil-pbc-proper-fp-permanence. Limits of sets commute with
   fibre products; directedness makes the constant factors stay constant. Thus
   the compatible maps X' → X'ᵢ form a limiting cone by Yoneda.
5. The scheme X' is proper over S by base change and composition. Its immersion
   into projective space is proper by lem-weil-pbc-proper-over-separated and hence
   closed by lem-weil-pbc-proper-immersion-closed.
6. Apply lem-weil-pbc-eventually-closed-immersion (0A0N) to X'ᵢ in projective space.
   The needed qcqs and finite-type properties follow from steps 1–4 and
   lem-weil-pbc-qcqs-morphism-permanence. From some stage onward these immersions
   are closed; closure under composition is lem-weil-pbc-closed-immersion-comp.
7. These X'ᵢ are proper over S. Their maps onto Xᵢ are surjective by
   lem-weil-pbc-surjective-base-change. By lem-weil-pbc-image-universally-closed
   (03GN), Xᵢ is universally closed over S. Its separatedness and finite type from
   step 3 therefore make it proper.
8. Choose a stage at or beyond the bound from step 6. Step 7 makes its structure
   map proper. Step 3 makes it finitely presented and gives a closed immersion
   from X, whose composition with the structure map is f. This is the envelope. -/
theorem exists_proper_finitePresentation_closedImmersion_envelope
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ S),
      IsClosedImmersion i ∧ IsProper g ∧ LocallyOfFinitePresentation g ∧
        QuasiCompact g ∧ QuasiSeparated g ∧ i ≫ g = f := by
  sorry

end AlgebraicGeometry
