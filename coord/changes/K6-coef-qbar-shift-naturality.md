# WeilConjectures.CoefQbarVerdier.descended_shift_core

## Reason

The previous statement allowed an arbitrary family of exact finite shift structures.
That hypothesis supplies no compatibility with the specified coefficient-extension
beta maps. The proof plan instead chooses the internal-Hom shifts canonically.

The defect is already visible for X = Spec(D.k), allowed because D.k is the fixed
algebraic closure and X has its identity structure map. Its finite rational categories
are bounded derived categories of finite-dimensional vector spaces, so all triangles
are split. Multiplying a canonical degree-n shift comparison by a^n, for a nonzero
coefficient scalar a, preserves the zero and addition laws and exactness. Choose a=1
at one finite field and a=2 at a strict extension. The normalized scalar-extension
comparison does not commute with these shifts. Its square on the dual of the unit
would identify the distinct nonzero scalar multiples 1 and 2 after faithful scalar
extension. Thus a single natural common-stage shift cannot restrict to both choices.
This is the reason for the STATEMENT-DISPUTED annotation of the old premise.

The corrected theorem assumes naturality of the explicitly constructed components,
then proves global zero/addition coherence and finite-comparison compatibility.
The caller keeps its complete original conclusion: it chooses finite shifts with
this naturality, using the separate finite internal-Hom normalization theorem.

## Old

```lean
theorem descended_shift_core (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (F.datum E).dual.CommShift ℤ)
    (htri : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      letI := t E
      (F.datum E).dual.IsTriangulated) :
    ∃ s : (descendedDual D l hl Ω X F hF).CommShift ℤ,
      letI := s
      ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
        letI := t E
          let J := GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E
          let jshift : J.CommShift ℤ :=
            GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
          let oshift : J.op.CommShift ℤ :=
            @Pretriangulated.Opposite.commShiftFunctorOpInt _ _ _ _ _ _ J jshift
          let cA : ((F.datum E).dual ⋙ J).CommShift ℤ :=
            @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual J ℤ _ _ _ _ (t E) jshift
          let cB : (J.op ⋙ descendedDual D l hl Ω X F hF).CommShift ℤ :=
            @Functor.CommShift.comp _ _ _ _ _ _ J.op
              (descendedDual D l hl Ω X F hF) ℤ _ _ _ _ oshift s
          @NatTrans.CommShift _ _ _ _ _ _
            (descendedComparison D l hl Ω X F hF E).hom ℤ _ _ _ cA cB
```

## New

```lean
theorem descended_shift_core (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      (F.datum E).dual.CommShift ℤ)
    (hnat : ∀ (n : ℤ)
      (P Q : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ) (f : P ⟶ Q),
      (descendedDual D l hl Ω X F hF).map (f⟦n⟧') ≫
        (shiftComponent D l hl Ω X F hF t n Q).hom =
      (shiftComponent D l hl Ω X F hF t n P).hom ≫
        ((descendedDual D l hl Ω X F hF).map f)⟦n⟧') :
    ∃ s : (descendedDual D l hl Ω X F hF).CommShift ℤ,
      letI := s
      ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
        letI := t E
          let J := GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E
          let jshift : J.CommShift ℤ :=
            GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E
          let oshift : J.op.CommShift ℤ :=
            @Pretriangulated.Opposite.commShiftFunctorOpInt _ _ _ _ _ _ J jshift
          let cA : ((F.datum E).dual ⋙ J).CommShift ℤ :=
            @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual J ℤ _ _ _ _ (t E) jshift
          let cB : (J.op ⋙ descendedDual D l hl Ω X F hF).CommShift ℤ :=
            @Functor.CommShift.comp _ _ _ _ _ _ J.op
              (descendedDual D l hl Ω X F hF) ℤ _ _ _ _ oshift s
          @NatTrans.CommShift _ _ _ _ _ _
            (descendedComparison D l hl Ω X F hF E).hom ℤ _ _ _ cA cB
```

The new module `Sheaf.SixFunctors.CoefQbarVerdierShiftComponents` constructs
`finiteRestrictionShift` by `Functor.CommShift.ofIso` and `shiftComponent` by
cancelling the opposite inclusion comparison. These are concrete constructions. The new finiteRestrictionShift is irreducible;
its proved finiteRestrictionShift_compatibility lemma supplies its compatibility API.
The proved generic assembly is in the new ShiftDescentAssembly module.
Its theorem `finite_shift_naturality` states the remaining finite exact shift
choice and arrow-naturality calculation. It asserts no global coherent shift.

`Sheaf.SixFunctors.CoefQbarVerdierShift` now obtains the compatible family from
that theorem and passes its naturality to the corrected core. Its theorem signature
and every target statement are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.CoefQbarVerdierShift | unclaimed | The only direct importer and declaration caller. Replace the arbitrary exactness choices by the normalized finite family; statement and visibility unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierExactness | unclaimed | Indirect importer; its use of descended_shift_compatibility has the identical signature. |

## Status

landed 20261028T072427-L-1945773 2026-10-28 (merge of deliver/K6/Sheaf.SixFunctors.CoefQbarVerdierShiftCore)
