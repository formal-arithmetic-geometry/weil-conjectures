# WeilConjectures.CoefQbarVerdier.finite_exceptional_formula_scalar

## Reason

The old `finite_exceptional_formula_scalar` quantified over arbitrary
`FiniteExceptionalFormulaCore`. Its finite identifications can be changed independently
at different fields, carrying along their transported adjunctions. Neither `normalized`
nor the comparison's unit/counit formulas identify those adjunctions with the
trace-normalized dual-formula adjunctions. The old universal assertion is therefore not
justified; T2 already marked this exact defect `STATEMENT-DISPUTED`. On the identity
map of a point, scaling one stage comparison by 2 and another by 1, and transporting
their adjunctions, exhibits the missing constraint in characteristic zero.

The repaired scalar theorem adds a hypothesis that every `t.finite E` adjunction satisfies
`RationalOperations.DualFormulaAdjunctionNormalized`. This is the existing trace/evaluation
normalization, not an assumption of the desired scalar square. The theorem now proves the
finite comparison square by the rational scalar-counit theorem and injectivity of the
adjunction transpose. It combines this finite square with the separate dual-formula
inclusion calculation.

A new, proved theorem `finite_exceptional_normalized_core` constructs cores with this
normalization from the old core existence theorem and the one-field normalized-adjunction
existence theorem. It replaces each comparison by right-adjoint uniqueness and conjugates
the old common-stage comparison by the new comparison followed by the inverse old one.
No definition is built from an arbitrary unproved existence witness: this construction
occurs within the proof of an existential theorem. No scalar square is assumed in it.

## Old

```lean
theorem finite_exceptional_formula_scalar
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (t : FiniteExceptionalFormulaCore D l hl Ω X f BX BY c S) :
    ∀ (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E),
      (inclusion L).map ((finiteRightScalar D l hl Ω X f c S E L h).hom.app M) ≫
        (t.comparison L).hom.app ((transition l Ω Y E L h).obj M) =
      (inclusionTransition l Ω X E L h).hom.app
          ((finiteRight D l hl Ω X f c S E).obj M) ≫
        (t.comparison E).hom.app M ≫
        (specifiedExceptionalFormulaCore D l hl Ω X f BX BY).map
          ((inclusionTransition l Ω Y E L h).inv.app M)
```

## New

```lean
theorem finite_exceptional_formula_scalar
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (t : FiniteExceptionalFormulaCore D l hl Ω X f BX BY c S)
    (ht : ∀ E : Index l Ω,
      RationalOperations.DualFormulaAdjunctionNormalized D l hl X c (fieldStage l Ω E)
        (BX.finite.omega E) (BY.finite.omega E) (BX.finite.datum E) (BY.finite.datum E)
        (t.finite E).adjunction) :
    ∀ (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E),
      (inclusion L).map ((finiteRightScalar D l hl Ω X f c S E L h).hom.app M) ≫
        (t.comparison L).hom.app ((transition l Ω Y E L h).obj M) =
      (inclusionTransition l Ω X E L h).hom.app
          ((finiteRight D l hl Ω X f c S E).obj M) ≫
        (t.comparison E).hom.app M ≫
        (specifiedExceptionalFormulaCore D l hl Ω X f BX BY).map
          ((inclusionTransition l Ω Y E L h).inv.app M)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar | U7 | Added trace normalization hypothesis; proved repaired scalar equation. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula | unclaimed | Proof constructs normalized core; statement unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierExceptional | unclaimed | Unchanged direct consumer of the parent; compile checked. |

The declaration-use search finds only the scalar module itself and its parent formula.
The transitive import closure has 120 modules; their statements see the unchanged parent
interface.

Consumer details:

- `Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar`: assigned to U7. Repaired theorem
  signature; proof supplied. Its new public import is required by the normalization
  predicate in that signature.
- `Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula`: unclaimed on the server when
  checked. The sole direct importer/caller of the scalar theorem. Its theorem and all
  public declarations keep their signatures and definitions verbatim. Its proof obtains
  a normalized core from the new construction and passes the normalization explicitly.
  The theorem docstring now describes this construction. The original scalar field
  assignment lacks the extra normalization argument.
- `Sheaf.SixFunctors.CoefQbarVerdierExceptional`: direct importer of the parent formula
  module. Its finite comparison input and parent theorem statement are unchanged; no
  source adaptation is needed.
- `Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore`: held by X3 on the server. Untouched,
  including its structure, theorem signature, proof and node. The new construction uses
  its existing interface. There is no strengthening of the other group's record.

The scalar node's only DAG citer is the parent finite-formula node, whose proof dependency
on core existence is replaced by normalized-core existence. The parent statement stays
identical. The nodes of both new modules carry the exact Lean statements and their proof
steps. No Challenge declaration, common-stage duality definition, coefficient category,
exceptional system or source-library declaration is changed.

The single new hole is `dual_formula_inclusion_scalar`, strictly the component-pasting
part of the old argument. It mentions no exceptional functor, compactification, system,
finite exceptional comparison, or core. The finite exceptional scalar-mate argument and
the construction of the required normalized family are proved in this packet.

## Status

landed 20261028T072455-L-1952792 2026-10-28 (merge of deliver/U7/Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar)
