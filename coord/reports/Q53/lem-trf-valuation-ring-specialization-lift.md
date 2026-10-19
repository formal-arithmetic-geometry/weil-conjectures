## Worker report

This is an existing-declaration delivery.  The node is stated exactly by
`AlgebraicGeometry.Scheme.exists_valuationSubring_of_specializes` in
`WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion`, at lines 218--235.
The declaration is already proved in the published slopmaster2 source, so this
packet adds no Lean module and introduces no duplicate declaration.  The copied
node changes only its `lean` record to `existing: true`, with the exact Lean
signature, source module, declaration, branch, date, and a note explaining the
match.  There is no statement correction, new definition node, dependency
module, or `STATEMENT-DISPUTED` issue.

I read the complete item node and the complete source declaration and docstring.
The declaration's signature is:

`lemma Scheme.exists_valuationSubring_of_specializes {Y : Scheme.{u}} {y' y : Y} (h : y' ⤳ y) :`
`    ∃ (A : ValuationSubring (AlgebraicClosure (Y.residueField y'))) (ρ : Spec (.of A) ⟶ Y),`
`      ρ (closedPoint A) = y ∧`
`      Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (Y.residueField y')))) ≫ ρ =`
`        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y')`
`          (AlgebraicClosure (Y.residueField y')))) ≫ Y.fromSpecResidueField y'`

Hypothesis and clause correspondence:

- The scheme `Y` is the explicit `{Y : Scheme.{u}}` binder, and points `y'` and
  `y` are the explicit elements of its carrier.  The hypothesis `h : y' ⤳ y`
  is exactly the stated specialization relation.
- The existential witness `A` is
  `ValuationSubring (AlgebraicClosure (Y.residueField y'))`.  A valuation
  subring is the valuation ring inside the displayed algebraic closure; its
  ambient fraction field is therefore the fixed `AlgebraicClosure` of the
  residue field `Y.residueField y'`.
- The existential witness `ρ : Spec (.of A) ⟶ Y` is the required scheme
  morphism from the spectrum of the valuation ring.
- `ρ (closedPoint A) = y` is exactly the closed-point clause.
- The final equality is the generic-point restriction clause.  Its left side
  is `Spec.map (algebraMap A (AlgebraicClosure ...)) ≫ ρ`, the map from the
  spectrum of the fraction-field algebraic closure through the valuation
  ring.  Its right side is `Spec.map (algebraMap (Y.residueField y')
  (AlgebraicClosure ...)) ≫ Y.fromSpecResidueField y'`, the canonical map
  `Spec κ(y')` followed by the residue-field point map.  The contravariance of
  `Spec.map` gives the arrows in exactly this order.

The dependency declarations read and used are:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`
  from `Mathlib.AlgebraicGeometry.Scheme`.  The structure extends a locally
  ringed space and its `Hom` is the scheme morphism used by `ρ`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` from
  `Mathlib.AlgebraicGeometry.ResidueField`.  Its full definition is the local
  ring's `IsLocalRing.ResidueField`, with a `Field` instance; this renders
  `κ(y')` as `Y.residueField y'`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`.  `Spec (.of A)` and both displayed
  contravariant spectrum maps use these declarations.
- `def-weil-algebraic-closure`: Mathlib's `AlgebraicClosure` from
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`; its `IsAlgClosure`
  interface is the recorded `IsAlgClosure` class in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`.  The declaration specializes it to
  `AlgebraicClosure (Y.residueField y')`.

Edge cases checked: `y' = y` is allowed (the specialization relation is not
required to be strict); a field residue ring gives the expected one-point
spectrum; the valuation ring may equal its fraction field when the specialization
is trivial; and the statement imposes no Noetherian, finite-type, separated,
or characteristic hypothesis.  Empty schemes cause no vacuous witness because
`y'` and `y` are explicit points.  The algebraic closure is the canonical
Mathlib construction, while the valuation subring and morphism remain the
existential data supplied by the source theorem.

Searches performed:

- `msearch.py Q53 lem-trf-valuation-ring-specialization-lift leanfinder` for
  “valuation ring realizes specialization of scheme points with algebraic
  closure fraction field”: eight hits (including valuative-criterion
  `SpecializingMap` results), but no exact theorem.
- `msearch.py ... loogle` for
  `Scheme.exists_valuationSubring_of_specializes, ValuationSubring,
  AlgebraicClosure`: zero hits; the project-specific identifier is unknown to
  the Mathlib search service.
- `msearch.py ... grep` for
  `exists_valuationSubring_of_specializes|valuationSubring_of_specializes`
  in `AlgebraicGeometry`: zero Mathlib hits.
- The node's recorded LeanSearch search likewise returned only general
  `SpecializingMap` and stalk-specialization declarations, with no exact match.
- Direct `rg`/`grep` over the source and `lean/Sheaf` found no duplicate outside
  `WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion`; the complete
  source declaration was confirmed with `scompile.py --source`.

## Second reading by Q53

I reread the copied node and the recorded signature after writing the record.
The binder `h : y' ⤳ y`, the valuation-subring/algebraic-closure witness, the
morphism `ρ`, the closed-point equality, and the generic restriction equality
all occur verbatim.  The dependency names resolve to the declarations listed
above, and every edge case remains represented.  Since the published theorem
already has the exact statement and is sorry-free, no source file or additional
change is needed.
