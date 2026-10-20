## What changed

The proof of `AlgebraicGeometry.exists_open_geometricallyIrreducible_linearSystemMember`
now constructs the required open from the universal incidence projection, applies generic
geometric-irreducibility shrinking, factors an arbitrary field point through its residue
field, and transports geometric irreducibility through the resulting pullback square.
The theorem signature, original public imports and `linearSystemMemberIdeal` definition
are verbatim unchanged. No existing definition or statement was changed, and no downstream
adaptation is required. The static gate requires a record for the added local irreducibility
commands: `coord/changes/C8-bertini-irreducible-proof-attributes.md`. It documents their local
scope and the absence of current Lean importers; the public interface remains unchanged.

`BertiniUniversalBaseChange` proves a public zero-ideal pullback formula for arbitrary scheme
maps, using uniqueness of tensor-pullback adjoints and compatibility of zero loci. Private
helpers in the item identify this formula with the original chosen-unit definition and
compare the Fin coordinates with the ULift coordinates required by the family API.

`BertiniAffineFunctionField` proves the algebraic part of the argument from the existing
independent-functions and field-extension theorems, including the actual finite-index
reindexing and finite generation of the fraction field. `BertiniUniversalGenericFibre`
combines it with the generic-residue-field criterion and the separate geometric chart
presentation. `BertiniIncidenceElimination` proves the polynomial quotient isomorphism with
its substitution formula. `IrreducibleDominantGenericFibre` proves the generic-fibre
irreducibility step directly from dominance and the source generic point.

`FibreResidueArrow` identifies the generic-fibre residue-field arrow with the source
residue-field map using the fibre inclusion's residue-field isomorphism.
`BertiniTrivializedZeroIdeal` proves the local coefficient ideal formula for the prescribed
tensor unit. `BertiniAffineAmbient` proves the canonical polynomial square is cartesian.
`BertiniAffineIncidenceChart` uses these to prove the actual polynomial quotient
presentation, including its projection to coefficient space.
`BertiniAffineIncidenceIrreducible` proves irreducibility of this scheme chart from the
height condition, for any finite variable type (including the required ULift type).

`BertiniUniversalZeroSection` constructs the zero-coefficient section over Y by the
closed-immersion lifting property. It supplies the points needed to glue incidence charts.

The remaining geometric work is isolated in `BertiniGenericFibreChart`: constructing a
trivializing affine chart meeting the codimension-two component, converting codimension to
the stated dimension equality, gluing irreducible incidence charts, and identifying the
generic residue-field arrow. Its conclusion contains concrete fields and an arrow
isomorphism, with no geometric-irreducibility assertion about the incidence function field.
Irreducibility of the generic fibre itself is proved from source irreducibility and
dominance. The algebraic Bertini argument and passage from a generic fibre to all
field-valued members are outside this statement and are completely proved in Lean.

## Proved and sorry left

Original holes: one. The original hole in
`AlgebraicGeometry.exists_open_geometricallyIrreducible_linearSystemMember` is replaced by a
complete proof from named declarations. Added holes: one,
`AlgebraicGeometry.exists_bertiniIncidenceChart`
(node `lem-zl-bertini-generic-fibre-chart`). This is a decomposition, not a net hole closure:
one original hole closed, one new hole added, net zero. No `sorry` remains in the item module.

The following new support declarations are proved without local holes:
`AlgebraicGeometry.bertiniUniversalIdeal_comap`,
`FieldTheory.geometricallyIrreducible_bertiniAffineFunctionField`,
`AlgebraicGeometry.geometricallyIrreducible_bertiniUniversal_genericFiber`,
`Algebra.exists_bertiniIncidenceElimination`,
`AlgebraicGeometry.irreducibleSpace_fiber_of_isGenericPoint`,
`AlgebraicGeometry.nonempty_fibreResidueArrow_iso`,
`AlgebraicGeometry.ideal_zeroLocus_tensorSectionsUnit_sum`,
`AlgebraicGeometry.isPullback_bertiniAffineAmbient`,
`AlgebraicGeometry.exists_bertiniAffineIncidenceChart`,
`AlgebraicGeometry.irreducibleSpace_bertiniAffineIncidence`, and
`AlgebraicGeometry.exists_bertiniUniversalZeroSection`.
All support declarations except the generic-fibre wrapper use no unproved input from this
packet; the generic-fibre wrapper and item still depend on the chart theorem. No arbitrary
data is chosen into a public definition from the remaining existence theorem: its witnesses are used solely in
the proof of a proposition.

Mathematical edge cases reviewed for the chart statement include affine space with sections
1,x,y, extra zero or dependent vectors in V, a nonreduced thickening, a finite ground field, and a change
of basis. These are mathematical checks of the new statement, not additional Lean tests.
The affine domain is chosen after reduction; generic residue fields are unchanged by that
reduction. The field arrow uses the actual induced map, allowing the sign change
in the eliminated coefficient. The elimination theorem also covers n=0 and the zero ring;
the generic-fibre lemma requires only dominance and irreducibility.

All thirteen sandbox modules compile through `lcompile.py`; all public signatures use explicit
variables and the project module system. The original public definition and theorem
signature were compared with the shared repository and are unchanged. The unit route and
source-library boundary are preserved.

## No longer needed

Removed these private proof imports from the item module:
`WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence`,
`WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing`,
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
`Mathlib.AlgebraicGeometry.Noetherian`,
`Sheaf.AlgebraicGeometry.BertiniIndependentFunctions`,
`Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility`,
`Sheaf.AlgebraicGeometry.LinearIncidenceIrreducible`, and
`Sheaf.FieldTheory.BertiniFieldExtension`.
Their needed uses are retained in the chart or proved algebraic support modules. They are
not globally pruned or withdrawn. No unused module or DAG dependency is claimed pruned. The chart-gluing step no longer
needs to solve the incidence equation over the nonvanishing locus of the first section: the
proved zero-parameter section supplies points in chart intersections directly.

Removed from the parent node's top-level `tool_uses` the direct approvals for
`lem-sc-reduction-nilradical-nilpotent` and
`lem-weil-pbc-finite-type-domain-dimension-local-ring`; their same mathematical uses now
belong to the chart presentation. The generic shrinking approval remains in order. Parent
`proof_deps` now records the wrapper, shrinking and base-change declarations actually used.

## Where the brief, the DAG or earlier work was wrong

The plan's affine chart and function-field identifications are substantial scheme-theoretic
work, not definitional rewrites of the concrete chosen tensor-pullback construction. The
existing three algebraic/generic-point inputs do not state this bridge. The new chart node
records that precise remaining argument, while the base-change and algebraic computations
are implemented.

The universal-family API indexes variables by a type in the scheme universe. The original
statement uses Fin r, so the proof uses ULift (Fin r) in the universal family and explicitly
transports the coefficient open through the polynomial variable-renaming isomorphism.
The generic-fibre irreducibility passage does not need the plan's affine localization
argument: dominance sends the source generic point into that fibre, proving it irreducible
immediately. This shorter argument is proved in its support module.

No target statement, unit step, adopted source declaration or mathematical hypothesis was
changed. No statement is disputed and no forced adaptation was made. The first full preflight
required a change record for the local proof attributes; that record is included and lists
the item and its consumers. Its status is open for the independent reader.

## New nodes

`lem-zl-bertini-universal-base-change` matches `BertiniUniversalBaseChange`: the proved
arbitrary-scheme specialization formula for the universal zero ideal. It exposes the
canonical adjunction-unit comparison used by the original member definition.

`lem-zl-bertini-affine-function-field` matches `BertiniAffineFunctionField`: the proved
algebraic Bertini deduction from the codimension-two independent-functions input and the
existing field-extension theorem.

`lem-zl-bertini-generic-fibre-chart` matches `BertiniGenericFibreChart`: the sole remaining
hole, a geometric incidence chart and generic residue-field presentation from the middle
and final paragraphs of Stacks Tag 0G4F. It is strictly part of the argument, not the original
general-member conclusion under a new name.

`lem-zl-bertini-universal-generic-fibre` matches `BertiniUniversalGenericFibre`: the proved
combination of the chart presentation, affine algebraic result and generic-residue-field
criterion.

`lem-zl-bertini-incidence-elimination` matches `BertiniIncidenceElimination`: the proved
elimination of the variable with coefficient one, retaining the substitution formula needed
for the parameter field identification.

`lem-zl-irreducible-dominant-generic-fibre` matches `IrreducibleDominantGenericFibre`: the
proved irreducibility of a dominant morphism's generic fibre when its source is irreducible.
It replaces the chart proof's longer localization argument.

`lem-zl-fibre-residue-arrow` matches `FibreResidueArrow`: the proved arrow isomorphism
comparing residue fields in a scheme fibre with the original residue-field map.

`lem-zl-bertini-trivialized-zero-ideal` matches `BertiniTrivializedZeroIdeal`: the proved
coefficient ideal equation, including compatibility of the chosen tensor unit with
ordinary pullback and its free generator.

`lem-zl-bertini-affine-ambient` matches `BertiniAffineAmbient`: the proved affine polynomial
pullback square, with both specified coordinate maps.

`lem-zl-bertini-affine-incidence-chart` matches `BertiniAffineIncidenceChart`: the proved
polynomial quotient presentation, compatible with the projection to coefficient space.

`lem-zl-bertini-affine-incidence-irreducible` matches `BertiniAffineIncidenceIrreducible`:
the proved irreducibility of trivialized affine scheme incidence charts from the
coefficient height bound, with finite-index reindexing implemented.


`lem-zl-bertini-universal-zero-section` matches `BertiniUniversalZeroSection`: the proved
zero-coefficient section of the incidence projection to Y. This shortens the chart-gluing
step by avoiding an additional unit-coefficient localization there.

Change record: `coord/changes/C8-bertini-irreducible-proof-attributes.md`.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
