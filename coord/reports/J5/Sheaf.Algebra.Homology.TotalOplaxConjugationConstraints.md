## What changed

Replaced the proof hole in `CategoryTheory.TotalOplaxConjugation.constraints`
with the ten-step argument already recorded in its docstring and DAG node.
Added a private proof import of
`Sheaf.Algebra.Homology.TotalOplaxConjugationSummands` and proved private helpers.
All existing public definitions and theorem statements are unchanged.
Four proved instance-shortcut theorems (`tensorExists`, `tensorGoodLeft`,
`tensorGoodRight`, and `tensorFour`) give elaboration direct access to the existing
graded-tensor existence and preservation instances. They are public because
public definitions cannot refer to private proof helpers; their instance
attributes are local to this module. They cache proposition-valued instance
proofs, not tensor data, and introduce no new mathematical assumption or
intermediate proof obligation. All four proofs are `inferInstance`.

The proof uses the published forward summand expansion, cancels the actual
isomorphisms for the inverse restriction, and uses the chain-map and inverse
identities of those isomorphisms. The canonical unit comparison gives its
component in degree zero; additive functors preserve the zero objects in other
degrees. Reinserting the source tensor comparison gives the hatted summand
formula. Naturality of the arbitrary square isomorphism, the ordinary
inverse tensorators, and tensoring computes both nested associator paths and
both unit paths. No monoidality of the square isomorphism is assumed.

For infinite sums, the proof applies preserved-coproduct extensionality first
to the outer coproduct and then to the inner coproduct after tensoring.
This yields all four detection tests. Finally, component extensionality and
these tests lift the ordinary constraint equalities; the unit cases separate
the degree-zero summands from zero summands.

## Proved and sorry left

Closed the one existing hole:
`CategoryTheory.TotalOplaxConjugation.constraints`
(node `lem-pd-total-oplax-conjugation-constraints`).
No holes added or split off. No `sorry` remains in the item module.

Validation: the complete delivered module compiled in 49.2 seconds, below the
60-second limit, with no errors or warnings. The axiom audit of `constraints`
reported only `propext`, `Classical.choice`, and `Quot.sound`. Every pre-existing
public definition is textually unchanged; the theorem statement is unchanged.
No new module, node, or consumer adaptation is required.

## No longer needed

Removed redundant public imports of
`WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`,
`Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`, and
`Mathlib.Algebra.Homology.DerivedCategory.Basic`. The statements only need the
complex tensor API, abelian categories, countable coproducts, and preservation
by equivalences; the replacements are the precise Mathlib imports
`Mathlib.CategoryTheory.Abelian.Basic` and
`Mathlib.CategoryTheory.Limits.Shapes.Countable`, alongside the retained imports.
The new proof import itself still imports the first two removed modules, so
this is removal of unnecessary public visibility, not withdrawal of those
modules from the library or their use elsewhere.

The existing DAG route is retained. The proof uses the declared
termwise monoidal comparisons, conjugated summand formula, tensor constraints,
tensor-map formulas, preserved-colimit extensionality, and colimit preservation
by the equivalences. No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The source Tag 0FPQ omits the
constraint verifications; the existing node supplies the explicit extraction
proved here. The unit route in `sk-thm-sf-verdier-exchange` is unaffected.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
