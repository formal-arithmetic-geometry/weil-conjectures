## Reason

The multiplication-roof statement combines construction of normalized maps, a finite
multiplication calculation, a homological tensor calculation and localization cancellation.
The three unfinished steps need independently importable modules. Keeping the data in the
item would create an import cycle between those proof modules and the item.

## Old

`Sheaf.CategoryTheory.LatticeCubicalMultiplicationRoof` declared `Roof`, its six composition
predicates/maps, the concrete cubical/Koszul coordinate constructions and one theorem whose
proof was `sorry`. Its three public imports exposed the existing input definitions.

## New

The definitions and instance aliases move verbatim, with the same namespace, signatures,
bodies, priorities and irreducibility attributes, to the new module
`Sheaf.CategoryTheory.LatticeCubicalMultiplicationData`. The item publicly imports that module,
which publicly imports the same three original modules. Consequently all previously public
names and imports remain available to every importer of the item. No mathematical construction
or existing theorem signature changes. `Normalized` abbreviates the three coordinate formulas
and three counit laws; `TensorRepresentatives` abbreviates the two original tensor clauses.
Neither definition chooses any data or contains a proof hole.

Three new proof modules each state one strict part of the argument. Their construction theorem
returns maps fixed by all the generating-cell formulas, and is used only inside the theorem's
proof; no public definition selects its witness. The parent derives the final theorem from the
three parts, with explicit proofs of localization cancellation, the sign identity, both low-rank
product formulas and the rank-one diagonal. The original statement remains verbatim.

## Users

There are no current direct Lean importers of
`Sheaf.CategoryTheory.LatticeCubicalMultiplicationRoof` (searched both library roots for both
ordinary and public import lines). DAG parents with unfinished proofs still need the item;
none is withdrawn or has its dependency changed. The item's own statement is compiled against
the relocated definitions and has exactly the same coordinate formulas and hypotheses.

The new proof modules import the data module and the item imports all three for its proof.
No existing module outside the item is changed, and no consumer adaptation is needed.

## Status

landed 20261026T082044-L-2126363 2026-10-26 (merge of deliver/H2/Sheaf.CategoryTheory.LatticeCubicalMultiplicationRoof)
