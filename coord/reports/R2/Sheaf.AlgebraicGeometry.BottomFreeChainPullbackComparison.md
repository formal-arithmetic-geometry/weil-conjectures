## What changed

Replaced the retained duplicate endpoint theorem with the new module
`Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare`. It states the geometric
comparison before homology in the derived category of the localized site.
The original theorem keeps its signature and docstring. Its proof constructs the
explicit additive functor, applies the derived square, maps that equation through
homology, and composes with natural homology-factorization isomorphisms.
The exact restriction/homology comparison is reused from the already proved
`Functor.mapDerivedCategoryHomologyFunctorIso` in the source library.
No definitions or existing statements change. The additivity helper is private and proved.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.bottomFreeChain_pullback_comparison` by decomposition.
Added one hole: `AlgebraicGeometry.Scheme.bottomFreeChain_derived_square`, node
`lem-sc-bottom-free-chain-derived-square`. This is the geometric part of the argument;
the final homology transport and additivity are proved. Net holes closed minus added: 0.
The retained `bottomFreeChain_pullback_endpoints` and its duplicate node were discarded.

## No longer needed

The original module no longer directly imports
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` or
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`; those remain needed by the new
geometric comparison module and are not pruned from the closure.
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses` and node
`lem-pc-derived-pullback-open-restriction-universes` are unnecessary for this route:
derived composition along the cartesian open square suffices.
The two retained additivity/endpoint nodes were discarded, not delivered.
For completeness, the old parent proof dependencies
`def-pc-derived-pullback` and `def-pc-module-pullback` remain statement dependencies
and are available through the retained public imports.
`lem-pc-flat-complex-derived-pullback` and
`lem-pc-ringed-spaces-derived-pullback-composition` move to the derived-square node;
their modules remain imported there. Thus all five old parent proof dependencies
are accounted for. No whole module is shown unreachable from all targets by this delivery;
only the open-restriction dependency is removed from this route.

## Where the brief, the DAG or earlier work was wrong

The previous endpoint theorem repeated the original signature and was not a reduction.
Its node records also abbreviated the signatures and omitted the LeanSearch kind.
These are replaced by a genuinely separate derived-square statement with its exact signature.
The previous report incorrectly wrote its own second-reading section; it is removed.
The original source reference 08DW concerns quasi-coherent derived pullback, not the
unrestricted open-restriction assertion. The new geometric argument uses 0D5S and
exactness of open immersion restriction, without a quasi-coherence assumption.
LeanSearch was unavailable; LeanFinder, Loogle, Mathlib grep and source-library grep ran.
No unit statement or realized unit step is bypassed.

## New nodes

`lem-sc-bottom-free-chain-derived-square` isolates steps 1 and 2 of the original argument:
K-flat computation, composition along the cartesian open square, and exact site transport.
It has no cohomology degree or homology square. The parent proof performs the missing
homology step using already proved library declarations. Empty opens, zero ranks and
zero complexes use the same exact equivalences and counits; no point or vanishing
hypotheses were introduced.
Change record: `coord/changes/additive-imports.md`. Preflight requires it for
the added local instance attributes, although their scope is this module only.


## Second reading by R2

1. **Interface preservation — pass.** Compared both delivered modules against the
   repository. The only existing module changed is the item. Its original theorem
   signature is byte-for-byte identical, as is its docstring; both public imports
   remain. The additivity helper is private and proved. The new derived-square
   module adds a theorem, not data or a replacement definition. The existing node
   changes only `proof`, `proof_deps` and `proof_origin`.
2. **Proof and trust — pass.** Compiled the two modules in import order with
   `lcompile.py --all`. The only explicit `sorry` is
   `AlgebraicGeometry.Scheme.bottomFreeChain_derived_square`. Inspected all delivered
   code for forbidden declarations and hollow definitions; none occur. Independently
   checked the additivity argument and the three naturality equations composing the
   homology square. The independent scratch-copy `#print axioms` checks passed: the private
   additivity helper uses only `propext`, `Classical.choice`, `Quot.sound`;
   the parent and the split derived-square theorem use those plus `sorryAx`,
   as expected from the remaining geometric hole. No additional axiom occurs.
3. **Split statement — pass as a decomposition.** The new lemma is exactly the
   geometric comparison before homology, carrying steps 1 and 2 of the old plan;
   the parent proves additivity and the homology-transport step. It is not the same
   conclusion under another name. Its free and bounded-above hypotheses imply K-flatness;
   a common counit gives naturality at the specified chain map. Derived composition
   along `V.ι ≫ g = h ≫ W.ι`, exact restriction, and the module-site equivalence
   give the stated endpoint identifications. Standard localization changes only
   the chosen model of the category. Checked empty opens, zero ranks/complexes,
   identity base change, and arbitrary degrees: none require extra hypotheses.
   Verified the cited [06YD](https://stacks.math.columbia.edu/tag/06YD),
   [06YJ](https://stacks.math.columbia.edu/tag/06YJ) and
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S).
   Repeated LeanFinder with an exact-restriction/flat-complex query, Loogle with
   `CategoryTheory.Functor.leftDerivedUnique`, and Mathlib grep for
   `restrictFunctorIsoPullback|mapDerivedCategoryFactorsh|leftDerivedUnique`.
   Searched the project for the same localization primitives, and inspected
   `LocalizedPullbackPerfectModel`, `AffineDerivedPullbackTensorTilde` and
   `DerivedPullbackOpenRestrictionUniverses`. These provide useful ingredients,
   but no existing theorem states this specified natural square for arbitrary
   bounded-above finite-free models. The remaining hole is not a few-minute closure.
4. **Route and pruning — pass.** The parent reuses the existing exact-functor
   homology comparison and Mathlib homology factorization. All new proof imports
   are plain imports; the new module's public exact-functor import is needed by
   its statement. Its geometric proof-dependency imports retain the plan for its
   remaining hole. The complete old-dependency accounting is above. Read
   `dag/units/sk-prop-av-cube.json`: this item realizes no unit statement or step,
   and the cube theorem's route is unchanged. The referenced literature unit
   file is absent on this machine; its full statement and proof step are recorded
   in that unit JSON, which was inspected.
5. **DAG agreement — pass.** Checked the parent proof's actual use of the new node,
   and the new node's proof steps, dependency union, source, searches, provenance,
   chapter/unit, creation metadata and verbatim Lean statement. The node's new
   theorem describes the actual derived square used before applying homology.

Changes made by the second reader: completed the accounting of all five old
parent proof dependencies; clarified that route pruning does not establish
whole-target-closure pruning; rewrote `coord/changes/additive-imports.md` with the exact old/new commands
and explained why the local instance attributes change no downstream interface
(the preflight nevertheless requires a record for these commands); appended
this independent review. No Lean proof or signature needed repair.
