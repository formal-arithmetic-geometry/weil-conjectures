## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.EtaleInverseImageComparisonAddition`
by a complete proof of `AlgebraicGeometry.etaleInverseImageComparisonAddition`.
Its signature and visibility are unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLiftOperations`.

Ring addition is constructed sectionwise on categorical products, with naturality
proved using restriction homomorphisms. Compatibility at the identity identifies
the forgotten ring unit with the set unit followed by `er.inv`. The two product
projections and injectivity of the set adjunction reduce ring addition transport
to `map_add` for that unit. For the abelian addition use the existing
`AlgebraicGeometry.etaleInverseImageAbelianLift_operations` with the supplied `ea`.
Private proved helpers give the tensor-to-product projection identities and the
categorical cancellation converting both equations to the required tensor form.
No arbitrary object is chosen from a holed existence theorem.

Updated the item's node proof, proof dependencies, and proof origin to describe
this route. No new modules or nodes; no interface changes or forced adaptations.
The unit `sk-def-exchange` realizes neither this statement nor a proof step, so
its fixed route is preserved.

## Proved and sorry left

Closed: `AlgebraicGeometry.etaleInverseImageComparisonAddition`
(node `lem-weil-pbc-inverse-image-comparison-addition`), 1 of 1 original holes.
No sorry remains in the item; no holes added or split off.
The sectionwise construction and all private helpers are proved.
Local single-file compilation passed without warnings (49.1 seconds).
The delivery dry run also checks the axioms of the declarations.

## No longer needed

The proof no longer needs `lem-weil-pbc-conjugate-iso-unit-equation`
(`CategoryTheory.unit_conjugateEquiv_symm` in Mathlib adjunction mates),
canonical ring lift comparison, or uniqueness of left adjoints.
`lem-weil-pbc-etale-inverse-image-algebraic-structures` is no longer a proof
dependency and its theorem is not applied. Its existing public import stays
because it supplies the public definitions and instances of the unchanged
statement, which also records it as a statement dependency. No original
proof-only import was present to remove. No claim that an entire module has
left the global targets' import closure is made.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox module was empty, so the repository module was copied and
proved anew. The planned canonical-lift and adjoint-uniqueness comparison is
unnecessary: the supplied hom-equivalence compatibility already determines
the unit equation needed for addition. The existing abelian operation theorem
handles an arbitrary supplied comparison, rather than only a chosen one.
The original theorem docstring records the old valid route and was preserved;
the updated DAG and this report describe the implemented shorter proof.

Searches: LeanFinder for inverse-image addition compatibility returned related
sheaf/module addition facts but no exact match; Loogle for `prodComparison`
returned the projection and inverse comparison tools; grep for
`homEquiv.*add|add.*homEquiv` returned adjunction/additivity facts.
Local reading found the existing supplied abelian operation theorem and the
ring-unit calculation in `EtaleInverseImageRingComparisonOperations` and
`EtaleInverseImageRingLift`, used as the model for this proof.

Source reading: [Stacks 00YV](https://stacks.math.columbia.edu/tag/00YV),
proof of (2) and the following ring paragraph, and
[Stacks 03D2](https://stacks.math.columbia.edu/tag/03D2), product transport of
the action. The unit/projection calculation supplies the adjointness details
left implicit in 00YV and is proved in Lean here.

## Second reading by H1

1. **Unchanged interface — pass.** Compared the delivered module and node with
   the repository versions using `diff -u`, then compared the complete original
   theorem signature byte for byte: identical. The only source additions are
   one plain proof-only import, four private declarations, the scoped heartbeat
   setting, and the theorem proof. No existing definition or visibility changed;
   no change record or forced adaptation is needed.
2. **Kernel proof — pass.** Independently compiled the delivered file through
   `lcompile.py`: exit 0, no warnings, 43.6 seconds. A scratch copy with explicit
   `#print axioms` for the public theorem, `ringAdd`, `tensor_add_transport`,
   `tensor_to_product_fst`, and `tensor_to_product_snd` compiled in 48.2 seconds.
   Every axiom list contains exactly `propext`, `Classical.choice`, `Quot.sound`;
   none contains `sorryAx`. Searched the delivered source for forbidden
   declarations and sorry tokens: none. `ringAdd` is an explicit sectionwise
   construction with a proved naturality field. The abelian witnesses come from
   an already proved operation theorem, and their section formulas determine
   the addition maps by extensionality. No arbitrary holed existence is used.
3. **Split-off statements — pass, none.** No new public statements, nodes,
   modules, or holes were introduced. Read each private helper: the two
   projection equations directly instantiate Mathlib's limit-cone uniqueness
   theorem, and tensor transport is inverse cancellation, valid also for
   identity comparisons and degenerate products. Ring addition uses no
   nonzero or inhabited-section assumption; zero rings and empty sites cause
   no exceptional case. Read the existing abelian operation theorem and
   checked that its supplied comparison and compatibility hypotheses are the
   ones passed here. Its addition section formulas uniquely determine the
   maps used in the conclusion.
4. **Shortest route and pruning — pass.** Searched local Sheaf and upstream
   sources for addition transport, ring addition and the cone projection
   identity, and made a fresh Mathlib grep search for
   `unit_naturality|map_add.*unit|unit.*map_add` through `msearch.py`. No shorter
   applicable public ring-addition theorem was found: `EtaleInverseImageRingLift`
   constructs its own lift, and the supplied-ring comparison theorem handles
   multiplication and one. The existing supplied abelian theorem is reused.
   The new import is plain `import`; the retained public imports provide the
   definitions, instances and tensor/module types of the unchanged signature.
   Both removed original proof dependencies are listed under No longer needed.
   No whole module is claimed pruned. Read `dag/units/sk-def-exchange.json`: its
   realized statement nodes are the derived exchange and replacement nodes,
   and its steps are empty; this auxiliary reduction bypasses neither.
   Read Stacks [00YV](https://stacks.math.columbia.edu/tag/00YV), proof of (2)
   and the ring paragraph, and [03D2](https://stacks.math.columbia.edu/tag/03D2):
   the operation and product transport agree with these sources.
5. **DAG agreement — pass.** The existing node's statement, statement
   dependencies, source and Lean signature record remain unchanged. Its three
   proof steps match the explicit ring-unit calculation, use of
   `etaleInverseImageAbelianLift_operations`, and tensor inverse cancellation.
   The union of the steps' uses equals `proof_deps`. Checked the declared Lean
   records of the direct/inverse image and abelian-operation dependencies.
   `proof_origin` explicitly attributes the expanded calculation to the agent.
   There are no new nodes requiring extra metadata.

Second reading changed only this report: added the independent checks and
verdicts. No proof repair was needed. The existing theorem docstring describes
the former canonical-lift route rather than the implemented shorter proof;
this discrepancy is documented here and above, while the updated DAG describes
the actual proof. Holes closed: `AlgebraicGeometry.etaleInverseImageComparisonAddition`
(1 of 1). Holes added or split off: none.
