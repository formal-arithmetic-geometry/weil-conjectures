## Worker report

The shared project already contains the complete stage-2 module
`Sheaf.Paper.ModelCompactComparisonUnit` for this item. I copied it verbatim into this
sandbox and retained the node's existing Lean record. It defines the explicit proper-unit
natural transformation, the model-iterate specialization, the identity-pullback-removed
comparison, and the global operator, then states (with `sorry`) the equality, naturality,
and global-operator clauses required by `lem-zl-model-compact-comparison-unit`.

The declaration uses the actual condensed module-object interfaces from
`WeilConjectures.TraceFormula.Statement`: `compactCohomologyFrobeniusComparison`,
`weilCompactCohomology`, `WeilBoundedConstructibleOfEnd.globalOperator`, the restricted
upper-star/lower-star adjunction, the chosen compactification lower shriek, and the proper
and composition comparison isomorphisms. The finite-field and Frobenius dependencies are
`WeilConjectures.FiniteFieldDatum`, `IsModelFrobenius`, and the published
`hΦ.isFinite`/`hΦ.isUniversalHomeomorphism` interfaces.

For the statement clauses, `compactSupportProperUnit` renders the ordered unit, inverse
proper comparison, inverse composition comparison, and `h ≫ a_X = a_X` factors;
`modelCompactComparison_eq_properUnit` renders the comparison equality, naturality for
all coefficient morphisms, and the final global-operator formula. The module has
`set_option autoImplicit false`, one universe, no hollow definitions, and only the final
statement theorem is postponed with `sorry`.

Edge cases covered by the quantified statement and definitions include `r = 1`, empty or
zero coefficient objects, non-reduced models, and the identity/empty scheme cases. No
adiс, discrete, Galois, trace, or duality conclusion is introduced.

Searches recorded on the base node were consulted: LeanFinder/LeanSearch/Loogle and grep
found only generic adjunction/Frobenius declarations; the exact compact-support
implementation is the published `TraceFormula.Statement` interface. The existing module
was therefore reused rather than introducing a duplicate notion or helper node.

## Second reading by NQ

I reread the copied node and module against the source declarations. The finite-field,
separated finite-type model, prime inequality, iterate positivity, properness, actual
bounded-constructible coefficient category, and all three conclusion clauses are present.
The helper declarations use the canonical chosen-compactification maps in the stated order;
`modelCompactComparisonWithoutIdentity` removes the identity pullback by the canonical
unitor isomorphism. The theorem's naturality quantifies over arbitrary objects and maps,
and its final clause is exactly the published `globalOperator` on the iterate. No node
fields other than the existing Lean record were changed.
