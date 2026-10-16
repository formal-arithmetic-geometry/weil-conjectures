## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_pullback_cube`
with its statement, public imports, and specified comparisons unchanged.
Proof-only `import all` imports reuse the proved generic `derived_pull_comp` and
`bounded_comp_hom` calculations from `Sheaf.Paper.ContinuousIntegralPullComposition`,
and the elementary rectangle and inverse-square calculations from
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct`.

Four private projection equations are proved by reflexivity. A private composition
lemma specializes the generic derived coherence to E → PadicAlgCl ℓ, then restricts
it to bounded constructible objects. Equality transport and rectangle pasting give
the square cube; cancellation gives exactly the original inverse-comparison orientation.
The final restriction step normalizes implicit object arguments and uses `convert!`
to avoid expensive comparisons of their unreduced functor expressions.

The existing node's proof, proof dependencies, and proof-origin note now describe this
implementation. No definition, existing signature, or consumer module was changed.
Validation: the final single-file compile and axiom probe reached preflight successfully.
A separate sandbox compiled this module with artifacts in 57.6 seconds, followed by
the unchanged direct consumer `CondensedQbarExchangeLeftAdjunct` in 39.8 seconds,
using the new compiled module. The original public declaration and the node's Lean
statement match the delivered declaration exactly. The DAG dependency list equals
the union of the proof steps' dependencies.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_pullback_cube`
(node `lem-weil-pbc-qbar-condensed-pullback-cube`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.
Every new private helper has a complete proof. No split-off statements or modules.

## No longer needed

No original import was removed and no module or node is globally pruned.
The experimental proof imports
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate`
and `WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction` were removed:
the final proof calls existing generic coherence instead of reproving conjugation.

`def-weil-pbc-adjunction-mate` is no longer a direct dependency of this node; its role
is supplied inside `lem-weil-pbc-continuous-integral-pull-composition`, so it remains
an indirect dependency. The integral specialization and geometric exchange theorem
in the two imported modules are not used; only their proved generic calculations are.
No new intermediate theory is required.

## Where the brief, the DAG or earlier work was wrong

The planned derived-composition coherence already has a fully proved generic implementation
inside `ContinuousIntegralPullComposition`. Its private visibility requires a proof-only
`import all` to reuse it. The elementary diagram calculations likewise already exist in
the integral target-adjunct module. The original mathematical plan and statement are valid.
No definition or statement repair was necessary. The preflight nevertheless requires a
change record for the added local scope and attribute commands; this is documented in
`coord/changes/qbar-pullback-cube-proof-scopes.md`. These commands do not change any
public signature or exported definition.

## Second reading by D4

1. **Signatures and accidental changes — pass.** I compared the delivered module with
the repository version. The public theorem statement and all existing declarations are
byte-for-byte unchanged; the module changes are proof-local helpers, proof-only imports,
and local elaboration settings. The node changes only record the implemented proof route
and dependencies.

2. **Proof validity — pass.** The module compiles through `lcompile.py` both alone and
with the sandbox import order. There are no `sorry`, `axiom`, `unsafe`, `opaque`,
`extern`, or `implemented_by` declarations. The sole original hole,
`constructibleToQbar_pullback_cube`, is closed; no hole was added. The proof uses only
the permitted generic coherence and elementary diagram lemmas, and its local helpers
are fully proved.

3. **Split-off statements — pass.** No split-off public theorem or new node was added.
The private helper lemmas are intermediate proof steps, so they do not duplicate the
item statement or create an untracked interface.

4. **Pruning and route — pass.** The proof follows the unit route through the generic
derived composition coherence, bounded composition calculation, equality transport,
and square cancellation. The removed experimental imports and obsolete direct node
dependency are recorded under `## No longer needed`; the two proof-only `import all`
commands are required to access existing private calculations. No additional import
or module can be removed without breaking elaboration.

5. **DAG agreement — pass.** The node's proof steps and `proof_deps` match the helper
lemmas and imported declarations actually used by the Lean proof. Its statement,
chapter, unit, source, and blueprint remain unchanged, and the proof-origin note records
the reuse of the existing generic implementation.

I changed only the report by adding this second-reading record; no Lean statement,
definition, consumer, or target was changed.
