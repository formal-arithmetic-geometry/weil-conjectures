## What changed

Completed the six theorem proofs in
`Sheaf.CategoryTheory.Sites.NormalizedFreeModuleComparison`, preserving every existing
signature, definition body and public import. Added the private proof import
`Mathlib.CategoryTheory.Sites.CartesianMonoidal` and proved private helpers.

The generator equation follows from the declared free-module extension inverse.
Semilinear transport is proved on arbitrary sections: finite-product preservation
lifts two operands simultaneously, and the recorded operation graphs transport
addition and scalar multiplication. Additivity gives preservation of zero.
Naturality restricts scalars along the possibly noninvertible coefficient map,
constructs the two linear composites, and applies the assumed representing
bijection's injectivity after checking their generator equations.
Products use naturality, composition of generator changes, and the canonical
projection identity. Identity uses injectivity of restriction to generators.
Composition constructs the actual composite presentation, transports the identity
map between the two presentations, and applies the composite representing
bijection. No adjunction is assumed for either set-sheaf functor.

The proof follows all seven existing DAG steps and their declared dependencies;
no node or route changes are needed. The source passages read were Stacks
`sites-modules.tex`, lemma-universal-module (04BL), generator extension in its
proof, and lemma-pullback-differentials (08TQ), its free-module identifications.
The unit record sk-i-curve-zero has no realized statement or steps assigned to
this auxiliary node, and no unit route is changed.

## Proved and sorry left

Closed all six original holes, with the common namespace
`CategoryTheory.SheafFreeModule`:

- `normalizedFreeModule_change_semilinear`
- `normalizedFreeModule_naturality`
- `normalizedFreeModule_generators`
- `normalizedFreeModule_products`
- `normalizedFreeModule_identity`
- `normalizedFreeModule_composition`

All six belong to node `lem-trf-normalized-free-module-comparison-calculus`.
Remaining holes in the item: zero. Holes added: zero. Split off: zero.
The proofs use the existing declared dependencies
`freeModule_restrict_bijective` and `freeModule_extend_inverse`; the current
FreeModuleUniversalProperty module already proves them.
Every new private helper is proved, including every field of the composite
presentation. The completed module passes the required single-file compiler
without warnings. The delivery tool performs the independent preflight.

## No longer needed

None. No existing import, node or module is pruned. All four declared proof
dependencies remain relevant through the module category, the free universal
property, the sheafification construction, and the algebraic transport interface.
Mathlib searches were run through msearch: LeanFinder on normalized generator
comparisons, Loogle on PresheafOfModules.freeAdjunction, and grep for free Hom
composition and product comparison projections. The returned free-sheaf API
uses constant generator types, so the existing arbitrary-sheaf declarations are
used as planned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The initial unchanged file exceeded the compiler's
60-second limit. Profiling identified repeated multicospan typeclass searches for
HasSheafCompose. Local reuse of the existing instances and command-scoped disabling of the
expensive generic multicospan search resolve this without changing any public
instance or definition. The attribute is restored after each declaration.
The returned packet omitted five consumers from the change record. The repaired
`coord/changes/normalized-free-comparison-local-instances.md` lists all five and
the other four current transitive downstream modules, with their holders and
unchanged effect. The earlier zero-consumer claim covered only textual mentions
of `normalizedFreeComparison` and was incomplete.

Reconciled the packet with the current source: kept its public import of
`FreeModuleSheafConstruction` and all nine local cache bodies `:= inferInstance`
verbatim. The old `InverseImageFreeModule` import would now create a cycle,
because that parent uses the normalized comparison theorems. No public import
changes relative to current source, consumer adaptations, or node changes are
needed. Explicit universe arguments in the transport and composite-presentation
helpers retain the independent site universes.

The empty finite index type is included: the generator calculation uses an
arbitrary map into the target generator sheaf and the projection clause is
vacuous. No nonemptiness, coefficient invertibility, or additional adjoint
hypothesis is introduced.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
