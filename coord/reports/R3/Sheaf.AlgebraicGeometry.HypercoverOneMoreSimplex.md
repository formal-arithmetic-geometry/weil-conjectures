## What changed

Proved `AlgebraicGeometry.Scheme.isSemiRepresentableCovering_simplicialHomRestriction_one_more_simplex`
with its original signature and public imports unchanged. All work is in
`lean/Sheaf/AlgebraicGeometry/HypercoverOneMoreSimplex.lean`, plus the matching existing DAG node.

The proof follows [Stacks Tag 01GM](https://stacks.math.columbia.edu/tag/01GM), read in full:
apply `SSet.glue_simplex` to the upper subcomplex `top`, transport along `Subcomplex.topIso`,
and use the existing Hom-pushout theorems. In successor degree, obtain a representing boundary
family from `exists_simplicial_hom_object`, identify its restriction with the matching map
using `simplicial_hom_boundary_matching`, and apply covering permanence under base change.
In degree zero, the boundary is empty; the Hom-pushout theorem gives a product, which is a
pullback over the terminal degree-zero matching object.

Fully proved private helpers supply the comparison equations, convert the unique-map
universal property into `Functor.IsRepresentedBy`, show split epimorphisms (hence
isomorphisms) are coverings by exhibiting the identity in each component sieve, and
transport covering permanence to an arbitrary pullback square. The two private definitions
are actual constructions: pull back a compatible family along a simplicial map, and invert
the bijection of a representing universal property. Neither chooses arbitrary data from
an unproved existence assertion.

The DAG retains the source route and records the actual component-map calculations and
its additional direct use of `lem-weil-pbc-simplicial-hom-object-exists`. No existing
statement, definition, visibility, or target signature changes. No new module or node remains.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.isSemiRepresentableCovering_simplicialHomRestriction_one_more_simplex`
(node `lem-weil-pbc-hypercover-one-more-simplex`). Holes closed: 1. Holes added: 0.
No `sorry` remains in any delivered declaration. All private helpers are completely proved.

This is a proof from the existing DAG declarations, which remain obligations of their own:
`SSet.glue_simplex`, `simplicial_hom_standard_simplex`, `simplicial_hom_boundary_matching`,
`exists_simplicial_hom_object`, both Hom-pushout theorems, and
`semiRepresentableCovering_comp_baseChange`. It does not claim these imported obligations
are already axiom-free. The final item compiles without errors or warnings in about five
seconds using the prescribed `lcompile.py`.

## No longer needed

None of the original dependency modules or imports is pruned. All are used by the proof:
Hom families/restriction; simplicial finiteness; covering permanence; the original
semi-representable matching objects, covering predicate and finite-limit instances;
Hom-pushout; standard-simplex/boundary matching; and simplex attachment. The finite-limits
node is realized by its recorded Mathlib declarations, including `FormalCoproduct.isTerminalIncl`.
No new unfinished degree-case module is part of the delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan was sufficient. The original proof dependencies
left the boundary Hom-object existence invocation implicit; the updated node names its
existing theorem explicitly. The zero-degree case is handled separately, without imposing
nonemptiness on the empty boundary or using the positive-degree matching theorem at zero.
The proof also covers empty schemes and formal index families, without adding assumptions.

Searches through the source library, the Sheaf modules and Mathlib found no theorem directly
proving this restriction covering. The prescribed LeanFinder search returned only zero/one
hypercover results; Loogle for `FormalCoproduct.Hom` exposed the component API, rather than
a theorem replacing the argument. The original statement and unit route are retained.

## Second reading by R3

1. Compared the complete module and node against the repository versions. The existing
   theorem signature (including every hypothesis, conclusion, and universe) and its
   docstring are byte-for-byte unchanged. All added helpers are private. The node changes
   only its proof route, dependencies, origin, and semantically identical JSON escaping
   in `lean.statement`. No change record or forced adaptation is needed. Verdict: pass.

2. Compiled the delivered file cleanly with the prescribed `lcompile.py`. Compiled a
   scratch copy of the entire delivered source with `#print axioms` for the target and
   every private helper/definition: only `propext`, `Classical.choice`, `Quot.sound`, and
   inherited `sorryAx` occur. The module has no local `sorry` or forbidden declaration.
   `pullFamily` constructs its components directly; `liftFamily` inverts a bijection,
   whose universal property determines the arrow uniquely. Verdict: pass.

3. There are no new split-off statements or nodes to review. Checked the proved helpers
   mathematically: a section supplies an identity factorization in every target sieve;
   the representing bijection uniquely supplies each comparison arrow. At degree zero
   the boundary is empty and the product theorem applies; at degree one the boundary
   theorem is used with parameter zero, so its nonemptiness hypothesis is valid. Empty
   target index families are handled vacuously, with no extra assumptions. Verdict: pass.

4. Read the imported declarations and searched the library and Mathlib using alternate
   terminology (simplicial hypercover restriction and simplex attachment), LeanFinder,
   Loogle, and `rg`. No existing theorem replaces the argument. Each original dependency
   remains used: no node/module is pruned. Both public imports provide statement data;
   all proof-only additions remain plain imports. Checked the source proof in
   [Stacks Tag 01GM](https://stacks.math.columbia.edu/tag/01GM): it uses the same
   simplex pushout, matching-cover pullback, and zero-degree product. The unit record
   `dag/units/sk-prop-h2.json` is unchanged, including its pre-existing empty `realized`
   entries; this below-unit proof preserves the recorded route. Verdict: pass.

5. The seven node proof steps and their union `proof_deps` match the Lean proof,
   including the explicit Hom-object existence invocation. The original statement,
   statement dependencies, chapter, and unit are unchanged. No new node fields or
   change records are required. Verdict: pass.

Second-reading changes: added this review section only. No Lean repair was necessary.
