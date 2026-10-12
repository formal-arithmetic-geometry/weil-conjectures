## What changed

Proved `AlgebraicGeometry.Scheme.isConstructibleSheaf_prime_of_underlyingAbelianIso`
in `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientConstructibilityTransfer`, with its
signature unchanged. Retained the existing proof-only imports of
`FiniteLocalCyclicModuleForget`, `FiniteLocallyConstantModuleValues`, and
`ModuleAbelianInverseImageComparison`. Added the proof-only import
`WeilConjectures.ConstructibleSheaf.Pullback` for local-constancy transport.

The proof retains the original stratification of F. The proved private helper
`finiteAbelianLocal_of_module` forgets a finite locally constant module sheaf to an
abelian locally constant sheaf with finite geometric stalks. The proved private
`moduleAbelianPullbackIso` packages the existing canonical inverse-image comparison
as an isomorphism. On every stratum, the given abelian isomorphism and these comparisons
transport local constancy and finite stalks to G. The existing cyclic-module equivalence
supplies finite constant module values, and the finite-values equivalence supplies the
required finite local constancy. No new definition or statement changes the public interface.

The module compiles locally without errors or warnings. The DAG proof now follows these
steps. No unit statement or realized unit step is bypassed.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.isConstructibleSheaf_prime_of_underlyingAbelianIso`
(node `lem-pbc-prime-coefficient-constructibility-transfer`).
Added 0 holes. No sorry remains in the delivered module.
The proof uses existing dependency declarations, including
`finite_local_cyclic_module_forget_iff` and `finite_locally_constant_module_values_iff`;
their remaining work is not copied into this delivery.

## No longer needed

Removed the original proof-only import
`Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`; its result is not used directly.
Both public imports serve the unchanged statement.
The trial proof import `Mathlib.RingTheory.Finiteness.Cardinality` was removed after
compilation confirmed the required finite-module theorem is already available.

`lem-weil-pbc-constant-sheaf-geometric-stalk` and its module
`Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk` are no longer direct proof
dependencies of this item. The existing cyclic-module equivalence encapsulates the
constant-stalk and cyclic-action lifting argument. It can still require that node
transitively, so this is not a claim that its module leaves the entire targets' closure.
All other original proof-dependency nodes are used, including the Mathlib constant-sheaf
comparison through the instance that forgetting preserves constant sheaves.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The separate geometric constant-stalk argument in the
original plan was unnecessary at this level: the existing cyclic-coefficient theorem
already states precisely the required conversion. The inverse-image comparison is used
for both coefficient rings, without imposing curve or nonempty-scheme assumptions.
The initial local compile lacked the recently landed cyclic-module object file; it became
available on the regular compiled-library refresh, and compilation then succeeded.


## Second reading by U2

1. Interface: compared the complete delivered Lean file and node with the repository
   using diff, and checked the existing theorem signature byte for byte by extraction.
   Its finite commutative coefficient ring, arbitrary scheme, prime r, constructible F,
   prime-field G, underlying abelian isomorphism and conclusion are unchanged. No existing
   definition changes and no change record is needed. Only two private proved helpers
   were added; no public interface was added. Verdict: pass.
2. Proof: compiled a scratch copy with the launcher and printed axioms for the main
   theorem and both helpers. The helpers use only propext, Classical.choice and
   Quot.sound. The main theorem also uses sorryAx from existing dependencies; there
   is no sorry in this module or either helper, no hollow definition and no prohibited
   declaration or attribute. The comparison helper constructs asIso of the existing
   adjunction mate, using its named invertibility theorem. Verdict: pass, a local hole
   closure conditional on existing open dependencies, not an axiom-free final target.
3. Split statements: none were added. Independently searched lean/Sheaf and
   lean/WeilConjectures for coefficient forgetting, abelian finiteness, pullback
   comparisons and constructibility under isomorphisms; LeanFinder query
   "constructibility invariant under restriction of scalars for sheaves over a finite
   prime field" returned condensed-sheaf results, not a shorter transfer theorem.
   The existing cyclic-module equivalence is genuinely intermediate: it converts local
   constancy and finite abelian stalks into finite module values on one scheme, without
   assuming constructibility or carrying a stratification. Checked empty schemes and
   empty strata, zero sheaves, and the zero coefficient ring: the first helper keeps
   the cover without choosing any point; its finiteness argument is at supplied points
   only. The target prime gives NeZero r, and the prime coefficient ring is finite.
   Verdict: no duplicate split or restatement.
4. Route and pruning: read the proof top down and sk-thm-p1.json's realized statement
   and all step lists. This node is below the unit's realized nodes; their route is
   unchanged. On each original stratum the first helper forgets a constant cover and
   transfers finite module stalks by sheafFiberCompIso. The comparison helper and e
   give UG ≅ UF; of_iso and the fiber functor transfer exactly the two predicates
   needed by finite_local_cyclic_module_forget_iff. The finite-values equivalence then
   closes finite local constancy. Public imports supply the statement; the three
   Sheaf proof imports each supply a used equivalence or comparison, and Pullback
   supplies IsLocallyConstantSheaf.of_iso. The only removed old proof dependency is
   lem-weil-pbc-constant-sheaf-geometric-stalk, explicitly listed above. Verdict: pass.
5. DAG: the changed fields are only proof, proof_deps and proof_origin. The steps
   match the helpers, the transported predicates and the two final equivalences;
   proof_deps is the union of uses. The constant-module-underlying leaf is realized
   by Mathlib's constantCommuteCompose through the constant-preservation instance.
   Read [Stacks 03SC](https://stacks.math.columbia.edu/tag/03SC), second proof
   paragraph, and [03RW](https://stacks.math.columbia.edu/tag/03RW), clauses 2 and 3.
   The coefficient bookkeeping is the documented expansion of that passage; Lean's
   global stratification convention is stronger than the affine-local definition on
   arbitrary schemes, as already documented in Defs, and this proof preserves that
   same global stratification. No source equivalence or definition was silently changed.
   Verdict: node agrees with Lean and the unit route is retained.

Second-reading changes: corrected the import accounting in What changed and No longer
needed (the three Sheaf proof imports already existed, and ConstantSheafGeometricStalk
was removed). Added this independent review and its axiom qualification. The Lean proof
and DAG needed no repair. Closed 1 existing named hole; added 0 holes; split off 0.
