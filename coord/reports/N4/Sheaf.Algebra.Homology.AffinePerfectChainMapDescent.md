## What changed

Replaced the sole hole in `Sheaf.Algebra.Homology.AffinePerfectChainMapDescent` by a
complete Lean assembly from two strictly smaller intermediate statements. The original
public theorem signature and public imports are unchanged. Added the proof imports
`Sheaf.Algebra.Homology.BoundedGradedMapColimitDescent` and
`Sheaf.Algebra.Homology.FiniteChainSquaresColimitDescent`; removed the direct proof
import of `Sheaf.Algebra.FinitePresentationColimit`.

The assembly proves finite presentation of all terms from finite projectivity, descends
only the graded components first, derives their extended chain-square equations by a
proved cancellation/naturality lemma, imposes finitely many squares at a later stage,
and constructs the chain map. Outside the source interval, its equations follow from
preservation of zero objects. The final comparison is the original canonical
`scalarExtensionHom`, checked by unfolding its components and extensionality.

Read Stacks Tags [09RE](https://stacks.math.columbia.edu/tag/09RE) and
[05N7](https://stacks.math.columbia.edu/tag/05N7). The first is the bounded-source
finite-data argument; the second supplies map lifting and eventual equality. The new
nodes retain both existing finite-presentation and filtered-ring-elementwise proof
dependencies, including the preorder bridge that their existing interfaces do not supply.
The unit's route is unchanged. No existing definition or statement was changed, and
no other group's module was adapted.

## Proved and sorry left

Closed the original hole in `CochainComplex.affine_perfect_chainMap_descent`
(`lem-pc-affine-perfect-chain-map-descent`); there is no sorry in the assigned module.
Its private lemma `CochainComplex.graded_comm_of_conjugate` is also fully proved.

Added exactly two named holes, each with proof exactly `:= by sorry`:

- `CochainComplex.exists_bounded_graded_map_of_directed_colimit`
  (`lem-pc-bounded-graded-map-colimit-descent`), in
  `Sheaf.Algebra.Homology.BoundedGradedMapColimitDescent`.
- `CochainComplex.eventually_commuting_finite_chain_squares`
  (`lem-pc-finite-chain-squares-colimit-descent`), in
  `Sheaf.Algebra.Homology.FiniteChainSquaresColimitDescent`.

This is a decomposition, not a sorry-free proof of the original mathematical result:
one upper hole was closed and two lower holes were added. The first lower statement
lifts arbitrary graded components and asserts no differential compatibility. The second
starts with maps already over a stage, requires no boundedness, and detects only a
specified finite interval of equations. Neither restates the upper theorem.

All three delivered modules compile together with `lcompile.py --all`, without errors
or warnings. The new statements were checked on an empty interval, a one-degree
source, the zero source, a constant diagram, and mutually comparable distinct preorder
indices. For an empty interval the first statement has only zero-source maps and the
second imposes no equations. The endpoint square n=b is explicitly included, so the
zero component in degree b+1 causes no missing boundary equation. The presence of i₀
ensures a nonempty indexing type without adding a hypothesis.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.FinitePresentationColimit` from the
assigned module. Its declaration `ModuleCat.finitePresentation_descent_directedColimit`
remains a planned dependency of the two new intermediate statements, and those new
modules import it; it is not globally pruned.

The old direct node dependencies `lem-pc-fp-module-map-descent-affine` and
`lem-pc-filtered-colimit-commrings-elementwise` have moved below the two new lemmas.
They remain needed there, so no existing DAG node or module can be declared globally
unneeded. No modules are claimed pruned. No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The cited finite-presentation theorem assumes `[PartialOrder I]`, whereas the assigned
statement assumes only `[Preorder I]`. It cannot be applied directly. The original DAG
already acknowledges this, but does not provide a Lean bridge. The two intermediate
statements isolate that bridge together with finite-family synchronization, explicitly
retaining directed preorders. Their docstrings and nodes give both the finite-matrix
argument and the mutual-comparability quotient route; neither silently assumes
antisymmetry or excludes equivalent distinct indices.

The target bound for K₀ is not needed by this assembly, but its hypothesis is preserved
exactly. The source bound is used to reduce all chain squares to a finite interval.

The local literature checkout has no `literature/stacks-project/perfect.tex` or
`literature/stacks-project/algebra.tex`; the public Stacks tag pages were read instead.
WANTED: those local source files for the two new nodes. The explicit specialization
proofs are marked `proof_origin.by = agent`. Searches of Mathlib, both library roots,
and the DAG found no existing bounded-graded-map or finite-chain-square descent
statement. LeanSearch was unavailable (Internal Server Error), which is recorded
without claiming a successful search; LeanFinder, Loogle, and source grep ran.

## New nodes

`lem-pc-bounded-graded-map-colimit-descent` states only the graded component lifting
part of the original proof. It has finitely presented terms and a bounded source, but
accepts any family of module maps and asserts no chain conditions. Its complete proof
sketch lifts finite presentation coefficients and relations, chooses a common stage,
and puts zero outside the interval. Its Lean statement pins the comparisons to the
canonical scalar-extension isomorphisms, rather than arbitrary isomorphisms.

`lem-pc-finite-chain-squares-colimit-descent` states only eventual equality of finitely
many differential squares for an existing stage graded map. It needs no support bound,
asserts equations only on [a,b], and preserves the colimit extension in every degree.
Its complete proof sketch uses the equality clause of finite-presentation descent,
a common later stage, and scalar-extension naturality and associativity. No new map
lifting is hidden in this statement.

Both nodes inherit chapter `sec-picard-framework` and unit `sk-thm-picard-semicon`.
The assigned node's proof, proof dependencies, and proof origin were updated to the
compiled Lean route. No change record is needed because all existing signatures and
definitions are unchanged.

## Second reading by N4

1. **Interfaces: pass.** Compared the assigned module with the repository using diff,
   and separately asserted byte-for-byte equality of the complete existing theorem
   signature up to its proof delimiter. Both bounds, all finite/projective hypotheses,
   the directed preorder, universes, and the canonical scalarExtensionHom conclusion
   are unchanged. The only new declaration there is the private proved conjugation
   lemma. Neither new module exists in the repository. No definitions or existing
   public imports were changed, and no forced adaptations or change records are needed.
2. **Lean proof and axioms: pass as a decomposition.** Compiled all three modules in
   import order through lcompile.py, without errors or warnings. Individually compiled
   scratch copies with #print axioms for all four declarations. The private
   graded_comm_of_conjugate uses only propext, Classical.choice and Quot.sound; the
   upper theorem and the two reported open theorems additionally use sorryAx. The only
   literal holes are the two named split-off theorems, each exactly := by sorry. There
   are no axioms, unsafe/opaque declarations, external implementations, new definitions,
   or arbitrary witnesses used as definition data. The existential choices are local
   to a theorem proof, not constructions exported from unproved existence statements.
3. **Split statements: pass.** Read both complete statements, docstrings and nodes,
   and Stacks [09RE](https://stacks.math.columbia.edu/tag/09RE), affine case (1), and
   [05N7](https://stacks.math.columbia.edu/tag/05N7), clauses (2) and (3). The first
   lower theorem descends graded components only; the second detects a finite list of
   equations for already supplied components. Neither restates chain-map descent.
   Finite presentation is available for each source and target, including the target
   degree n+1 of a square, and is preserved by scalar extension. A common upper stage
   synchronizes the finite interval. For a>b, zero sources make the first comparison
   automatic and the second has no equations. For a=b the endpoint square is retained;
   outside the interval the upper proof uses a zero source. Constant diagrams and
   mutually comparable distinct indices introduce no extra obstruction: the latter
   give inverse ring isomorphisms, justifying the posetal-reflection bridge. The base
   index i₀ supplies nonemptiness. Independently searched with LeanFinder for finite
   presentation of morphisms over varying scalar rings, Loogle for
   Module.FinitePresentation, msearch grep for map lifting/equality at colimits, and
   rg on both library roots and Mathlib's module sources. Hits concern fixed-ring
   module colimits or finitely presented ring homomorphisms, not these statements.
   The nearby graded-object and differential descent statements do not supply these
   canonical component comparisons. Neither lower hole can be closed in a few minutes
   by the current partial-order descent interface; its preorder bridge still needs work.
4. **Route and pruning: pass.** Read the finite-presentation dependency and nearby
   graded-model/differential descent interfaces. The upper proof first uses Mathlib's
   finitePresentation_of_projective, then performs genuine assembly: differential
   naturality and epi/mono cancellation, a finite-square reduction, zero-source
   equations, and componentwise comparison with the original scalarExtensionHom.
   This follows the finite-data affine argument of 09RE. Inspected the unit record
   sk-thm-picard-semicon (its realized arrays are currently empty); no unit route or
   realized step is removed. All public imports of the new modules support their
   signatures, and their sole private dependency import supports the planned descent
   proofs. The report names both old direct proof dependencies moved below the split
   statements and the removed direct import; neither is globally pruned. One upper
   hole is closed and two lower holes are added, so the net hole count increases by
   one; this delivery is explicitly a decomposition, not a completed mathematical proof.
5. **DAG agreement: pass.** Compared the existing node with the repository: changes
   are confined to proof, proof_deps and proof_origin. Its four steps match the actual
   Lean proof, including the private conjugation argument and the zero-source case.
   Read both new nodes: each has its exact Lean statement, source, self-contained
   hypotheses, complete prose proof, search records, creation metadata, blueprint
   ancestry, chapter/unit and lean record. Their planned dependencies are the existing
   finite-presentation descent statement and the Mathlib elementwise colimit criterion;
   the docstrings explicitly explain why the partial-order interface needs transport.

**Changes by the second reader:** appended this substantive review and recorded the
independent compilation, axiom, edge-case and search checks. No Lean or DAG repair was
needed. Removed temporary axiom-probe copies before delivery. The holes closed and
added remain exactly those listed under Proved and sorry left.
