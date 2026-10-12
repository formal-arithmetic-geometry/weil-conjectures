## What changed

The signature and visibility of `AlgebraicGeometry.Etale.etale_replacement_stage_diagram`
are unchanged. Its proof now obtains compatible coefficient systems, pulls the two new
systems to the cone, constructs α and β by conjugating inverse-image maps, proves their
naturality and zero composite, constructs the comparison short-complex maps with all
three inverse comparison components, and proves componentwise and functor-category short
exactness. The proof uses exactness instances already provided by the source library and
Mathlib's jointly conservative evaluation theorem.

Added three modules: `EtaleCoefficientInjectiveSystem` states the product/direct-image
injective embedding step; `EtaleSystemConeFunctor` states the single-system cone transport;
`EtaleCoefficientInjectiveCokernelSystem` PROVES the cokernel extension of an injective
system. The quotient objects are actual `cokernel (ai i)` objects. Their transitions use
`PreservesCokernel.iso` and `cokernel.map`; cancellation of the epic pulled-back quotient
projections proves identity and composition, and cokernel universal properties prove
stage short exactness.

Two scoped unused-variable linter settings address proof-valued existential binders in
these interfaces; all original binder names are retained. All four delivered modules
compile cleanly together (3.2 s, 3.1 s, 38.7 s, 8.8 s in the final sandbox check).
No existing statement or definition changed, and no adaptation was needed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.etale_replacement_stage_diagram`
(node `lem-weil-pbc-etale-replacement-stage-diagram`). Its proof contains no `sorry`.

Also proved the new
`AlgebraicGeometry.Etale.etale_coefficient_injective_cokernel_system`
(node `lem-weil-pbc-etale-coefficient-injective-cokernel-system`), including actual
cokernel objects, compatible quotient transitions, both quotient system laws and stage
short exactness.

Exactly two new holes remain:

- `AlgebraicGeometry.Etale.etale_coefficient_injective_system`
  (`lem-weil-pbc-etale-coefficient-injective-system`): compatible monic embeddings into
  injective coefficient systems; no cokernels or cone diagram.
- `AlgebraicGeometry.Etale.etale_system_cone_functor`
  (`lem-weil-pbc-etale-system-cone-functor`): pulling one arbitrary compatible system to
  one cone; no injectivity, cokernels, natural transformations or short exactness.

This is a decomposition, not an unconditional proof or a net reduction of holes:
one original hole closed, two holes added (net -1 before any subsequent pruning).
Every remaining proof is exactly `by sorry` in a named public theorem with its node and
source proof. There are no holes in definitions or private declarations.

## No longer needed

Removed from the item's proof imports:

- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`;
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`;
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already publicly available
  through `TopologicalInvariance`).

The first two remain mathematical dependencies of the unresolved product/direct-image
embedding step, recorded in its new node. The corresponding enough-injectives,
product-injectives and right-adjoint-preserves-injectives nodes are therefore not globally
pruned. Their direct edges from the parent are replaced by the injective-system route:
`lem-weil-pbc-site-sheaves-enough-injectives`, `lem-weil-pbc-product-injectives`,
and `lem-sp-right-adjoint-preserves-injectives`.

`lem-weil-pbc-site-pullback-abelian-exact` and module
`Sheaf.CategoryTheory.SitePullbackAbelianExact` are unnecessary throughout this proof
route: scheme-specific inverse-image exactness is already proved, represented by
`prop-weil-pbc-inverse-image-exact`. No assertion is made that other targets do not use
the removed modules. No unit-level statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan grouped the product construction, quotient construction, and cone
transport into very large steps; its recorded general site exactness theorem was
unnecessary for scheme inverse image. Existing exactness instances prove the required
short-exact pullback directly. No statement was found false.

The attempted direct cone construction had mathematically matching unit and associativity
proofs but exceeded the 60-second file limit. Profiling isolated about 33 seconds of kernel
checking for a transported inverse-image unit comparison; the whole construction still
timed out after attempts to abstract that comparison and the composition calculation.
It is left as the strictly smaller single-system cone lemma, with its complete argument
in the docstring and node. No timeout was bypassed and no definition was altered.

LeanSearch returned HTTP Internal Server Error; this is recorded as unavailable, not a
negative search. LeanFinder, Loogle, source searches and blueprint searches were performed.
The new statements were checked on a singleton index and the zero coefficient system;
the cone lemma also admits an empty index, where the asserted functor is the empty one.
The coefficient construction uses no affine, quasi-compactness, limit or colimit hypothesis.

## New nodes

`lem-weil-pbc-etale-coefficient-injective-system` is the product/direct-image injective
embedding portion of Tag 0EXZ. It is a remaining hole strictly smaller than the parent:
it asserts no quotient, cone diagram or short exactness.

`lem-weil-pbc-etale-coefficient-injective-cokernel-system` is proved from that embedding
and the cokernel universal properties, following Tag 04JC and the parent's stage proof.
It records the actual quotient construction and its system laws.

`lem-weil-pbc-etale-system-cone-functor` is the coherence portion of the parent's cone
transport step. It concerns one compatible system only and remains a named hole.
All three inherit the parent's chapter, unit and blueprint ancestor. The second reading adds the import-visibility record
`coord/changes/etale-replacement-stage-diagram-proof-import.md`; no declaration
interface changed.

## Second reading by F1

1. Compared the sole existing delivered module with its repository version using `diff`.
   The complete signature of `AlgebraicGeometry.Etale.etale_replacement_stage_diagram`,
   including all existential proof binders, is byte for byte unchanged. Its docstring
   is unchanged. There are no existing definitions or other declarations to alter.
   The three extra modules are genuinely new. Verdict: unchanged statement.

2. Independently compiled all four modules in import order: 3.3, 3.0, 37.4 and 8.0 seconds,
   without errors or warnings. Read the naturality calculations for α and β, the zero
   composite, all three components of s, and the use of objectwise evaluation to infer
   short exactness. Read the quotient construction: FR is an actual cokernel, φR uses
   its preserved universal property, and the identity/composition proofs cancel an
   epic pulled-back projection. A scratch module printing axioms of all four named
   declarations reports only propext, Classical.choice, Quot.sound and sorryAx.
   Source scan found precisely the two named `by sorry` theorems reported above and no
   forbidden declaration or holed definition. The existential witnesses are eliminated
   inside proofs of propositions; no public data definition chooses an arbitrary witness
   from a holed existence assertion. Verdict: valid conditional reduction, two open holes.

3. Read Stacks 0EXZ's product-of-direct-images construction and 04JC's exactness of
   abelian inverse image. The injective-system lemma is its embedding step, with
   normalized identity and composition, not a restatement of the stage diagram.
   On a singleton index it reduces to enough injectives; for a zero system take all
   zero sheaves. For the cone lemma, objects are c_i inverse image of F_i, and arrows
   are the composition comparison followed by inverse image of φ_f. Substitution of
   hidentity and the comparison unit law gives identities; substitution of hcomposition,
   naturality and comparison associativity gives composition. An empty index produces
   the empty functor, a singleton gives one pulled-back sheaf, and the zero system gives
   the zero functor. Neither lemma needs a scheme-limit or affineness hypothesis.
   Both docstrings supply their construction and verification, and both have nodes.
   Independently searched LeanFinder for coherent pullback diagrams on a cone, Loogle
   for injective monomorphisms, and grep for compatible embeddings and diagrams.
   Also searched lean/Sheaf and upstream SixFunctors. The existing
   `exists_compatible_injective_system` is a theorem about a strict small diagram of
   categories with specified precoverages and transposed right-adjoint cocycles;
   it is not directly this scheme-pullback system with canonical comparisons. The
   scheme-module embedding theorem concerns modules on a single fixed scheme.
   Neither duplicates these statements or gives a direct application. Verdict: the
   two holes are true, needed, separate parts of the argument; neither closed in a
   few minutes with the available declarations.

4. The upper proof closes its hole by combining the coefficient and cone steps with
   real naturality and short-exactness arguments; it is a decomposition, not a net
   decrease in holes. The proved cokernel module uses Mathlib's universal properties
   rather than a new holed exactness statement. All newly added proof imports are
   ordinary imports. Corrected the existing proof-only import of abelian functor
   categories to an ordinary import, and removed the new cokernel module's redundant
   `ShortComplex.Abelian` import (already public through `ShortExact`). Added the
   omitted removal of `UpperLowerStar.Defs` to the pruning report, and explicitly
   named the three replaced direct dependency edges. The unit sk-thm-p1's realized
   statement and four steps are untouched; this decomposition is below that level.
   The cone hole is a mathematical coherence step, not a split of a slow Lean proof
   across files; the attempted proof remains undelivered scratch work. Verdict: route
   retained, pruning report repaired.

5. Opened all four node files. Their recorded Lean signatures agree verbatim with
   the four declarations; every proof_deps set is exactly the union of its step uses.
   The parent uses the new coefficient-cokernel and cone nodes, comparison naturality
   and inverse-image exactness. The cokernel node describes precisely the implemented
   construction and epi cancellations. The two remaining nodes describe the complete
   unresolved arguments, with source, searches, creation record and inherited unit,
   chapter and blueprint ancestry. Only proof, proof_deps and proof_origin differ in
   the existing node. No change to dag/units is needed. Verdict: nodes agree with Lean.

The sole direct importer, `Sheaf.AlgebraicGeometry.EtaleLimitReplacementExactSystems`,
compiled unchanged against the delivered overlay in 16.5 seconds. The public-import
visibility repair is recorded in
`coord/changes/etale-replacement-stage-diagram-proof-import.md`; preflight requested
that record. No target meaning is affected.

Second reading changed only import visibility/redundancy, its change record and the pruning report; no
statement, definition or proof body changed. This remains one original hole closed and
two strictly smaller holes added, not an unconditional proof.
