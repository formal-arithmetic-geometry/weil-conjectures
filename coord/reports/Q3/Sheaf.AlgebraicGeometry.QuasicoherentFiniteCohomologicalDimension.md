## What changed

Proved `AlgebraicGeometry.Scheme.exists_quasicoherent_cohomology_bound` in
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteCohomologicalDimension` with its
signature and all public imports unchanged. The proof chooses a finite set of
Mathlib affine opens covering the top open, orders its subtype using equivFin,
and takes the cardinality as the uniform bound. The affine diagonal gives
pairwise affine intersections; finite infimum closure gives the Leray hypotheses.

Three private helpers construct actual site intersections, identify the site
complex with the source explicit abelian Čech complex, and prove vanishing above
the cover size using `alternatingCechComputes` and the finite cardinality argument.
All helpers are proved. Existing source Leray and its additive homology
identification give vanishing of ordinary H. Added the proof-only import
`Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison` to transport this to
the module right-derived cohomology in the statement. Updated the node proof,
proof_deps and proof_origin to record this bridge and the actual bound d=N.

The proof follows the second proof of [Stacks 01XI](https://stacks.math.columbia.edu/tag/01XI)
and the ordered comparison of [Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM).
These source pages were checked directly because the untracked Stacks tex sources
are absent on this machine. Checked the unit record sk-prop-av-cube: no realized
unit statement or step is bypassed. Empty cover, N=0, p=0, one-open cover and zero
coefficients are included: the generic vanishing helper works even for N=p=0,
and the main statement asks only p>N. No nonempty scheme hypothesis is needed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.exists_quasicoherent_cohomology_bound`
(node `lem-sc-picard-qcoh-finite-cd`). No sorry remains in the delivered module.
Added zero holes and zero new modules. This is a proof from existing declarations,
not a decomposition into new statements. Existing imported declarations remain
responsible for their own transitive dependencies.

The module compiles locally without errors or warnings through lcompile.py.

## No longer needed

None of the original imports, proof-dependency nodes or modules is pruned.
The affine-intersection node remains used through its Mathlib match, and both
`lem-pc-alternating-cech-computes` and `lem-pc-cech-computes` remain used.
No new affine-intersection, finite-cover or bounded-alternating-complex theorem
needs to be left to another worker: Mathlib and the proved private glue suffice.
The temporary explicit Mathlib QuasiCompact and EquivFin imports were removed
because their declarations are already available through the retained imports.

## Where the brief, the DAG or earlier work was wrong

The planned Čech comparison alone reaches the source library's ordinary H model,
whereas this statement uses module right-derived sections. The existing node
`lem-sc-module-cohomology-source-comparison` supplies the necessary additive
bridge; it is now in proof_deps. This is a general comparison tool from another
unit, used only to reconcile these existing cohomology models, with no change to
the unit route. The maintainer may record it as a tool use if required.
The original N-1 choice required treating empty covers separately; choosing N
satisfies the unchanged existential conclusion uniformly. No statement,
definition or visibility was changed, and no forced adaptation is needed.

## Second reading by Q3

1. **Interface: pass.** Compared the complete delivered module with the repository
   by `diff -u`. The sole existing declaration's signature is byte for byte
   unchanged. All three public imports are unchanged; the added source-comparison
   import is proof-only. No existing definition or visibility changed. The
   theorem docstring now describes the actual bound N and additive transport.
   There are no change records or forced adaptations to review.
2. **Proof: pass for local closure.** Independently compiled the entire file with
   lcompile.py, without errors or warnings. Inspected all three private helpers:
   intersections are actual infima, inclusions satisfy the product universal
   property, and identity component maps intertwine the two signed face sums.
   No sorry, axiom, unsafe, opaque, implemented_by, extern or hollow definition
   occurs in the delivered module. Compiled a scratch copy with explicit
   `#print axioms` for all four declarations. The two constructed definitions
   use only propext, Classical.choice and Quot.sound. The vanishing helper and
   target additionally use sorryAx through existing imported dependencies;
   therefore this delivery closes one local hole, but does not claim the target
   is globally proved under the three permitted axioms. The existential
   alternating complex is used inside a theorem proof, not to define an arbitrary
   object for downstream use.
3. **Split statements: pass, none.** No new public statement, module, node or hole
   is added. Checked the cardinality argument at N=0, p=0, N=1 and p=N: a
   strictly increasing tuple of length p+1 would force p+1 <= N, contradicting
   N <= p. Empty schemes and zero coefficient modules need no extra assumption.
   The bound is selected before F and is uniform. Independently searched with
   leanfinder for high-degree vanishing on quasi-compact semi-separated schemes,
   loogle for the finite-cardinality injection lemma, grep via msearch for
   vanishing/zero Cech cohomology, and rg over the library. No shorter existing
   theorem for the unchanged target was found; the injection lemma is already
   used by the proof.
4. **Route and pruning: pass.** The finite affine cover, affine intersections,
   alternating comparison and Leray comparison follow the old plan. The module
   comparison bridges the two pre-existing cohomology models. The equivalences
   compose from module cohomology through ordinary H to the zero abelian Cech
   homology; their injectivity proves subsingleton, hence IsZero. Each retained
   proof import is used, and each retained public import supplies the existing
   signature. No old proof dependency is unused, so No longer needed is complete.
   Checked dag/units/sk-prop-av-cube.json: its realized statement and step lists
   are empty, and this subordinate finite-bound argument bypasses no unit step.
5. **DAG: pass.** Compared the node versions: only proof, proof_deps and
   proof_origin differ. The three steps accurately describe the Lean code,
   including d=N, actual site intersections and the new additive bridge. The
   affine-intersection dependency is realized by its documented Mathlib match,
   isAffineHom_diagonal_iff. proof_deps is the union of the steps' uses. No new
   node fields are required.

Second reading changed only this report: added the independent checks and made
explicit the transitive sorryAx limitation. The proof and DAG needed no repair.
