## What changed

The target module imports the two one-variable compatibility modules using plain
proof-only imports. `AlgebraicGeometry.tensorHomEvaluation_natural` is reduced to
precomposition at M and postcomposition at L'. A private, fully proved categorical
lemma factors the internal-Hom map, interchanges the tensor maps, and reassociates.
The existing public signature, definitions and public import are unchanged.
The two new modules state the unresolved one-variable localization compatibilities.
The target node now records the actual two-component reduction.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.tensorHomEvaluation_natural` (1 of 1
original holes), conditional on the two component statements. Added two holes:

- `AlgebraicGeometry.tensorHomEvaluation_precomposition`, node
  `lem-pc-tensor-hom-evaluation-precomposition`.
- `AlgebraicGeometry.tensorHomEvaluation_postcomposition`, node
  `lem-pc-tensor-hom-evaluation-postcomposition`.

This is a decomposition, not a completed proof of derived evaluation naturality.
The delivery-local hole balance is 1 closed minus 2 added = -1; no positive net
progress is claimed. The private categorical lemma has no holes. No definitions
or arbitrary data witnesses are added.

## No longer needed

No original import or module is removed: the public uncurry-differential import
is needed by the statement's concrete evaluation map. No module is claimed pruned.
All eight old target proof dependencies cease to be direct proof dependencies of
the target and are retained in the component nodes' localization plans:

- `lem-pc-kflat-resolution`
- `lem-pur-hom-kflat-into-kinjective`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-pc-tensor-hom-uncurry-differential`
- `lem-sc-hom-complex-projections`
- `lem-pur-hom-complex-global-cochains`
- `def-pc-canonical-derived-tensor-hom-model`
- `def-pc-derived-pullback-tensor-comparison`

The canonical-map existence route considered during development is not a removed
baseline dependency: it was never imported by the original target module.

## Where the brief, the DAG or earlier work was wrong

Importing canonical-map existence would create a cycle through
`CanonicalTensorHomIdentityEvaluationCoherence`, which imports this target.
This prevents deriving the square from that canonical family at this point.
The first worker's target proof hit the default elaboration heartbeat limit;
raising it to 600000 still failed. The second reader replaced only the formal
factorization with a generic categorical helper, preserving the reduction.
The first worker omitted the target node update and described the target as
proved without explicitly counting the two added holes; both are corrected.

## New nodes

`lem-pc-tensor-hom-evaluation-precomposition` isolates dinaturality in the evaluated
complex, with the target M fixed. `lem-pc-tensor-hom-evaluation-postcomposition`
isolates naturality in the target complex, with L fixed. Each has its own module,
source, full natural-language localization proof and independent search record.
Neither merely restates the simultaneous two-variable target. No change record
is needed because no existing statement or definition changes.

## Second reading by B3

1. Compared the delivered target with the repository using diff and checked the
   text from `theorem tensorHomEvaluation_natural` to `:=` byte for byte: identical.
   No existing definition changes. New imports are proof-only; the existing
   public import stays. Verdict: unchanged interface.
2. Read the formal factorization and repaired its excessive concrete elaboration
   with a private generic lemma. The only sorries in the delivered modules are
   exactly the two named component theorems. No forbidden declarations, hollow
   definitions, or arbitrary witnesses are introduced. Compilation and axiom
   probe results are recorded below. Verdict: a genuine conditional reduction.
3. Read each new statement and its proof: these are the source-only and target-only
   squares, with exactly the parameters used in the target proof. Identity
   comparisons reduce to identity composition; with zero source or zero target
   the evaluation maps are zero. No noninvertible zero comparison is assumed.
   Checked Stacks 08DJ, 0A90 and 0A96 online. Repeated searches with the alternate
   terms evaluation counit, dinaturality, injective resolution, and internalHom_map
   using leanfinder, loogle and grep, and read Mathlib's closed-monoidal lemmas,
   upstream CochainComplex.InternalHom, and the sheaf localized chain-evaluation
   theorem. None supplies the exact fixed-model arbitrary-derived-isomorphism
   statement; the localization/roof step remains. The two lemmas are true,
   strictly one-variable parts, and both are used. Verdict: valid decomposition.
4. The proof takes the formal two-variable factorization after the two independent
   compatibilities. Canonical-family existence is cyclic; chain-map naturality
   alone does not identify arbitrary derived arrows. Retained the original
   statement-required import and used plain imports for both new proof lemmas.
   Listed every old direct proof dependency above. The unit
   `sk-thm-picard-duality` and its `realized` record are unchanged; this item is a
   lower-level auxiliary, not a realization of a unit step. Verdict: route kept,
   no baseline module pruned.
5. Updated the target node's proof, proof_deps and proof_origin to the actual
   factorization using the two new nodes. Checked both new nodes' mandatory
   fields, verbatim Lean statements, source, creation and blueprint origin.
   Their planned dependencies cover the remaining localization proof.
   Verdict: DAG matches the reduction and the remaining holes.

Changes by second reader: generic factorization helper and its concrete
instantiation; byte-identical signature spacing; target proof metadata;
independent search records; explicit hole accounting and pruning report;
this second-reading section; corrected the new module-level blueprint tags.
No public signature or definition changed.

Validation: all three modules compiled with the prescribed lcompile.py, with no
compiler warnings or errors. The repaired target compiled under the default
200000-heartbeat limit in 45.2 s. Scratch-copy `#print axioms` checks for all three
public theorems compiled successfully and reported exactly propext, sorryAx,
Classical.choice and Quot.sound. The scratch target check took 31.5 s. The
remaining sorryAx dependence is disclosed, not treated as an axiom-free proof.
