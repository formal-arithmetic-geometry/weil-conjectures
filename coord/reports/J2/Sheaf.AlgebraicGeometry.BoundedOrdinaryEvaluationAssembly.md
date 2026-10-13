## What changed

`AlgebraicGeometry.boundedOrdinaryEvaluation_degree` now has a complete Lean proof
from finite source and target biproduct comparisons and invertibility of each diagonal
block. The proof checks all matrix entries: the ordinary evaluation formula gives the
diagonal and vanishes for distinct indices; it then factors the degree map through the
biproduct of diagonal isomorphisms. Its existing signature is unchanged.

The existing evaluation definitions moved verbatim to the new
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationData`, publicly reexported by the original
module, to let the new statements import them without a cycle. All three new proof
imports in the original module are private. The five existing downstream users are
listed in `coord/changes/ordinary-evaluation-data-relocation.md`; none needs editing.

The finite target comparison is proved: the inverse extends the finite projections
by zero and lifts through the recorded Hom product. A private proved helper shows
internal Hom from a zero module sheaf is zero. Both inverse equations are checked.

## Proved and sorry left

Original hole closed (by decomposition):
- `AlgebraicGeometry.boundedOrdinaryEvaluation_degree`
  (`lem-pc-bounded-ordinary-evaluation-assembly`).

Also proved:
- `AlgebraicGeometry.ordinaryEvaluation_target_biproduct`
  (`lem-pc-ordinary-evaluation-target-biproduct`).

Two holes added, each strictly part of the finite-support argument:
- `AlgebraicGeometry.ordinaryEvaluation_source_biproduct`
  (`lem-pc-ordinary-evaluation-source-biproduct`): the canonical finite tensor
  decomposition; it has no evaluation-map or invertibility hypothesis.
- `AlgebraicGeometry.ordinaryEvaluation_diagonal_block`
  (`lem-pc-ordinary-evaluation-diagonal-block`): one diagonal component is
  invertible; it assumes no boundedness and makes no finite assembly conclusion.

No holes remain in the assigned module, the data module, or the target comparison.
This is a decomposition, not a claim that the target import closure is sorry-free:
one original hole closed and two smaller holes added, net minus one.

## No longer needed

No mathematical dependency or library module is pruned. The original seven public
imports now reside in OrdinaryEvaluationData, preserving their public availability.
The old direct proof dependencies `def-pc-tensor-complex-sheaves`,
`def-pur-hom-complex`, `lem-pc-sheaf-modules-tensor-closed`, and
`lem-sc-hom-complex-projections` are no longer direct assembly dependencies;
each remains used transitively by the source, target, or diagonal-block node.
No unit route changes.

The second reader removed the unused direct public imports of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree`,
`Mathlib.CategoryTheory.Preadditive.Biproducts`, and `Mathlib.Data.Int.Interval`
from OrdinaryEvaluationDiagonalBlock. The source and target comparison signatures
still need finite biproducts and integer intervals. MonoidalFree supplies their
finite-biproduct instance and is therefore a signature dependency there.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery: the relocation record omitted
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferentialSummand` from `## Users`.
Added it as unclaimed and checked its existing public assembly import; the unchanged
public reexport provides every relocated declaration used in its signature and body.
The downstream declaration-use scan found exactly these five existing users.
No Lean or DAG change is needed for this repair.

The earlier sandbox report described a missing compiled module. That blocker cleared:
the unchanged assigned module now compiles with the sandbox dependency overlay.
The original DAG's mathematical route is retained. Its steps had no already stated
finite tensor/Hom comparison or diagonal-component inversion theorem, so these three
parts now have precise Lean interfaces, with the Hom comparison proved here.

The local source checkout lacks literature/stacks-project/cohomology.tex. The source
was read on the Stacks Project pages for Tags 08DQ and 08DM. The finite decompositions
are the displayed sums in 08DQ and the finite-product argument in 08DM. LeanSearch
returned Internal Server Error and is recorded as unavailable; Loogle, LeanFinder,
and Mathlib/library grep found generic biproduct APIs but no specified comparison.

An additional scratch experiment proves the generic tensor-Hom naturality identity
and the singleton-product projection inversion. Applying that identity to the chosen
complex term repeatedly exceeded the single-file 60-second compile limit. Those
experiments are excluded from the delivery; the diagonal theorem remains exactly
`:= by sorry` with the complete source proof in its docstring. No progress is claimed
for scratch work, and no slow or partially holed proof is delivered.

Edge cases checked mathematically: b<a forces P=0, so the source and target are zero
and both finite biproducts are empty; a=b leaves one diagonal block; zero P, zero F,
and empty U give zero objects; no bound on F enters any new hypothesis. The diagonal
statement only needs the evaluation comparison for B=F^(r+n), exactly the instance
supplied in the assembly proof. The finite comparisons are uniquely characterized
by their displayed inclusion/projection equations, with no arbitrary witness data.

## New nodes

`def-pc-ordinary-evaluation-data` records the relocated, unchanged constructions;
there are no new mathematical definitions or hollow definitions.

`lem-pc-ordinary-evaluation-source-biproduct` isolates the finite-support tensor
coproduct reindexing. Its docstring gives the singleton-dual and zero-summand proof.

`lem-pc-ordinary-evaluation-target-biproduct` records the proved finite Hom product
comparison, characterized by its projection equations.

`lem-pc-ordinary-evaluation-diagonal-block` isolates the singleton dual projection
and tensor-Hom naturality calculation for one term, independently of boundedness.

Change record: `coord/changes/ordinary-evaluation-data-relocation.md`.

## Earlier second reading (a previous round; superseded)

1. **Existing interface and constructions: pass.** Read the repository module and
   diffed it with the assembly module. Compared the entire relocated block from
   `localEvaluationPreadditive` through `IsLocalOrdinaryEvaluation`, including bodies,
   byte for byte with OrdinaryEvaluationData: identical. The full signature of
   `boundedOrdinaryEvaluation_degree` is byte-identical. The relocation is declared
   in the change record; the existing seven public imports remain publicly reachable.
   No target or mathematical definition changes and no downstream adaptation is made.

2. **Proof and trust: pass as a decomposition.** Compiled all five modules in import
   order through lcompile.py. Read the assembly's two extensionality steps: the
   inclusion equation hs, projection equation ht, and hf give the matrix entry;
   i=j gives d i and i!=j gives zero because j-i!=0. The factorization conjugates
   the biproduct of asIso(d r), so its two surrounding maps and middle map are
   invertible. Read the target comparison's explicit f and g: hlim.fac proves
   their component equations; hbounded and homObj_isZero_left dispose of precisely
   the indices outside Icc a b. Both inverse equations are proved. Searched the
   delivered Lean for forbidden constructs and holes. The only holes are the two
   named, exactly `by sorry` split theorems; no data definition contains a hole.
   In a separate scratch module, printed axioms of all seven public data declarations
   and all four public theorems. The data and target comparison use only propext,
   Classical.choice, Quot.sound. The source, diagonal block, and assembly additionally
   use sorryAx, exactly as expected for the two reported remaining holes.

3. **Split statements, source, and existing results: pass.** Independently read
   [Stacks 08DQ](https://stacks.math.columbia.edu/tag/08DQ) and
   [Stacks 08DM](https://stacks.math.columbia.edu/tag/08DM), especially the dual
   term, displayed tensor/Hom sums, and finite-support product comparison. Checked
   all hypotheses against the new Lean and JSON statements. Source decomposition
   needs bounded P but neither evaluation nor hblocks; diagonal inversion needs
   just the single module comparison, without boundedness. Both are strictly
   parts of the argument, and neither restates the assembly conclusion. Each has
   its complete source proof docstring and matching node. For b<a the interval is
   empty and P and the dual are zero; for a=b only one summand survives. Zero P,
   zero F, and empty U cause no failure, and unbounded F is allowed throughout.
   Repeated searches with different queries via msearch.py: LeanFinder for
   "cochain complex tensor totalization zero terms finite coproduct reindexing"
   found total-complex inclusion/zero lemmas; Loogle for
   "CategoryTheory.Limits.IsLimit, CategoryTheory.IsIso" found general limit
   comparisons and binary terminal-factor results; LeanFinder for
   "naturality curry tensor Hom evaluation composed with map into dual object"
   found generic curry/uncurry naturality. None is either split theorem.
   Grepped Mathlib, upstream Homology/sheaf modules, and lean/Sheaf. Read
   HomComplexSingle, HomComplexSingleNatural, and FiniteFreeDerivedDualModel:
   their single-factor helpers are private and their public results concern
   a single source complex or finite-free derived models, not the specified
   dual projection and diagonal component used here. No public replacement
   closes either split statement directly. A bounded scratch attempt to reuse the
   saved factorization calculation, with transparency respected during elaboration,
   timed out at 60 seconds; it is excluded from the delivered modules and no hole
   was claimed closed by it.

4. **Top-down route and pruning: pass after import cleanup.** The finite matrix
   calculation is the original node's route, now expressed by three precise
   comparisons. No finite-free assumption was introduced. The source and target
   isomorphism witnesses are used only in a theorem proof; no arbitrary object is
   defined by choosing them. Their inclusion/projection equations determine their
   hom maps uniquely. The old four proof dependencies remain in the new nodes'
   transitive dependency closure; they are individually listed above. The unit
   sk-thm-picard-duality has unchanged realized.statement=[] and realized.steps=[[]];
   this item is not its key statement or a recorded realization. No unit step is
   bypassed. Removed three unused imports from the diagonal module and confirmed
   it still compiles; its remaining OrdinaryEvaluationData import is needed by
   the theorem signature. Kept the finite-biproduct/interval signature imports
   of the source and target modules.

5. **DAG agreement: pass.** Compared the existing assembly JSON with its repository
   version: only lean, proof, proof_deps, and proof_origin differ. Read all four
   new nodes; their declaration names, signatures, chapter, unit, source, creation
   records, and blueprint ancestry agree with the files and original item. Checked
   each proof_deps list equals the union of step uses. The assembly directly uses
   precisely source, target, and diagonal-block comparisons; the target node
   describes the full-product lift and zero-factor uniqueness proved in Lean.

Second-reading changes: removed the three unused diagonal-module imports and made
No longer needed explicitly list the old direct dependency ids and their continued
transitive use. No existing signature, definition body, or proof was rewritten.
The delivery remains one original hole closed by decomposition and two holes added,
with the target comparison genuinely proved; net minus one hole, not a complete proof.

## Second reading by J2

1. **Visible interface: pass.** Independently diffed the repository assembly module
   against this delivery. A byte comparison of the entire block beginning at
   `localEvaluationPreadditive` and ending at `IsLocalOrdinaryEvaluation` against
   OrdinaryEvaluationData succeeded, including definition bodies and docstrings.
   The full `boundedOrdinaryEvaluation_degree` signature is byte-identical.
   The relocation is declared in ordinary-evaluation-data-relocation.md, and all
   seven original public imports remain publicly reachable. Independently scanned
   declaration uses in lean/Sheaf: the five downstream users are exactly those in
   the repaired Users table. In particular OrdinaryEvaluationDifferentialSummand
   is present, resolving the 06:59 UTC landing return. No existing signature,
   mathematical construction, or downstream file is changed.

2. **Proof and axioms: pass as a decomposition.** All five delivered modules
   compiled in dependency order through lcompile.py, without errors or warnings.
   Independently compiled a scratch module printing axioms of the seven public
   data declarations and the four public theorems against the sandbox overlay.
   Data and target comparison have only propext, Classical.choice, Quot.sound;
   assembly, source comparison and diagonal block additionally have sorryAx.
   The source and diagonal block are precisely the two named whole-proof holes;
   there is no hole in a definition and no forbidden trust construct. Read the
   target comparison's f, g, hg, hfg and hgf: the full product universal property
   gives g, boundedness disposes of outside factors, and finite projection
   extensionality checks the other composite. Read the assembly's hs/ht/hf
   rewrites and both index cases: j-i is nonzero exactly off the diagonal, and
   conjugation by s and t yields the asserted invertibility.

3. **Split statements and search: pass.** Independently read Stacks
   [08DQ](https://stacks.math.columbia.edu/tag/08DQ) and
   [08DM](https://stacks.math.columbia.edu/tag/08DM): the dual degree formula and
   displayed tensor/Hom sums justify the two finite comparisons, and termwise
   evaluation justifies the diagonal calculation. Source comparison assumes only
   bounded P and specifies every surviving inclusion; diagonal comparison assumes
   invertibility only for B=F^(r+n), with no boundedness. Each is strictly a part
   of the original argument and carries a complete source proof and its own node.
   Checked b<a (empty interval and zero P), a=b (one summand), zero P, zero F,
   and empty U; none requires a bound on F. Fresh LeanFinder search for
   "coproduct total complex restrict nonzero summands bounded dual complex"
   returned total-complex inclusion and zero-inclusion APIs, not a finite dual
   decomposition. Fresh Loogle search for IsLimit and IsZero returned generic
   zero-limit APIs, not either specified comparison. Grepped the library for
   Hom-complex isomorphisms and tensor inclusions; read HomComplexSingle,
   HomComplexSingleNatural and HomTensorTotal. The former public comparisons have
   a single source, while this dual has a single target; their sole-factor
   helpers are private. HomTensorTotal is tensor-Hom currying, not the finite
   source decomposition or the specified diagonal map. No direct replacement
   or closure of a remaining hole in a few minutes was found.

4. **Route and pruning: pass.** This retains the original finite-matrix route
   and adds no finite-free or affineness hypothesis. Source/target comparisons
   are unpacked inside a theorem proof; their equations uniquely determine the
   comparison maps, and no definition chooses arbitrary existential data.
   Checked the old four direct proof dependencies against No longer needed:
   all four are listed and remain transitively used. No module is pruned.
   Checked sk-thm-picard-duality.realized (statement=[], steps=[[]]); this item
   is not a recorded unit realization and bypasses no step. The three proof
   imports of assembly are private. The new comparison signatures need their
   public finite-biproduct/interval imports; diagonal needs only its data import.

5. **DAG agreement: pass.** Parsed all five node files. The existing node differs
   only in lean, proof, proof_deps and proof_origin. For every node, proof_deps
   equals the union of step uses. Compared all three new theorem interfaces and
   their informal statements, source proofs, declaration names, module paths,
   creation records, chapter/unit and blueprint ancestry. Assembly cites the
   three comparisons it actually uses; target's proof describes the implemented
   full-product lift and the two inverse checks. The data node records relocation,
   with no new mathematical construction.

Changes in this reading: appended this independent review; no Lean or DAG repair
was needed. Confirmed the already repaired missing downstream-user record rather
than changing a correct proof. One original hole is closed by decomposition,
two smaller holes are added, and the target comparison is fully proved: the net
hole change remains minus one. Scratch axiom inspection is excluded from delivery.
