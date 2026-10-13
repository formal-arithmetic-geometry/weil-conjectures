## What changed

Proved `free_complex_extend_family` in Sheaf.Paper.FreeComplexExtendFamily after
correcting its false intermediate interface by adding the necessary hypothesis
`ha₀ : δ 0 ≫ a₀ ≫ η = 0`. Added proof-only Mathlib imports
Mathlib.Algebra.Category.ModuleCat.Projective and
Mathlib.Algebra.Category.ModuleCat.Abelian. Each adjacent-pair step uses
ShortComplex.Exact.liftFromProjective and liftFromProjective_comp; dependent
Nat.rec assembles the infinite family. Both files compile without warnings.

Adapted the sole caller, Sheaf.Paper.FreeComplexMapsToResolution, to prove the
new condition from its existing base-lift equality and hδ0. Its statement and
visibility are unchanged. Updated the two DAG proof records and the corrected
node's lean.statement and statement_change. No new module or node is needed.

Change record: coord/changes/free-complex-extend-initial-compatibility.md.
The unit sk-thm-p1 route stays intact; this intermediate recursive-comparison
lemma does not realize a unit statement or one of its fixed steps.

Searches actually run via msearch.py: LeanFinder queried chain-map extension and
returned ProjectiveResolution.liftFSucc and related resolution constructions;
Loogle on ShortComplex.Exact.liftFromProjective returned unknown identifier;
grep found the exact lifting primitives and their use in Mathlib's resolution
comparison proof. Read the primitive signatures and copied their recursive
argument rather than requiring the source complex to be exact. Read Stacks
Tag 00LS, proof of (1), at https://stacks.math.columbia.edu/tag/00LS because the
referenced local algebra.tex is absent from this read-only checkout.

## Proved and sorry left

Closed: `free_complex_extend_family` (node
lem-weil-pbc-free-complex-extend-family), with the explicitly corrected signature.
This is a complete proof of the true corrected statement, not a proof of the
false original statement. The proof depends only on Mathlib and standard Lean
recursion, with no Sheaf theorem imports and no newly introduced holes.

Holes added: none. Sorries left in either delivered module: none.
`free_complex_maps_to_resolution` remains proved with its original signature;
its existing dependency on `free_complex_base_lift` is unchanged and outside
this item's scope. The dry-run axiom probe checks both delivered modules.

Edge cases: zero terms, zero ring, and finite resolutions padded by zero require
no separate branch. Projective lifting permits all of them. No assumption of
exactness on F, surjectivity of η, finite rank, or nonzero modules is added.
The counterexample and necessity calculation below check the corrected boundary.

## No longer needed

None. No original import removed and no planned node or module pruned.
The original node had no proof dependencies. The proof now records the existing
Mathlib leaf lem-weil-pbc-free-module-projective; exact projective lifting is
provided by the already-public Mathlib exactness import. No additional Sheaf
intermediate lemma is needed. The caller keeps its existing dependency imports.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original free_complex_extend_family omitted the
augmentation compatibility of a₀ and is false. Over ℤ, let N=N' 0=ℤ, η=id,
higher N' terms zero, and d=0. Let F 0=F 1=ℤ, higher F terms zero, δ 0=id,
higher δ=0, and a₀=id. The original conclusion at i=0 would say 0=id.
The augmented target is exact (ker id=0; higher target terms vanish), and every
source term is free; both differential zero-composite conditions hold.

The original node's assertion that both zero-composite identities alone imply
the first obstruction vanishes is incorrect. For i=0 it also needs
δ 0 ≫ a₀ ≫ η=0. Any compatible family implies that condition via hd0.
The source has it because a₀ lifts π ≫ φ and δ 0 ≫ π=0. The earlier caller
ignored hδ0 with `have _ := hδ0`; the forced adaptation now uses it.
Only the false intermediate interface is corrected. No target statement or
unit route is weakened or changed.

## Forced adaptations

Sheaf.Paper.FreeComplexMapsToResolution (unclaimed): original against the new
dependency failed at line 58 with `Tactic rcases failed`: the result of the
old call is now an implication requiring the missing condition, not an
existential. This was reproduced by compiling the original source against the
sandbox .lbuild overlay. The changed lines prove hstart by rewriting ha₀,
associativity and hδ0, pass hstart in the call, and remove the now-redundant
`have _ := hδ0`. Adapted file compiles. Every existing signature, public import
and visibility in this file is unchanged. deliver3.py independently performs
the original-baseline and original-overlay compile checks.

## Second reading by V2

1. Compared both delivered modules with the repository by diff. Verdict: the
   only interface change is the recorded, necessary ha₀ hypothesis in
   free_complex_extend_family. Independently checked the ℤ counterexample:
   target exactness holds at every term, yet the old degree-one equation says
   zero equals the identity. The added condition is necessary by composing
   that equation with η. The caller's signature, visibility, and imports are
   byte-for-byte unchanged. Its proof adaptation uses exactly its existing
   augmentation condition; no target or definition changes.
2. Compiled both modules locally in import order without warnings. Inspected
   every proof, including the definitional equality between the next pair's
   first map and the current pair's second map. Verdict: valid recursion,
   no sorry, axiom, unsafe, opaque, implemented_by, or extern, and no data
   chosen from an unproved theorem. Scratch copies with #print axioms verify
   both declarations use only propext, Classical.choice, and Quot.sound.
3. No statements are split off and no new declarations or nodes are added.
   Verdict: the corrected statement covers zero modules, the zero ring,
   arbitrary free ranks and resolutions padded by zero; projective lifting
   has no exceptional branch. Independently searched using msearch grep
   for liftFromProjective|liftFSucc and rg for comparison/extension language.
   Read Mathlib's lifting primitives and ProjectiveResolution.liftFSucc:
   the latter requires an exact source resolution, absent here, and cannot
   replace the present direct recursion.
4. Read from the target intermediate theorem downward. Verdict: the direct
   Mathlib lifting route is appropriate, both new imports are proof-only
   (projectivity instances and ModuleCat abelian structure), and all existing
   public imports supply signature notions. No old proof dependency exists
   to prune. Inspected sk-thm-p1 realized: this intermediate node realizes
   none of the fixed unit steps, and the caller and unit route remain intact.
5. Compared both node records to Lean. Verdict: proof steps, dependencies,
   corrected lean.statement, statement_change and sole citer agree; the
   free-module projectivity dependency is an existing Mathlib leaf. No new
   nodes need schema review. Change record includes old/new interfaces,
   necessity, unchanged downstream meaning and the forced caller adaptation.

Second-reading changes: credited the caller's proof adaptation in proof_origin;
 retained the schema-required "V2 stage 2" statement_change author (preflight
 requires that form even for a stage-3 interface correction);
 appended this independent review. No Lean proof repair was needed.
The corrected intermediate theorem is proved, with zero new holes; this
 delivery does not claim to prove the false original statement.

## Forced adaptations

### Sheaf.Paper.FreeComplexMapsToResolution
Original against changed dependencies failed:
```
/tmp/forced-adaptation-_396qwh4/lean/Sheaf/Paper/FreeComplexMapsToResolution.lean:58:9: error: Tactic `rcases` failed: `x✝ : δ 0 ≫ a₀ ≫ η = 0 →
  ∃ α, α 0 = a₀ ∧ ∀ (i : ℕ), α (i + 1) ≫ d i = δ i ≫ α i` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-_396qwh4/.lbuild) [1.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
