## What changed

Repaired H2: restored the target node’s `lean.statement` exactly from the base
node, including its multiline formatting. Reverted both factorization options
`backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to `false`, as requested. The helper
and API rewrites remain the necessary proof adaptation; the earlier claims that
changed transparency settings were necessary are withdrawn.

Repaired H10 in the sandbox, preserving every existing signature and the fixed
coefficient-transpose morphism. All five previously delivered modules remain.
`PicardCoefficientTransposePasting` constructs the transpose through the typed,
irreducible `coefficientCounitTranspose`, with its proved defining equation and
pasting API in the same file. `TensorSinglePullbackComposition` constructs the
fixed `tensorSingleCoefficientMap`, with explicit shared sheaf categories and
proved defining-equation and composition APIs. `TensorCoefficientComparison`
gives the fixed chosen adjunctions small categorical types and a proved equation
showing the original isomorphism. The generic APIs keep the expensive definitions
folded when specialized to fibre products. No file is split to evade the limit.

The original construction is still the adjunction transpose of the fixed
base-change mate: the forced factorization adaptation unfolds the API equations
and uses the proved `coefficientMate_evaluation` identity. The transpose's type,
its lifts, and all chosen adjunctions remain unchanged. The public import of
`TensorSinglePullbackComposition` is now required by the definition's data.
The node route and definition change record are updated to the actual construction.

H2 validation: all five delivered modules compiled without errors or warnings
using the prescribed launcher: DerivedSquareVerticalPasting 26.4 s,
TensorCoefficientComparison 2.9 s, TensorSinglePullbackComposition 6.2 s,
PicardCoefficientTransposePasting 20.8 s, and
PicardDirectImageDerivedTransposeFactorization 28.7 s with both transparency
settings `false`. Every module stayed within the unchanged 60-second limit.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.picardCoefficientTranspose_pasting` by decomposition.
The new `AlgebraicGeometry.canonicalDerivedSquareComparison_vertical` is proved.
The defining-equation and composition APIs and both private naturality helpers
are proved; they add no direct holes.

Exactly one delivered declaration remains directly sorry:

- `AlgebraicGeometry.tensorSinglePullback_composition`
  (`lem-sc-tensor-single-pullback-composition`).

One original hole closed, one strictly smaller hole added: this remains a
one-for-one decomposition, with net zero holes before closure pruning. The
coefficient composition APIs and pasting theorem inherit this reported dependency.
There is no sorry in a definition, no new arbitrary existence choice, and no
changed target statement.

## No longer needed

Removed the original proof-only import
`Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare` and its direct
proof dependency `lem-pc-canonical-single-pullback-square`. The tensor-coherence
node retains `lem-pc-canonical-single-pullback-composition` as its ingredient.
The original derived pullback composition and module pullback adjunction remain
needed transitively; they are not claimed pruned. The direct public import
`Sheaf.AlgebraicGeometry.TensorCoefficientComparison` is also removed: the typed
coefficient module already publicly imports it. The five delivered modules
are all needed transitively. No additional module is claimed to leave the target closure.

The temporary lift wrapper, private specialized evaluation wrapper, and alternate
proof snapshots used for profiling are not delivered. The final construction uses
only its typed coefficient and counit data APIs and the two coherence statements.

## Where the brief, the DAG or earlier work was wrong

H10 was correct: the previous 48.6-second success did not establish a robust
60-second build. The returned version reproduced the timeout. Profiling found
about 40 seconds of kernel checking, concentrated in the specialized coefficient
conversion. Inferred single functors used the scheme-module presentation while
the coherence statement explicitly used the shared sheaf-of-modules presentation.
Merely changing unfolding tactics or the local let cleanup did not fix the cost.
The final repair changes the definition representation and gives it typed APIs,
checking coherence on general schemes before specializing to the fibre products.

The mathematical route is unchanged: projection equations identify the composed
lift; derived-square coherence and tensor-single coherence combine by naturality
on the counit. The realized cube unit statement and steps are untouched. Identity
maps, zero modules and empty schemes add no hypothesis; no single-pullback map is
inverted. Earlier whole-goal placeholder nodes remain removed.

## New nodes

The previous new nodes `lem-sc-derived-square-vertical-pasting`,
`lem-sc-tensor-single-pullback-composition`, and
`def-sc-tensor-coefficient-comparison` are retained. The first is proved; the
second carries the sole reported hole; the third constructs the fixed isomorphism.

`def-sc-tensor-single-coefficient-map` names the explicit composite of the fixed
single-pullback map and the single embedding of that coefficient isomorphism.
Its defining equation is proved by reflexivity and its composition API is proved
from the existing tensor-coherence declaration. It adds no hole and uses no
unproved existence witness. Its source, statement, Lean signature, dependencies,
edge cases and actual LeanFinder, Loogle, grep and unavailable LeanSearch searches
are recorded. It lives in the existing tensor-composition module.

Definition change record: `coord/changes/picardCoefficientTranspose.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization`
(unclaimed in the read-only claim snapshot) retains every signature and visibility.
The original final application `exact transpose_three_maps _ _ _ _` fails against
the changed definition because its result ends in the inverse-Hom expression,
while the new data is in the equal counit presentation. The adapted proof follows
that identity by adjunction naturality, fixed mate evaluation and the proved data
API equations. Those are the only added proof lines beyond the returned adaptation.
The untouched other direct importer is compiled against the delivery overlay.
The original-versus-adapted check and final timings are recorded below after checking.

H10 validation before the final dry run: the prescribed `--all` compilation passed
without warnings for all five modules: DerivedSquareVerticalPasting 38.8 s,
TensorCoefficientComparison 3.6 s, TensorSinglePullbackComposition 8.5 s,
PicardCoefficientTransposePasting 24.0 s, and the adapted
PicardDirectImageDerivedTransposeFactorization 33.5 s. The untouched other direct
importer, PicardDirectImageDerivedTransposePasting, compiled against the overlay
in 51.0 s. All launcher limits stayed at 60 s. The dry run rechecks the final
source after removal of the redundant coefficient-comparison import.

The original factorization passed against the compiled baseline in 29.8 s.
Against the delivered overlay it failed in 8.1 s at its original line 89:
```
error: typeclass instance problem is stuck
  Category.{?u.214, ?u.216} ?m.275
```
The adapted replacement retains `transpose_three_maps`, then follows its result
with the counit presentation. Its final added lines are:
```
  refine (transpose_three_maps _ _ _ _).trans ?_
  congr 1
  rw [coefficientCounitTranspose_eq, tensorSingleCoefficientMap_eq,
    Modules.tensorCoefficientComparison_eq]
  exact coefficientMate_evaluation _ _ _ _ _ _ _ _
```
The proved private evaluation helper uses adjunction naturality, the inverse-Hom
counit identity, fixed mate evaluation and associativity. Both factorization
transparency settings retain their original `false` values; the helper and API
rewrites suffice without changing those file-level options.
The signature comparison found no changed existing signature in either existing
module. Only the original necessary factorization adaptation is delivered.

The import-based axiom probe passed in 1.9 s. The transpose and all new data
constructions and defining equations, vertical square coherence, and adapted
factorization use only `propext`, `Classical.choice`, and `Quot.sound`.
The sole tensor-composition hole, its composition API and the pasting theorem
also use `sorryAx`, exactly as reported. There is no other axiom. The mandatory
dry run additionally probes every declaration in every delivered file.

Final dry run returned OK for commit `125910f1a3`: compilation, forced-adaptation
counterfactual checks, every-declaration axiom probes, and preflight passed.
The only expected outstanding review is the independent second reading; nothing
was pushed. The untouched direct importer was rechecked against the final
refreshed overlay after import pruning and passed in 58.0 s. Its earlier 51.0 s
check and the final check both used the unchanged 60-second launcher limit.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered target and forced-adaptation modules with the
repository versions. Existing declaration signatures and visibilities are
unchanged; the definition change is recorded in
`coord/changes/picardCoefficientTranspose.md`, and no target statement was
weakened or given extra hypotheses. Verdict: pass.

2. I compiled all five delivered modules with the prescribed launcher. The
source contains exactly one remaining `sorry`, in
`tensorSinglePullback_composition`, which is the named split-off node; there
are no forbidden declarations, hollow definitions, or unlisted sorries. The
reported axiom probes restrict proved declarations to the permitted axioms,
with `sorryAx` only through that split-off theorem and its dependent pasting
theorem. Verdict: pass.

3. The split-off theorem is a strict underived coefficient-composition lemma,
with a source, natural-language proof, matching node, and edge-case account;
it is not a restatement of the item. The new coefficient comparison and
single-coefficient definitions are explicit constructions, and their defining
equations are proved by reflexivity. Verdict: pass.

4. The proof uses the typed counit presentation, the derived-square vertical
coherence lemma, and the tensor single-pullback composition API. The old
canonical-single-pullback-square import is removed, while required public and
proof-only imports are retained. The report and node dependencies list the
pruned route; the realized cube unit route is preserved. Verdict: pass.

5. The DAG nodes agree with the Lean declarations: the target node records the
three actual proof ingredients, the vertical and tensor-composition nodes
record their implemented routes, and the definition nodes record their
constructions. The unit and chapter fields remain unchanged. Verdict: pass.

Changed during second reading: no Lean proofs, statements, definitions, or
node metadata required repair; only this section was appended to document the
review.

## Forced adaptations

### Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-a8bkrjau/lean/Sheaf/AlgebraicGeometry/PicardDirectImageDerivedTransposeFactorization.lean:89:8: error: typeclass instance problem is stuck
  Category.{?u.214, ?u.216} ?m.275

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Category` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.

(with the modules compiled into /tmp/forced-adaptation-a8bkrjau/.lbuild) [6.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by A4

1. Compared every delivered module with the repository versions. Existing declaration signatures and target statements are unchanged; the only definition change is recorded in `coord/changes/picardCoefficientTranspose.md`. Verdict: pass.

2. Recompiled all five delivered modules with the prescribed launcher after restoring both transparency settings to `false`; all compile without warnings and within the 60-second limit. The sole remaining `sorry` is the named `tensorSinglePullback_composition` split-off theorem. No forbidden declarations or hollow definitions occur. Verdict: pass.

3. Checked the split-off node and its docstring: it states the strictly smaller tensor coefficient composition lemma, with a source and edge-case rationale, rather than restating the target. The explicit coefficient and counit constructions contain no arbitrary existence data. Verdict: pass.

4. Traced the proof from the target through the typed coefficient map, vertical square coherence, and tensor composition API. The realized cube route is retained; the removed canonical-single-pullback import is genuinely unused. Verdict: pass.

5. Compared the Lean declarations with the DAG nodes and proof dependencies. The target node, new definition nodes, vertical coherence node, and tensor composition node agree with the implemented route and report. Verdict: pass.

Changed during this reading: restored `backward.isDefEq.respectTransparency` and `.types` to `false`, matching the repository baseline and the H2 validation record; appended this review. No proof or statement repair was otherwise needed.

## Forced adaptations

### Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ttf_tw02/lean/Sheaf/AlgebraicGeometry/PicardDirectImageDerivedTransposeFactorization.lean:89:8: error: typeclass instance problem is stuck
  Category.{?u.214, ?u.216} ?m.275

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Category` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.

(with the modules compiled into /tmp/forced-adaptation-ttf_tw02/.lbuild) [4.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
