## What changed

Repaired reviewer X-a7def point 4 exactly: the raw theorem now takes the prescribed
completed morphism `θ` and equation `hθ`, immediately before its unchanged conclusion.
Its body remains `:= by sorry`, as the review's minimum statement repair specifies.
Replaced the invalid docstring by a complete affine formal-gluing argument: use θ for
the completed component, the inverses of a′ for the localized components, hθ for their
compatibility, exactness to descend, injectivity for the equation and overlap agreement,
and sheaf morphism gluing. For J=0, θ itself is the map. Unit-ideal and empty-scheme
cases are also explained. No Challenge declaration or definition changes.

`TorsionControlledCompletionHomLiftExists.lean` has only the forced proof edit at
line 41, appending `θ hθ` to its application of the raw theorem. Every signature,
visibility and import of that module is unchanged. The raw node now records the
verbatim repaired Lean statement, explicit hypotheses in its prose, and the corrected
four-step proof plan and origin. Its statement_change records the sole DAG citer.
Change record: `coord/changes/torsionControlled_completion_hom_lift_raw.md`.

Removed the prior sandbox's STATEMENT-DISPUTED annotation and five private
counterexample checks, reverting to the repository layout before making the requested
repair. The earlier zero-ideal counterexample no longer satisfies hθ, so it is not a
counterexample to this new statement. The deleted checks were not library declarations.
No new modules or nodes are introduced.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split off: 0. This is a statement
correction requested by the reviewer, not a proof or a decomposition.
The sole remaining delivered sorry is
`AlgebraicGeometry.torsionControlled_completion_hom_lift_raw`
(node `lem-weil-pbc-torsion-controlled-completion-hom-lift-raw`). Its named theorem
has the requested corrected signature and a complete natural-language proof.
`AlgebraicGeometry.torsionControlled_completion_hom_lift_exists` remains a complete
Lean proof from the existing named dependencies, with no sorry in its body.
Both delivered modules compile through lcompile.py in import order without warnings.

## No longer needed

No library imports, nodes or modules are pruned. The public import
`Sheaf.AlgebraicGeometry.CoherentFormalModule` remains needed by the raw statement.
The prior sandbox's proof-only MonoidalFree import is removed together with its five
counterexample checks; it was never an import of the baseline library module.
The raw node's proof_deps remains empty: its repaired prose argument is a plan for
the remaining named hole, not a claimed formal proof from undeclared dependencies.
The fixed blueprint unit route in `dag/units/sk-thm-p1.json` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The first delivery retained a false signature and merely marked it disputed. That
did not repair reviewer point 4. The raw decomposition had dropped θ and hθ even
though its parent binds both. The original raw prose relied only on localization,
which gives no data when J=0. The repaired signature restores the two omitted
hypotheses, and the proof plan now uses θ throughout rather than trying to recover
it from the localized arrows.

Read the primary sources [Tag 0889](https://stacks.math.columbia.edu/tag/0889)
and [Tag 05EK](https://stacks.math.columbia.edu/tag/05EK). The corrected argument
keeps the completed component alongside the localized components, as required for
formal gluing. Existing source-library searches from the earlier delivery found no
shorter proof. This repair makes no new claim of having formalized that argument.

The sole DAG citer is the completion-compatibility node. Its premises already
include θ and hθ, so it can still obtain raw existence. The separate assertion that
an arbitrary raw g has completion θ is not implied by this repair: for J=0 and
both arrows zero, hθ and hg put no constraint on g versus θ. That separate module
is held by another worker and requires its own repair; no unforced edit to it is
included here. The reviewer-requested Exists adaptation retains its existing use
of that dependency unchanged.

## Forced adaptations

`Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists` is unclaimed
in this checkout. It compiled against the original interface; after compiling the
repaired raw module, the original caller failed at line 41:

```
Tactic `rcases` failed: `x✝ : ∀ (θ : (completion X J).obj F ⟶
  (completion X J).obj F'),
  θ ≫ (completion X J).map a' = (completion X J).map a → ∃ g, g ≫ a' = a`
is not an inductive datatype
```

Changed exactly that line by appending the bound arguments `θ hθ`. The raw result
is now an existential rather than a function waiting for those arguments; the
existing obtain proof therefore works. No other caller lines changed. The adapted
module compiled against the repaired raw module. deliver3.py reruns the original
against both baseline and changed dependencies to check that this adaptation is forced.


## Second reading by D3

1. Compared both delivered modules with the repository versions. The only existing
   signature change is the declared restoration of θ and hθ to the raw theorem;
   the change record reproduces both signatures. Exists retains its signature,
   visibility and imports byte for byte and changes only the forced application.
   No definition or target changed. Verdict: passes as a statement repair.
2. Compiled both modules locally in import order without errors or warnings. Scratch
   copies with `#print axioms` for both declarations show only propext,
   Classical.choice, Quot.sound and sorryAx. The raw named theorem is the sole
   delivered body containing sorry; Exists still relies on open dependencies.
   No forbidden declaration or hollow definition occurs. Verdict: honest remaining
   hole, not a completed proof. Independently compiled the original Exists against
   the changed raw module and reproduced the reported rcases error at line 41.
3. No new split-off statement, node or witness-producing definition was added.
   Read the raw theorem's complete affine gluing argument against Stacks Tags 0889
   and 05EK. Checked J=0 (θ gives the morphism), J=unit (a′ is invertible),
   and the empty scheme. The repaired hypothesis excludes the previous zero-ideal
   counterexample. Verdict: the corrected statement and its prose argument are
   mathematically sound; zero holes are claimed closed.
4. Searched Mathlib with an independent leanfinder query about descent from adic
   completion and localizations and a grep query for formal gluing and completion
   fullness. Results were generic completion maps, not this descent theorem.
   Searched repository declarations using formal-gluing and hom-lifting terms;
   the surrounding existence/lifting results depend on this node and cannot close
   it without a cycle. The single public raw import is needed by its statement;
   Exists uses all three imports. Old proof_deps is empty and no baseline import
   was removed, so the pruning list is complete. Read sk-thm-p1's realized route;
   it is unchanged. Verdict: no short proof or pruning overlooked.
5. Compared the raw node's stored Lean signature with the delivered declaration,
   and checked its four proof steps and proof_origin against the docstring.
   Its empty proof_deps describes an unformalized source argument, not a claimed
   proof from a new dependency. The statement_change and change record declare
   the intermediate interface repair and its caller. Verdict: metadata agrees.

Second reading changed only this report: added the independent checks and verdicts.
No Lean code or DAG repairs were necessary.

## Forced adaptations

### Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists
Original against changed dependencies failed:
```
/tmp/forced-adaptation-3kth7flz/lean/Sheaf/AlgebraicGeometry/TorsionControlledCompletionHomLiftExists.lean:41:9: error: Tactic `rcases` failed: `x✝ : ∀ (θ : (completion X J).obj F ⟶ (completion X J).obj F'),
  θ ≫ (completion X J).map a' = (completion X J).map a → ∃ g, g ≫ a' = a` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-3kth7flz/.lbuild) [2.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
