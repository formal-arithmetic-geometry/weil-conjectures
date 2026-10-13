## What changed

Completed CategoryTheory.tower_limit_exact_of_coordinate_maps in
Sheaf.Algebra.Category.ModuleCat.TowerLimitExactCoordinateMaps. The proof establishes
injectivity by coordinate extensionality, middle exactness by unique coordinate preimages,
and surjectivity by recursive correction of lifts with kernel elements. Two proved private
helpers establish successor compatibility and realization of compatible families as limit
elements using Mathlib Types.isLimitEquivSections. The second reader removed the redundant proof-only import
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic; its declarations are already
available through ModuleCat.Limits. Both public imports support the signatures.

Corrected the missing naturality hypotheses hα and hβ. The original claim is false,
not a harder version of the source theorem. The sole caller
Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels already has both
hypotheses. Its only changed line passes them to the corrected theorem; every existing
signature and visibility in this adapted module stays identical.
Change record: coord/changes/tower-limit-coordinate-naturality.md.
No new modules, definitions, or nodes. The unit sk-thm-p1 statement and realized steps stay.

## Proved and sorry left

Closed the original hole of CategoryTheory.tower_limit_exact_of_coordinate_maps
(node new-tower-limit-exact-coordinate-maps), after the documented interface correction.
There are no remaining sorries in the item or the adapted caller, and no added holes.
This is a complete proof of the corrected source statement, not a decomposition.
The private helpers limit_succ_apply and exists_limit_of_succ are proved.

Local single-file compilation and compilation of both delivered modules in dependency
order pass without warnings. The delivery dry run also checks all declaration axioms.

## No longer needed

No original imports were removed. Removed the first worker's redundant added import
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic after a successful compile without it. The node's proof dependency on
lem-weil-pbc-tower-limit-exact-surjective-kernels, module
Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels, is removed:
that is the caller, so importing it would create a cycle. The proof needs only Mathlib
and directly implements the elementary coordinate argument. This removes the proof edge,
not the caller from the target closure. No whole module is claimed pruned.
The node's statement dependency remains unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original signature): hU and hV alone do not make α and β commute
with transitions on arbitrary coordinate elements. Counterexample over Z: F is the zero
tower, G has Z at each level with zero strict transitions, H is the constant Z tower,
α=0 and β=id. Each coordinate sequence is short exact; lim F=lim G=0, lim H=Z.
U=V=0 obey hU and hV, and F transitions are surjective, but V is not surjective.
The corrected signature explicitly assumes the commuting squares already required by
[Stacks 03CA](https://stacks.math.columbia.edu/tag/03CA) and
[Stacks 02N1](https://stacks.math.columbia.edu/tag/02N1).
The recursion specializes the correction-of-lifts argument in
[Stacks 0598](https://stacks.math.columbia.edu/tag/0598).

The earlier sandbox attempt had already added those hypotheses and a compiling direct
proof, but lacked the caller adaptation, node correction, change record, and report.
This delivery completes those requirements. The old DAG pointed back to the caller;
its proof and proof_deps now describe the actual direct proof.

Searches run: LeanFinder for short exact inverse limits (no exact generic theorem;
AdicCompletion.map_exact is specialized); Loogle for Types.isLimitEquivSections
(found its equivalence and evaluation lemmas); grep for limit exactness and sections
(found no shorter full theorem). Source-library and Sheaf searches locate only this
item and its caller for this coordinate formulation.

## Forced adaptations

Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels is unclaimed in this
checkout. Its original compiles on the shared baseline. Compiling it against the corrected
coordinate module fails at line 117 with Application type mismatch: the argument hshort
has the coordinate short-exact type but is expected to have the transition-naturality
of α type. Change only that line, adding existing hα hβ before hshort.
The adapted module compiles with the corrected dependency. No other proof edits,
imports, helpers, signatures, or visibility changes are made in the adapted module.

## Statement corrected

The corrected node explicitly requires transition compatibility, as the source does.
The only DAG citer is lem-weil-pbc-tower-limit-exact-surjective-kernels. Its statement
holds unchanged: it already assumes hα and hβ. Its Lean proof requires exactly the
forced two-argument adaptation above. All 278 transitive downstream modules appear
in the change record; the only direct user needs adaptation and the others retain
identical statements. No target signature or definition changes.

## Second reading by K2

1. Compared both modules against the repository with diff. The only existing signature
   change adds hα and hβ to the coordinate theorem, explicitly declared in the report and
   coord/changes/tower-limit-coordinate-naturality.md. All other signature bytes and
   visibility are unchanged. Confirmed the stated Z counterexample: zero strict G
   transitions force every limit coordinate to zero, while H has nonzero constant
   sections; the zero F transitions are surjective. Stacks 03CA requires commuting
   squares and 02N1 requires a sequence of inverse systems. The correction restores
   those hypotheses. The sole caller already assumes both and changes only its call.
   Compiled the original caller against the corrected dependency: precisely the reported
   type error at hshort occurs. The adapted caller compiles. No target or definition changes.
   Verdict: pass, as a documented correction of a false intermediate statement.
2. Independently compiled both delivered modules in import order without warnings.
   Scratch #print axioms for the coordinate theorem and both private helpers gives only
   propext, Classical.choice, Quot.sound. No sorry or forbidden declaration occurs in
   either delivered module. The recursive choices are inside a proved theorem and use
   proved coordinate surjectivity and proved hstep; no data is taken from an unproved
   existence theorem. Reviewed the signs in the correction b_prime-alpha(a_prime),
   successor orientation, n=0 initialization, and compatibility for arbitrary n≤m.
   Zero modules and constant towers satisfy the corrected argument. Verdict: pass.
3. There are no split-off statements, new nodes, or additional holes. The two private
   helpers are proved. Repeated LeanFinder with compatible sequences and kernel bonding
   maps, Loogle with the fully qualified section-equivalence name, and rg with inverse
   limit/short-exact variants. No shorter theorem matching the independent module
   universes was found. The proved AddCommGrpCat ML theorem would require converting
   towers and short complexes and handling universes; it is not a shorter route.
   Verdict: pass.
4. The proof closes injectivity, middle exactness, and surjectivity directly using Mathlib
   limit extensionality/sections and recursive lift correction. Removed the redundant
   added ConcreteCategory.Basic import after compiling a scratch copy without it.
   Public imports provide the statement's module limits and Function.Exact vocabulary.
   The sole old proof dependency is recorded under No longer needed: it is the caller,
   not a lemma invoked by this proof. No whole-module pruning is claimed. Checked
   dag/units/sk-thm-p1.json realized: this node is below the fixed unit steps, and no
   realized node or route is bypassed. Verdict: pass.
5. Read the old and delivered node side by side. Its updated statement and Lean record
   include precisely the naturality assumptions, and its four proof steps match the
   helpers, coordinate injection, unique kernel preimages, and recursive correction.
   Empty proof_deps agrees with the direct Mathlib proof. proof_origin names the cited
   source specialization. statement_change preserves old fields and lists the sole DAG
   citer with holds:true. No new node schema applies. Verdict: pass.

Second reading changed only the redundant added proof import and this report; the proof,
corrected signature, caller adaptation, change record, and node were retained.

## Forced adaptations

### Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels
Original against changed dependencies failed:
```
/tmp/forced-adaptation-qv77lo7a/lean/Sheaf/Algebra/Category/ModuleCat/TowerLimitExactSurjectiveKernels.lean:117:16: error: Application type mismatch: The argument
  hshort
has type
  ∀ (n : ℕ), Function.Injective ⇑(α n) ∧ Function.Exact ⇑(α n) ⇑(β n) ∧ Function.Surjective ⇑(β n)
but is expected to have type
  ∀ (n : ℕ) (x : ↑(F.obj (Opposite.op (n + 1)))),
    (ConcreteCategory.hom (G.map (homOfLE ⋯).op)) ((α (n + 1)) x) =
      (α n) ((ConcreteCategory.hom (F.map (homOfLE ⋯).op)) x)
in the application
  tower_limit_exact_of_coordinate_maps R F G H α β hshort

(with the modules compiled into /tmp/forced-adaptation-qv77lo7a/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
