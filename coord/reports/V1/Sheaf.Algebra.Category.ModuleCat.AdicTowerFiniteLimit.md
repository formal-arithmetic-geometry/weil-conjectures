## What changed

Replaced the sorry in `ModuleCat.adicTower_finiteLimit` with a compiling proof,
keeping its signature and public imports unchanged. Added two new modules:
`Sheaf.Algebra.Category.ModuleCat.AdicTowerCompletedFreeSurjection` and
`Sheaf.Algebra.Category.ModuleCat.AdicTowerFreeKernelCorrection`.

The proof obtains a completed finite free surjection, transfers finite generation
through `AdicCompletion.piEquivFin` and `Module.Finite.of_surjective`, proves all
projection surjections by shifting the tower and applying Mathlib's concrete
limit-projection theorem, and proves the projection kernel equality. For the
nontrivial inclusion it subtracts a global presentation-kernel correction and
uses `AdicCompletion.pow_smul_top_eq_ker_eval`. It constructs an explicit A-linear
restriction of q to avoid an induced scalar-action instance ambiguity.
The reverse inclusion follows directly from annihilation and A-linearity.

The completed free surjection needs only finiteness of level zero and no
Noetherian hypothesis. The kernel-correction theorem assumes an arbitrary given
surjective completed finite free map, and needs neither finiteness of T nor
Noetherianity. The parent uses its Noetherian hypothesis to obtain I.FG for
Mathlib's completion evaluation kernel formula.

The existing node copy records the actual proof route. The new nodes carry
source references, full proof plans and exact compiled Lean statements. No
existing statement, definition, visibility or target was changed.

## Proved and sorry left

Closed the original hole `ModuleCat.adicTower_finiteLimit`
(`lem-weil-pbc-adic-tower-finite-limit`). Its module has no sorry remaining.

Added two named holes, each in its own module with proof exactly `by sorry`:

- `ModuleCat.adicTower_completedFreeSurjection`
  (`lem-weil-pbc-adic-tower-completed-free-surjection`): generator lifting,
  nilpotent Nakayama, surjective presentation kernels and their limit surjection.
- `ModuleCat.adicTower_freeKernelCorrection`
  (`lem-weil-pbc-adic-tower-free-kernel-correction`): lift a finite-level kernel
  vector to a global kernel vector of a given completed free presentation.

This is a decomposition: one upper hole closed, two lower holes added (net -1).
It is not a sorry-free proof of the target closure. The two remaining theorems
are distinct parts of the source argument; neither restates the original
conjunction of finiteness, surjectivity and all projection kernel equalities.

Validation: all three modules compile together through lcompile.py without
warnings. The final proof contains no sorry or axioms of its own. Edge cases
checked mathematically before stating the lemmas: I=top forces every T_n, N and
the completed free source to be zero; I=bot makes all tower maps isomorphisms
and free completion evaluation injective, so the correction can be y itself;
d=0 and a surjective q force N=0. For an arbitrary non-finitely-generated ideal,
the correction argument factors each projected q through free residues by the
scalar residue equation on finitely many basis vectors, not by assuming a
completion evaluation kernel formula without I.FG.

## No longer needed

Removed direct proof imports of
`Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels` and
`Sheaf.RingTheory.NakayamaNilpotent` from the parent module. They remain planned
proof dependencies of the new completed-free-surjection module; tower exactness
also remains a dependency of the correction module. They therefore are not
claimed as globally pruned modules. No source-plan node or module can be removed
from the target closure by this decomposition: globally pruned modules: none.

The parent's direct dependency on tower exactness for projection surjectivity
is replaced by Mathlib's concrete projection theorem after an explicit final
shift. Its direct Nakayama dependency is moved to the presentation-construction
step. Every other original proof-dependency node is retained either in the
parent's proof or in a new node's proof. The parent's public imports are retained
because its statement uses those interfaces.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The existing dependencies prove tower
exactness and nilpotent Nakayama but do not themselves construct compatible free
presentations or the completed scalar comparison. Those two stretches of glue
are now named, independently compilable items. Finiteness of every level is
stronger than what the generator-lifting step needs: only level zero is used.

The named source file literature/stacks-project/coherent.tex is absent in this
local checkout. The proof of Stacks Lemma 087W was read at
https://stacks.math.columbia.edu/tag/087W; the new statements follow its completed
free presentation and K to K_n paragraphs. LeanSearch returned Internal Server
Error, recorded as unavailable; LeanFinder, Loogle and Mathlib/source/DAG grep
were used without finding an exact existing theorem.

## New nodes

`lem-weil-pbc-adic-tower-completed-free-surjection`, in
`dag/nodes/sec-proper-base-change/`, states the completed finite free surjection
construction. Its module is
`lean/Sheaf/Algebra/Category/ModuleCat/AdicTowerCompletedFreeSurjection.lean`.
It follows the generator-lifting and Mittag-Leffler paragraphs of Stacks 087W.

`lem-weil-pbc-adic-tower-free-kernel-correction`, in the same chapter, states
surjectivity from the global presentation kernel to the finite-level kernel,
expressed as a vector with the same free residue. Its module is
`lean/Sheaf/Algebra/Category/ModuleCat/AdicTowerFreeKernelCorrection.lean`.
It follows the final cokernel calculation of Stacks 087W. No change record is
needed: no existing interface was changed.

## Second reading by V1

1. Compared the parent module and existing node with the repository using diff.
   The existing theorem signature and docstring are byte for byte unchanged;
   there are no existing definitions or visibility changes. Only proof imports,
   the proof body, and the node's proof/proof_deps/proof_origin differ. No change
   record is needed. The two added modules are new interfaces, openly reported.
   Verdict: pass.
2. Compiled all three files with lcompile.py, and scratch copies ending with
   #print axioms for each of ModuleCat.adicTower_finiteLimit,
   ModuleCat.adicTower_completedFreeSurjection and
   ModuleCat.adicTower_freeKernelCorrection. Each lists only propext,
   Classical.choice, Quot.sound and sorryAx. The parent has no sorry; the new
   theorems have exactly their reported named holes. No forbidden declarations
   or hollow definitions occur. The existential presentation is eliminated
   within a theorem proof; no definition chooses data from its unproved
   existence statement. Verdict: pass as a decomposition, not a closed proof.
3. Read Stacks 087W at https://stacks.math.columbia.edu/tag/087W and both new
   Lean statements and node plans. The completed-free-surjection theorem needs
   only finite T_0: successor surjectivity lifts generators, composite kernels
   identify T_n/I T_n with T_0, nilpotence gives the finite-level surjections,
   and surjective relation transitions give the limit surjection. No
   Noetherian hypothesis enters that part. For kernel correction, B-linearity
   and the scalar residue hypothesis on finitely many basis vectors make p_n q
   factor through A^d/I^(n+1)A^d even for a non-finitely-generated I. Surjectivity
   of p_n and q gives the presentation surjection. Lifting and subtracting
   an I^(n+1) correction proves surjectivity of its relation transitions;
   recursively lifting relations then gives precisely z and its two equations.
   Thus this statement needs neither finiteness of the levels nor Noetherianity.
   Checked I=top (all terms zero), I=bot (all transitions invertible), d=0
   (surjective q forces N=0), and n=0 (first nonzero exponent). The two holes
   are distinct, strictly partial claims, not renamed copies of the parent.
   Independently searched LeanFinder for lifting relations of compatible
   quotient modules, Loogle for AdicCompletion.piEquivFin, and rg over
   lean/Sheaf, lean/WeilConjectures and Mathlib's completion sources. Found
   completion and inverse-limit ingredients, no duplicate arbitrary-tower
   theorem. Neither remaining hole admits a short closure using those tools.
   Verdict: pass.
4. Checked the finite-generation transfer, shifted-limit projection proof,
   subtraction of the corrected relation, Noetherian finite-generation use in
   pow_smul_top_eq_ker_eval, and the annihilation argument separately. The
   parent follows the source route and retains every relevant old dependency
   either directly or through the two new nodes. The module-completion-complete
   node's Mathlib match explicitly includes pow_smul_top_eq_ker_eval. The
   No longer needed section accounts for both removed direct imports; no
   globally pruned module is claimed. Read sk-thm-p1.json realized: this is a
   split below its realized steps, and no unit statement or route is bypassed.
   Verdict: pass.
5. Checked each node's Lean statement against its actual theorem signature,
   chapter/unit, source, new-node creation and blueprint ancestry fields,
   search records, and union of step uses against proof_deps. The parent node
   describes the proof as written; the new nodes describe their remaining
   constructions. Verdict: pass.

Changes in this reading: expanded the new docstrings and matching node proof
steps to spell out the composite-kernel induction and tower-projection
surjectivity. Replaced public Functoriality imports in both new modules by
public Algebra, which supplies their signature's completed ring/module and
evaluation interfaces; removed redundant public ModuleCat.Limits imports
already supplied by ChangeOfRings. No existing signature or proof was altered.
The delivery remains one original hole closed and two holes added (net -1),
with no globally pruned module.
