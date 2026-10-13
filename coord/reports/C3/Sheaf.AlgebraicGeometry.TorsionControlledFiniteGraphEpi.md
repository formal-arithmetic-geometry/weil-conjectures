## What changed

Repair of the landing-tool return at head 7c7b42fd7: removed the new private
`AlgebraicGeometry.stalk_injective` declaration from
`FiniteKernelPullbackCokernelAnnihilated`. Its three uses now apply the existing
public `RingedSpace.module_stalk_exact` theorem, together with Mathlib's
`ModuleCat.mono_iff_injective` and section evaluation's `Functor.map_mono`.
No duplicate injectivity statement remains, and no new import is needed.


Replaced the sorry in `AlgebraicGeometry.torsionControlledGraphFst_epi` with a compiling
reduction to closed-fibre surjectivity and a proved cokernel annihilator bound. Every
existing declaration and definition keeps its original signature and visibility.
Added proof-only imports of `FormalGraphFirstQuotientEpi` and
`FiniteKernelPullbackCokernelAnnihilated`; no public import changed.
Second reading also added the missing proof-plan imports of
`CoherentFormalModulesAffine` and `Mathlib.RingTheory.AdicCompletion.Exactness`
to `FormalGraphFirstQuotientEpi` (the affine module publicly imports the tilde dictionary).

The latter new module is fully proved. Its theorem applies to arbitrary module sheaves
on any scheme and to any discrepancy map into a finite ideal quotient. It needs only
the power-annihilation of the comparison cokernel, and proves the explicit bound
J^(s+n+1) on the graph-projection cokernel. The proof uses the pullback cokernel
monomorphism, the composition cokernel exact sequence, and the ideal-product stalk
formulas. Private helpers are proved and contain no sorry.

In the item, the final power-annihilated Nakayama step is fully proved. Quotient
naturality and cancellation make the cokernel's first quotient projection zero;
at every stalk IC=C and I^kC=0 imply C=0 by induction. Section extensionality then
makes the sheaf cokernel zero, and the categorical criterion proves epimorphy.

The remaining completion argument is stated in a separate new module, with its full
source-based proof in words. Unlike the item, it assumes no comparison torsion and
concludes only epimorphy onto F/JF. The two new node records and the updated item's
proof dependency records follow the delivered argument.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.torsionControlledGraphFst_epi`
(node `lem-weil-pbc-torsion-controlled-finite-graph-epi`) by decomposition, with a
complete Lean combination proof. No sorry remains in the item.

Added and fully proved `AlgebraicGeometry.finiteKernelPullback_cokernel_annihilated`
(node `lem-weil-pbc-finite-kernel-pullback-cokernel-annihilated`). No sorry remains
in its new module.

Exactly one new sorry remains:
`AlgebraicGeometry.formalGraph_first_quotient_epi`
(node `lem-weil-pbc-formal-graph-first-quotient-epi`). Its proof is exactly `by sorry`.
This is the closed-fibre part of the original argument, with no torsion hypothesis
and a strictly weaker conclusion; it is not the original theorem under a new name.

Hole accounting: one original hole closed, one new hole added. This delivery is a
decomposition, not a net reduction in holes. All three modules compile through
`lcompile.py --all` with no compiler warnings or errors.

## No longer needed

The duplicate private `AlgebraicGeometry.stalk_injective` helper is removed.
The proof directly uses the already imported public module-stalk exactness API.


No existing import was removed, and no module is globally pruned.
All three old direct `proof_deps` of the item were replaced by the two new
intermediate statements and the stalk/quotient formulas:

- `lem-weil-pbc-affine-tilde-gamma-adjunction`;
- `lem-weil-pbc-coherent-formal-modules-affine`;
- `lem-weil-pbc-completion-exact-finite-modules`.

These three nodes remain transitive dependencies of
`lem-weil-pbc-formal-graph-first-quotient-epi`; they are no longer directly used
in the item's combination proof. Its new module imports the affine dictionary
(which publicly imports the tilde dictionary) and exact finite completion.
The final combination and the cokernel-annihilation proof use no affine completion
machinery and no assumption on the comparison kernel. The item's existing kernel
hypothesis is retained unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned delivery repeated a stalk-injectivity statement already present as
`AlgebraicGeometry.Scheme.Modules.stalk_inj`. That existing helper is private,
so importing its module would not expose it. The repair removes our helper and
uses the existing public, more general `RingedSpace.module_stalk_exact` instead.
The original second-reading notes below describe the earlier delivery; this
repair supersedes their statement that the checked proof terms were retained.


The original DAG marked its away-from-the-closed-subset argument elementary. The
annihilator bound and the final stalkwise detection required substantial Lean glue;
that glue is now proved explicitly. No statement is disputed or changed.

The generic annihilator bound uses neither coherence nor Noetherianity. Only the
remaining closed-fibre step uses those hypotheses. Edge-case review includes the
zero ideal, unit ideal, n=0, zero modules and the empty scheme. For J=0 the finite
graph is the graph of the actual formal map; for J=1 its first quotient is zero and
comparison-cokernel annihilation already forces that cokernel to vanish. The generic
annihilator theorem also covers s=1 and imposes no condition on the discrepancy.

The literature files named by the existing node are absent from this read-only clone;
I read the official Stacks pages for Tags 0889, 05EK, 0CYV and 00DV. The new nodes
record the same project literature paths and exact tags. LeanSearch returned HTTP
500 for both new-node queries and is recorded as unavailable; Lean Finder, Loogle
and Mathlib source searches ran successfully.

The module-style exact-completion API exposes an abelian witness whose inherited
zero morphisms differ from the canonical full-subcategory instance. A direct proof
of the closed-fibre lemma would need to normalize that interface and formalize the
kernel/pullback and quotient comparisons. No interface change or forced adaptation
is included here. The unit `sk-thm-p1` and all its realized steps stay unchanged.

## New nodes

`lem-weil-pbc-formal-graph-first-quotient-epi`, in
`Sheaf.AlgebraicGeometry.FormalGraphFirstQuotientEpi`: the strictly partial closed-fibre
surjectivity statement, with one sorry. Its proof follows the original affine
completion plan and names the existing three dictionary/exactness dependencies.

`lem-weil-pbc-finite-kernel-pullback-cokernel-annihilated`, in
`Sheaf.AlgebraicGeometry.FiniteKernelPullbackCokernelAnnihilated`: a fully proved,
more general annihilator bound for a kernel-restricted pullback projection. Its
proof is independent of formal compatibility and preserves the same unit route.

No change record is needed: no existing statement, definition or public interface
changed, and no module held by another group was adapted.

## Earlier second reading (a previous round; superseded)

1. PASS: compared every delivered module with the repository. The two helper modules
   are new. In the item, all four existing definition bodies, every existing signature,
   and visibility are byte-for-byte unchanged. Only proof imports, proved private
   helpers and the original theorem body were added. No change record or forced
   adaptation is required. No data is selected from an unproved existence statement.
2. PASS: all three modules compile locally without warnings or errors. A source scan
   finds exactly the reported named `formalGraph_first_quotient_epi` sorry, no sorry
   in data, and none of the forbidden declaration forms. Scratch copies printed
   axioms for all delivered declarations, including private helpers. The graph
   definitions, both final Nakayama helpers, all annihilator helpers, and
   `finiteKernelPullback_cokernel_annihilated` use only `propext`, `Classical.choice`
   and `Quot.sound`. The split lemma and original theorem additionally use
   `sorryAx`, as reported. Thus this is a decomposition, not a completed original
   theorem or a net hole reduction.
3. PASS: independently read the closed-fibre proof against Stacks
   [0889](https://stacks.math.columbia.edu/tag/0889),
   [087W](https://stacks.math.columbia.edu/tag/087W) and
   [00MB](https://stacks.math.columbia.edu/tag/00MB). Exactness on finite modules
   preserves the completed pullback and kernel; the target discrepancy quotient is
   already complete, and the compatible pair (id, theta) is killed by that map.
   Its first projection is identity. Reduction modulo I then yields the claimed
   first quotient epimorphism. Checked J=0, J=1, n=0, zero modules and empty X.
   A further test over Z with I=(2), a=id and a'=multiplication by 3 has a formal
   inverse comparison: the graph projects onto 3Z, surjecting modulo 2 but not onto Z.
   This confirms why the split lemma legitimately drops torsion and keeps only the
   first quotient conclusion. The generic annihilator proof gives the product of
   the two outer cokernel annihilators in the exact composition complex, including
   s=1. Repeated Lean Finder, Loogle, Mathlib grep and direct searches of both
   library roots with different terms found no matching sheaf graph theorem.
   The remaining comparison proof is substantial, not a hole closable in a few
   minutes; its docstring and node give the complete mathematical reduction.
4. PASS after repair: inspected from the original theorem downward. The combination
   uses exactly the closed-fibre lemma, the fully proved annihilator bound, quotient
   naturality and the elementary power-annihilated Nakayama induction. Read the
   existing formal-exactness and cokernel-reflection APIs; neither provides the
   missing graph comparison directly. Removed each of the five proof imports of
   the annihilator module in separate scratch copies: each removal fails with a
   missing declaration, so all are necessary. The public CoherentFormalModule
   import supplies signature definitions. Added missing plain proof-plan imports
   to the holed closed-fibre module: CoherentFormalModulesAffine (which publicly
   supplies the tilde dictionary) and Mathlib's completion Exactness. Repaired
   `No longer needed` to enumerate all three replaced old direct proof dependencies
   while recording that they remain below the new closed-fibre lemma. No module is
   globally pruned. Read dag/units/sk-thm-p1.json: its statement, steps and realized
   records are unchanged; this split is below the unit level.
5. PASS after repair: the item's three proof steps and dependency union match the
   Lean combination. The two new nodes match their Lean statements, source-based
   proofs, dependency unions, chapter/unit and required creation/search records.
   Replaced whitespace-collapsed lean.statement fields of the two new nodes with
   verbatim multiline signatures. No existing node statement or statement dependency
   changed. Added the second reader's distinct searches to the new closed-fibre node.

Second reading changed only missing proof-plan imports, verbatim new-node Lean
signatures, search records and report dependency accounting. The checked proof
terms were retained. Hole accounting stays one original hole closed and one new
hole added; the separate annihilator theorem is fully proved.

## Second reading by C3

This reading checks the repaired delivery after removal of the duplicate private
stalk-injectivity theorem; the earlier reading above concerns the previous round.

1. PASS. Diffed the item against the repository and checked its declaration table.
   Every existing signature and visibility, all four definition bodies and existing
   docstrings are unchanged. The two other delivered modules are new. The only
   changed fields of the existing node are proof, proof_deps and proof_origin.
   No public import changed, no arbitrary data is chosen from an unproved theorem,
   and no statement change or forced adaptation needs a change record.
2. PASS. Compiled all three delivery modules with lcompile.py --all: no warning or
   error (16.4, 3.6 and 8.8 seconds). Regenerated scratch copies from the repaired
   sources and printed axioms for every declaration, including private helpers.
   The annihilator theorem, its helpers, the graph definitions and the two final
   Nakayama helpers use only propext, Classical.choice and Quot.sound. Only the
   named closed-fibre lemma and the original theorem additionally use sorryAx.
   A source scan finds exactly the reported named sorry and no forbidden forms.
   In particular the replacement uses module_stalk_exact itself; the duplicate
   stalk_injective helper is absent. This is one hole closed and one hole added,
   a decomposition with zero net hole reduction, not a completed original theorem.
3. PASS. Read the split closed-fibre statement, its docstring and its node against
   Stacks [0889](https://stacks.math.columbia.edu/tag/0889),
   [087W](https://stacks.math.columbia.edu/tag/087W) and
   [00MB](https://stacks.math.columbia.edu/tag/00MB). Exact completion on finite
   modules preserves the pullback and discrepancy kernel; the pair (id, theta)
   gives a section of the completed first projection, and its reduction modulo J
   gives the asserted epimorphism. This needs no torsion hypothesis and concludes
   only epimorphy onto F/JF, so it is strictly part of the original argument.
   Checked J=0, J=1, n=0, zero modules and empty X. Over Z with J=(2), a=id,
   a'=multiplication by 3, and theta its 2-adic inverse, the finite graph projects
   onto 3Z: it is surjective modulo 2 but not onto Z. Thus the weakened conclusion
   is material. The proved annihilator bound also handles s=1; its exact middle
   cokernel is killed by the product of the two outer annihilators, as in
   [0CYV](https://stacks.math.columbia.edu/tag/0CYV). Repeated Lean Finder, Loogle,
   Mathlib grep and searches of both library roots with distinct queries found
   no replacement graph theorem. The remaining affine comparison needs substantial
   kernel/pullback/quotient transport and is not a short proof repair.
4. PASS. Read from the original hole down through closed-fibre surjectivity,
   cokernel power annihilation and the proved elementary IC=C, I^kC=0 argument.
   The repaired proof obtains each stalk monomorphism from the existing public
   module_stalk_exact clause and evaluation.map_mono. Checked the formal-completion
   exactness and thickening-cokernel-reflection APIs; neither removes the missing
   graph comparison. Removed each of the five plain proof imports of the annihilator
   module in fresh scratch copies; every removal fails at its used declaration,
   confirming their necessity. The closed-fibre module's plain proof-plan imports
   supply its remaining affine dictionary/exactness route. No existing import or
   module is pruned. No longer needed already lists all three old direct proof_deps,
   now retained transitively below the split lemma. Read sk-thm-p1.json: its statement,
   steps and realized records stay unchanged, and this reduction is below unit level.
5. PASS. The DAG proof steps match the Lean reduction and the repaired annihilator
   proof. Verified each proof_deps is the union of its step uses; the two new nodes
   have required source, creation, blueprint, chapter/unit, search and Lean records.
   All lean.statement fields occur verbatim in their modules. The only remaining
   sorry has its named theorem, full proof in words and matching node.

Changes in this second reading: refreshed scratch axiom/import checks, added the
current independent search results to the new closed-fibre node and appended this
review. The repaired Lean proofs were correct and were retained unchanged.
