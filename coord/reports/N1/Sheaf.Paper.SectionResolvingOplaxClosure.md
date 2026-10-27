## What changed

Restored the three resolving-input hypotheses omitted from
ResolvingOplaxConstraints.section_resolving_oplax_closure, and proved that corrected
source assertion. Four applications of the existing total-tensor theorem give
the four nested resolving totals. The algebraic inverse-image presentation and
fixed pullComparison identify section pullback with algebraic inverse image;
the existing ringed-topos K-flat theorem and flat inverse-image theorem give
resolving pullbacks. Finite-list case analysis assembles ResolvingClosure.

All six added proof imports already belong to the original shared data module's
transitive import closure; the proof introduces no new module into that closure.

The sole consumer, Sheaf.Paper.SectionResolvingOplaxModelEdges, now passes its
already available P.property, Q.property and H.property. Its signature and all
other declarations and definitions remain unchanged. Added only private proof
imports and proved private helpers. The item node now records the corrected
statement and actual proof. Change record:
coord/changes/N1-section-resolving-oplax-closure-hypotheses.md.

## Proved and sorry left

The item originally had one sorry in
AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_resolving_oplax_closure.
The corrected assertion is proved with no sorry. This is a false-statement repair
with a complete proof of the source-correct statement, not a proof of the false
original unconditional assertion. No holes added, no statements split off, no
sorry in the delivery's Lean files. Existing imported theorem proofs retain their
own dependency status; none was replaced by a new assertion.

Validation: the item compiled in 12.1 s. The original direct importer was tested
against the changed item and failed at its line 63 with Application type mismatch:
the unapplied closure theorem has type sectionResolving P → sectionResolving Q →
sectionResolving H → ResolvingClosure, whereas the conjunction expects
ResolvingClosure. Passing the three existing properties is the entire adaptation.
Final two-file compile passed: the item in 16.8 s and the adapted direct importer
in 7.4 s, both below the 60 s limit.

## No longer needed

No existing imports removed and no modules withdrawn. The old proof dependencies
lem-pd-section-kflat-tensor-comparison and
lem-weil-pbc-site-derived-tensor-descent are not used as theorems: the total-tensor
closure theorem states exactly the closure facts needed. Their modules remain
transitively imported by the shared data interface, so no module pruning is
claimed. The section resolving property still comes from that interface.

The proof instead uses lem-pur-kflat-total-tensor-model, the existing algebraic
inverse-image presentation and flat inverse-image theorem, and the planned
ringed-topos K-flat pullback theorem. These are generic tools below the fixed
unit route; no unit is bypassed. No new maintainer tool approvals were added.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original version, repaired here): the earlier closure split
quantified arbitrary complexes while its parent and its own docstring described
resolving inputs. At identity pullback its second conjunct incorrectly forces
all module sheaves to be flat. Take Λ the discrete condensed integers, a
nonempty geometric point, and the constant Z/2 module in degree zero:
multiplication by 2 on the constant Z module is monic, but its tensor with Z/2
is zero and not monic. The source's flat-term K-flat hypotheses are essential.

Read Stacks sites-cohomology.tex, lemma-tensor-product-K-flat (07A2),
lemma-pullback-K-flat (0G7E), and lemma-pullback-tensor-product (07A4). The latter
explicitly replaces its inputs by flat-term K-flat complexes before using tensor
closure. The sole parent already supplies those hypotheses, so restoring them
preserves every mathematical use. The node's statement_change lists that sole
citer. The original section-kflat comparison theorem does not itself assert total
tensor closure; the already proved KFlatTotalTensorModel theorem does.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
