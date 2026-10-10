# lem-weil-pbc-formal-glueing-canonical-maps

## Worker report

Split the three clauses in seven steps. No new nodes, Lean attachments, or wanted sources. Stacks Remark 05EL names the canonical maps; the proof expands their construction through Algebra 07K0, 00DK and 00D2, reusing the reviewed tensor-localization node. `review_split.py` passes. `check_dag.py` finds no cycles and reports seven pre-existing unreachable nodes elsewhere.

## Review by K1

I read pinned Stacks `more-algebra.tex` Remark 05EL (`remark-glueing-data`) and `algebra.tex` Lemmas 07K0 (`lemma-universal-property-localization-module`), 00DK (`lemma-tensor-localization`), and 00D2, and checked their labels in `tags/tags`. The item states exactly the functorial localization, iterated-localization swap and tensor-localization maps used in 05EL, with no flatness or finite-generation assumption added. Its blueprint ancestor is the 0GS2 essential-surjectivity step of `thm-weil-pbc-finite-etale-lifting`; a whole-blueprint search for `can_i` and for localization/tensor/glueing found no duplicate. There are no new nodes under B1-B8.

Steps 1-2 evaluate localized maps on fractions and use the stated universal property in `def-weil-pbc-module-localization-away`; the scalar identities establish the asserted $S$-action, including agreement with the original $R$-action. Steps 3-5 use that $f$ and $g$ act invertibly in both iterated localizations, so that 07K0 extends $P\to(P_g)_f$ twice; the two fraction formulas visibly compose to the identity. Steps 6-7 use `def-weil-module-base-change` for the tensor map and `lem-weil-pbc-localization-tensor-over-base` for exactly the $R$-linear isomorphism claimed in (3). The fraction calculation supplies the $S$-linearity, which that leaf does not state. Each cited node supplies the fact used; the argument does not appeal to a node's proof.

I checked $f=0$ and $g=0$: localization is the zero module and the same inverse formulas remain valid. With $f=1$, the swap and tensor comparison reduce to the identity under the canonical identifications. No step assumes a nonzero module or a regular element. I requested no correction after the worker's final pass. The repository-wide DAG check still has seven unrelated reachability notices, without a new cycle or missing dependency.
