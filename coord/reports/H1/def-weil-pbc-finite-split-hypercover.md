# def-weil-pbc-finite-split-hypercover

## Worker delivery

The source-first search found no exact declaration in
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for finite split etale
hypercovers, and no declaration carrying
`(blueprint: def-weil-pbc-finite-split-hypercover)`.  Searches covered
`hypercover`, `split hypercover`, `matching scheme`, and
`PreZeroHypercover`; the only related source uses are generic `PreZeroHypercover`
objects in `AlgebraicGeometry/Sites/{Fpqc,Proetale}.lean`, which do not state
this node and therefore are not attachments.  The source checkout was not
modified or built.

I marked the imported node split in
`dag/nodes/sec-curve-estimates/def-weil-pbc-finite-split-hypercover.json` and
added the existing general site Cech-complex node to `stmt_deps`.  No new DAG
node was needed: the statement itself introduces all remaining data (the
augmented simplicial scheme, finite matching limits, split decomposition,
finite-degree condition, truncation, refinement/homotopy relation, and the
alternating-face complex).  The statement's external notions are exactly the
existing scheme-conventions, etale-site, and general Cech-complex nodes.

The split report records the blueprint clauses realized and `same_as: []`.
No Lean attachment, WANTED source, or statement correction is reported.

## Review by H1

I checked the complete imported statement clause by clause against the
blueprint node and the cited DAG definitions.  The matching-scheme clause
introduces its finite-limit meaning and the displayed low-degree cases; the
covering and nondegenerate-summand clauses define the split etale condition;
the finite-degree and truncation clauses are self-contained; and refinement,
homotopy, and the alternating-face differential are explicitly defined.  The
general Cech-complex node supplies only the already-defined ambient complex
notion.  No source declaration states the item, so no attachment was made.
