## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-geometric-reducedness-separable-scalar-restriction.json` (statement; split; no Mathlib match), `dag/nodes/sec-trace-formula/lem-trf-geometrically-reduced-base-change.json` (new statement node; no Mathlib match), `dag/nodes/sec-trace-formula/lem-trf-separable-algebraic-diagonal-localization.json` (new statement node; no Mathlib match), `citations.json`, and this report. No Lean, compiler, Lake, build, or live-project file was written.

Attachments: none. I searched the read-only Lean source and upstream master for the item id, its source terminology, and the blueprint tag; no sorry-free declaration states this item. Existing Mathlib geometric-reducedness declarations were read, but none gives restriction invariance along a separable algebraic extension.

WANTED: none.

The item statement is retained exactly. It is Stacks Algebra Tag 0C2Y, whose proof explicitly uses Tags 030U, 034N, and 0C2X. I searched the whole DAG and blueprint for these tags and for the relevant tensor/localization statements. The existing `lem-weil-pbc-separably-generated-tensor-reduced` is the broader established DAG input for 030U and is cited as a tool; no duplicate 030U node was created. The two new nodes are strictly smaller: 034N proves reducedness of one tensor product with a geometrically reduced algebra, while 0C2X proves only the diagonal localization.

## Not duplicates

`lem-trf-geometrically-reduced-base-change` vs `lem-weil-pbc-separably-generated-tensor-reduced`: the former starts with geometric reducedness of the algebra and allows any reduced algebra as the other factor; the latter starts with a separably generated field extension and proves its tensor with a reduced algebra is reduced.

`lem-trf-separable-algebraic-diagonal-localization` vs `lem-weil-pbc-localization-base-change`: the former proves the multiplication map for a separable algebraic field extension is itself a localization; the latter is the general base-change theorem for an already given localization.

## Not duplicates

lem-trf-separable-algebraic-diagonal-localization vs lem-weil-pbc-finite-separable-multiplication-etale: the new node treats arbitrary (possibly infinite) separable algebraic extensions and proves the multiplication map is a localization; the existing node treats only finite separable extensions and concludes that the multiplication map is etale/smooth.

lem-trf-separable-algebraic-diagonal-localization vs lem-pur-finite-field-derived-tensor-summand: the new node is an ordinary-ring localization statement for arbitrary separable algebraic extensions; the existing node is a finite-field derived tensor direct-summand construction and does not state the diagonal localization.

## Review by Q53

I read the complete Stacks Algebra source around Tags 034N, 0C2X and 0C2Y, including the two-direction proof of 0C2Y. I also read the statements of every cited DAG node and checked the hypotheses one by one. In the forward item step, separable algebraicity of $k_1/k$ makes the empty family a transcendence basis and gives the separably generated hypothesis required by `lem-weil-pbc-separably-generated-tensor-reduced`; its conclusion says exactly that $E\otimes_k k_1$ is reduced. The new 034N node applies with this ring as the reduced factor and the item's $A$ as the geometrically reduced factor. The cited tensor-cancellation node supplies the explicit reassociation isomorphism, so reducedness transfers to $E\otimes_kA$.

In the reverse step, condition (1) gives reducedness of $E\otimes_kA$ for the extension field $E/k$. The tensor-cancellation statement gives the displayed identification of $E\otimes_{k_1}A$ with the base change of $E\otimes_kA$ along the multiplication map $k_1\otimes_k k_1\to k_1$. The new 0C2X node says that this map is a localization; the existing localization-base-change leaf says its base change remains a localization. I wrote out why a localization of a reduced ring is reduced, including the nilpotent fraction calculation. No hypothesis on finite generation, nonzero rings, or finite degree was added.

For the new 034N node I checked the statement against Tag 034N and the small cases $R=k$, $R=0$, $A=k$, and a finite product of fields. Its Mathlib searches (LeanFinder, Loogle, grep) found only the more general `IsReduced.tensorProduct_of_flat_of_forall_fg` and geometric-reducedness APIs, not this theorem. For the new 0C2X node I checked the finite separable primitive-element case and the directed union over finite subextensions exactly as in the Stacks proof; the zero and trivial extension cases are covered. Its searches likewise found only generic localization and tensor declarations, not the diagonal statement. Both nodes therefore remain unsplit statement nodes.

I verified every proof citation against the exact node statement and recorded the corresponding verbatim excerpts in `citations.json`. The item’s Mathlib searches were run with `msearch.py` and retained in `searches.jsonl`; they found no exact declaration. The blueprint ancestry is recorded from `lem-trf-local-term-locality`, and the item’s `split_report` records the established off-unit tool use of `lem-weil-pbc-separably-generated-tensor-reduced`. All proof steps are concise routine arguments; no hidden long lemma remains.
