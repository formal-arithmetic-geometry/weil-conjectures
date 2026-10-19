Files written:

- `dag/nodes/sec-six-functors/lem-coef-right-fibration-constant-right-kan.json` — item, statement split with four proof steps.
- `dag/nodes/sec-six-functors/lem-coef-right-fibration-fiberwise-kan.json` — new unsplit statement node; Mathlib no match.
- `dag/nodes/sec-six-functors/lem-coef-space-constant-diagram-limit.json` — new unsplit statement node; Mathlib no match.
- `citations.json` — verbatim statement quotes for every cited node in every item step.

Attachments: none. No declaration carrying `(blueprint: lem-coef-right-fibration-constant-right-kan)` or the exact item statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

WANTED: An archival copy of Kerodon tags 02ZL (Propositions 7.3.4.1 and 7.3.4.4, opposite/cartesian form) and 0309 (Proposition 7.3.6.1); these were read online at `https://kerodon.net/tag/02ZL` and `https://kerodon.net/tag/0309`.

The imported item had an empty proof. I kept its statement and dependencies, and filled its blueprint place with paragraph 2 of `prop-coef-integral-exceptional-adjoint.proof.md` (the fibrewise right Kan calculation used by the representable comma-colimit argument). The split introduces the general fibrewise Kan-extension theorem and the constant Kan-complex limit/evaluation theorem; neither restates the item, since the first allows arbitrary coherent diagrams on the total right fibration and the second is independent of Kan extension.

## Review by NJ

I read the item, the `sec-six-functors` chapter record, the `sk-prop-sf-biduality-general` unit record and its blueprint section, and the ancestor proof paragraph in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. I also read the complete statements of `lem-coef-right-fibration-section-limit` and `lem-coef-infinity-hom-bifunctor-functoriality`, which the item cites. The two new statements are self-contained: the first explicitly cites the right-fibration definition and states the fibrewise limits, counit and full mapping-space universal property; the second states the constant-space limit and its evaluation cone, including empty indexing shape and coherent naturality.

Step 1 applies the general fibrewise theorem to the constant diagram on $E$; its hypotheses are exactly that $p$ is a right fibration of small quasicategories and that the fibre diagrams have limits. Step 2 uses the constant-diagram node for each Kan fibre, then uses the section-limit statement that fibre transport has values the Kan fibres and acts by prescribed-target lifts; the Hom-bifunctor statement supplies coherent precomposition and higher simplices. Step 3 transports the counit and the mapping-space equivalence, with the evaluation component $x\mapsto\theta_b(x)(e)$, and cites the Hom-bifunctor naturality clause for all parameters. Step 4 checks the explicitly stated containing-universe and empty-fibre conventions. Every cited statement was opened and the corresponding sentence is copied verbatim in `citations.json`; the item `proof_deps` is the union of the step uses.

I tested the formulation on the identity right fibration, a right fibration over a point, an empty fibre and an empty total space: the formula reduces respectively to the identity, the mapping space from the fibre, the terminal mapping space from the empty Kan complex, and the unique empty diagram case. Mathlib searches were run for the item and each new node with LeanFinder/LeanSearch, Loogle and focused source grep; only ordinary-category Kan-extension/evaluation declarations appeared, so both new nodes remain unsplit.

What could not be finished: no archival Kerodon PDF is present in `literature/`; the online propositions are recorded as WANTED above. No Lean code or compiler was used.

## Not duplicates

lem-coef-right-fibration-fiberwise-kan vs lem-coef-right-fibration-constant-right-kan: the new node allows an arbitrary coherent diagram $G:E\to\mathcal S_{\mathcal U}$ and states the general fibrewise right Kan theorem; the item is only the constant diagram and adds the explicit $Q_p$ mapping-space formula.
lem-coef-right-fibration-fiberwise-kan vs lem-coef-pointwise-lan-mapping-property: the new node is the right Kan extension along a right fibration of quasicategories; the existing node is a pointwise left Kan mapping property for a different comma construction and opposite variance.
lem-coef-right-fibration-fiberwise-kan vs lem-weil-pbc-normal-domain-ring-equivalence: the new node is an infinity-categorical Kan-extension theorem; the existing node is an ordinary commutative-algebra equivalence of normal-domain and normal-ring conditions.
lem-coef-right-fibration-fiberwise-kan vs def-weil-pbc-normal-ring: the new node is a statement about right fibrations and limits of space-valued diagrams; the existing node only defines normal rings.
lem-coef-space-constant-diagram-limit vs lem-coef-right-fibration-constant-right-kan: the new node is the independent limit/evaluation characterization for any Kan complex and space, while the item applies it to fibres of a right fibration and proves the right Kan universal property.
lem-coef-space-constant-diagram-limit vs lem-coef-pointwise-lan-mapping-property: the new node identifies limits of constant diagrams in spaces; the existing node concerns mapping spaces for pointwise left Kan extensions and does not state this constant-limit result.
lem-coef-space-constant-diagram-limit vs lem-weil-pbc-normal-domain-ring-equivalence: the new node is an infinity-category of spaces result; the existing node is an ordinary algebraic statement about normal domains and rings.
lem-coef-space-constant-diagram-limit vs def-weil-pbc-normal-ring: the new node is a constant-space limit theorem with evaluation cone; the existing node is only a normal-ring definition.

## Second reading by NJ

- Item statement: checked against Kerodon 02ZL (Propositions 7.3.4.1 and 7.3.4.4, opposite form) and 0309 (Proposition 7.3.6.1), with the definitions of right fibration, coherent functor, fibre transport, and mapping space; verdict: correct, with the right Kan variance and evaluation component matching the source.
- Item step 1: checked against the complete statement of `lem-coef-right-fibration-fiberwise-kan`; verdict: the right-fibration and fibre-limit hypotheses and the whole mapping-space universal property are used exactly as stated.
- Item step 2: checked against the complete statements of `lem-coef-space-constant-diagram-limit`, `lem-coef-right-fibration-section-limit`, and `lem-coef-infinity-hom-bifunctor-functoriality`; verdict: the constant-fibre limit, contravariant transport, and higher naturality supply the claimed coherent identification.
- Item step 3: checked against the same three statements and the Step 1 universal property; verdict: repaired to define the transported counit explicitly and to derive the displayed mapping-space map componentwise by evaluation.
- Item step 4: checked against the empty-fibre and containing-universe clauses of the two cited nodes; verdict: repaired to spell out the empty-fibre and empty-total-space cases rather than refer to “the same argument.”
- New node `lem-coef-right-fibration-fiberwise-kan`: checked for self-contained quasicategory, right-fibration, fibre, limit, and coherent mapping-space notions; Kerodon 02ZL opposite form; verdict: genuine general lemma, not a restatement or duplicate, and Mathlib searches remain no-match.
- New node `lem-coef-space-constant-diagram-limit`: checked for self-contained Kan-complex and space notions, including $K=\varnothing$; Kerodon 0309 opposite form; verdict: genuine constant-diagram limit lemma, not a restatement or duplicate, and Mathlib searches remain no-match. Removed an unused `def-coef-infinity-fibrations` statement dependency.
- Duplicate audit: opened all nodes sharing tags 02ZL or 0309 and compared their statements; verdict: none states either new lemma or the item's coherent right-fibration result. The existing 0309 node is the pointwise left Kan mapping property with different variance.
- Source and blueprint audit: the Kerodon pages were read online and are recorded as WANTED because no archival copy is present. The current `main-20261015` ancestor proof file's paragraph 2 is a derived Hom-adjunction calculation and does not contain this imported right-fibration calculation; the split retains the imported item's stated route and records this blueprint discrepancy for maintainer review.
- Edge-case audit: identity right fibration, right fibration over a point, empty fibre, and empty total space all reduce to the stated identity, mapping-space, terminal, and unique-empty-diagram cases.
- Mathlib audit: the recorded LeanFinder, Loogle, and focused source-grep searches were rerun through `msearch.py`; ordinary-category Kan-extension hits do not state the quasicategorical right-fibration or constant-space results.

Changes made: removed the unused statement dependency from the constant-limit node; made counit transport and empty cases explicit in the item proof; corrected the constant-limit source place to identify the opposite right-Kan argument; preserved all worker sections, citations, searches, and duplicate-audit entries.
