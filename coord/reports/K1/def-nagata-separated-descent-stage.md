# Stage-1 report: def-nagata-separated-descent-stage

Files written:

- `dag/nodes/sec-nagata-compactification/def-nagata-separated-descent-stage.json`: definition, split; no Mathlib leaf.
- `citations.json`: empty, because the item is a definition with no proof steps.

Attachments: none. The source search found no sorry-free declaration defining the named stage or model. The related declaration `AlgebraicGeometry.Scheme.exists_isSeparated_pullback_snd` is the existence theorem recorded by the existing node `lemma-nagata-separated-descent-stage-exists`, not an attachment for this definition.

WANTED: none.

The imported node was already stated as the choice of a witness from `lemma-nagata-separated-descent-stage-exists`; I retained that statement and its existing dependency. The blueprint note says this bookkeeping is bypassed by the formalized route, but that does not make the definition itself a Lean declaration. The source theorem in `WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` (around lines 3449--3504) proves existence of a later separated stage, while the theorem around lines 3507--3530 proves the combined finite-presentation descent; neither defines `lambda_sep(X/S)` or a named descended model. No new node is needed because witness selection is the definition's elementary construction from the cited existence node.

## Review by K1

I read the item node, the unit record `sk-prop-nagata-sketch-approximation`, the chapter record, and the source Lean around `Scheme.exists_isSeparated_pullback_snd` and `Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`. The item statement matches the blueprint clause: it starts with a separated finite-presentation morphism and its finite-stage descent model, then chooses one witness from the existing existence statement and records its index and model. The statement dependencies are exactly `lemma-nagata-separated-descent-stage-exists` and `def-nagata-finite-presentation-descent`; I opened both nodes and confirmed that they state the witness and the starting model used here.

There are no proof steps, so `citations.json` is empty and there are no step-level citation quotes to check. I searched the project source by the item id and by the separated-descent terminology; only the existence lemma's blueprint tag was present. I also searched the DAG and blueprint for duplicate definitions and found only the distinct fixed-base and eventual separated-stage nodes. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; the LeanSearch service was unavailable and is recorded as such, while the other searches found no declaration defining this named construction. I checked the small logical edge case that the existence witness is nonempty by the cited lemma, so selecting one witness is valid; no extra mathematical hypothesis is introduced. The item was changed from `imported` to `split`, with its blueprint origin and search log filled in.

## Second reading by K1

- Item statement: checked against the blueprint definition clause and the existing existence node; verdict: agrees, with separated finite-presentation input and witness-selection output retained.
- Item dependencies: opened `lemma-nagata-separated-descent-stage-exists` and `def-nagata-finite-presentation-descent`; verdict: both state the witness and starting model used by the definition.
- Proof steps: none, because this is an unsplit definition whose construction is the choice supplied by its cited existence statement; verdict: no uncited proof step.
- New nodes: none; verdict: no duplicate, elementary, or Mathlib node was introduced.
- Edge cases: the existence node supplies a nonempty witness set, so choice is valid; the definition adds no hypothesis or conclusion.
- Blueprint/search metadata: checked the project DAG and blueprint search records; verdict: the imported definition correctly retains `blueprint.from: null`, and no Mathlib counterpart exists.

No mathematical statement or dependency was changed. The imported node's `blueprint.from: null` is retained as required for blueprint-origin nodes.

