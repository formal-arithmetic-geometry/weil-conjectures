# Delivery report: `lem-weil-pbc-closed-immersion-unit-quotient`

## What changed

The node now has a complete Stage 1 split. Its proof follows Morphisms of Spaces, Lemma 04CJ(1), with the stalkwise local algebra supplied by Modules, Lemma 08KS. The argument treats points outside the closed image, points on the image, the stalk formula for module pullback, the tensor-with-a-quotient calculation, and the global sheaf conclusion. No new node was necessary; every non-elementary dependency is an existing DAG node.

## Review by F1

I checked the statement against the cited source: for a closed immersion, the unit from a module to pushforward of its pullback is the quotient by the ideal action. The outside-image case correctly uses the vanishing pushforward stalk and the fact that the ideal is the whole structure sheaf there. At an image point, the cited closed-pushforward-stalk node supplies the local ring and module identifications, while the closed-immersion definition supplies surjectivity with kernel the ideal stalk. The cited module-stalk-pullback node gives the tensor description and identifies the unit with `m |-> m tensor 1`. The remaining algebra is the standard isomorphism `M/KM ~= M tensor_R R/K`, and the proof explicitly gives both directions and identifies the image ideal stalk. The final use of the stalkwise surjectivity and isomorphism criteria is appropriate, and naturality follows from the adjunction unit and multiplication map. The proof dependencies stay within the `sk-thm-p1` route and no existing node or Stacks tag is duplicated.

## Checks

`tools/review_split.py`, `tools/check_dag.py`, and `tools/preflight_delivery.py` were run on the clean one-commit branch before delivery.
