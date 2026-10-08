+++
id = "lem-weil-pbc-closed-immersion-proper"
kind = "lemma"
title = "Closed immersions are proper"
order = 908
uses = ["def-weil-pbc-scheme-conventions", "lem-weil-pbc-proper-composition"]
+++
A closed immersion [def-weil-pbc-scheme-conventions] is proper, and so is the
composite of a closed immersion followed by a proper morphism; in particular,
a closed subscheme of a proper scheme is proper over the base.

## Proof

A closed immersion is affine, hence separated, is of finite type (a
surjective ring homomorphism makes the target a finitely generated algebra
over the source), and is universally closed, since closed immersions are
closed maps and are stable under base change; all these notions are those of
[def-weil-pbc-scheme-conventions]. Hence a closed immersion is proper, and
the composite of a closed immersion followed by a proper morphism is proper
by [lem-weil-pbc-proper-composition]; in particular a closed subscheme of a
scheme proper over the base is proper over the base.
