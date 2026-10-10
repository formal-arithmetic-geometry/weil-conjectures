# Delivery report

Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-field-artin-schreier-sequence.json`: item split into three proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node in every step.

Attachments: none.

WANTED: none.

The slopmaster2 source was searched for the item id and for Artin-Schreier declarations. It contains Artin-Schreier morphisms and covers, but no declaration of the field etale-sheaf exact sequence. The existing DAG was searched for the field kernel, etale local-surjectivity, standard-etale construction, geometric stalk exactness, and stalkwise mono/epi/exact criteria; all were already present, so no supporting node was created. The item statement and blueprint metadata were preserved.

## Review by K1

I checked the statement against the field Artin-Schreier paragraph used by `lem-sc-function-field-cd-one`: E has characteristic p, `F_p` is the constant sheaf, `G_a` is the etale structure sheaf, and the maps are inclusion and `x^p-x`. Step 1 uses only the structure-sheaf, constant-sheaf, and abelian-etale-sheaf definitions; additivity, functoriality, and `wp iota = 0` are the elementary calculation.

Step 2 uses the existing local-surjectivity criterion exactly as stated, then the standard-etale derivative lemma with derivative `-1`, the nonempty-geometric-fibres surjectivity lemma, and the two etale composition/open-immersion statements to construct the covering by `A_i[T]/(T^p-T-f_i)`. The hypotheses are checked: the quotient is finite type, the derivative is a unit, and each geometric fibre is a nonzero polynomial quotient.

Step 3 uses exactness of geometric stalks, the constant-sheaf geometric-stalk isomorphism, and the existing field Artin-Schreier-kernel leaf. It then applies the existing stalkwise mono, exactness, and epi criteria and the definition of short exactness. Each citation was read and its quoted sentence in `citations.json` is copied from that node's statement. The small case E=F_p was checked directly: `x^p-x` is zero on constants and the cover `T^p-T-u` supplies local lifts for every u.

