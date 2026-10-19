# Stage-1 report: pur9-rg-def-phi

## Files written

- `dag/nodes/sec-smooth-purity/pur9-rg-def-phi.json`: repaired and split definition; no new nodes.
- `citations.json`: empty, because a definition has no proof steps.

## Attachments

No exact sorry-free Lean declaration was found. The source checkout contains only related regular-immersion declarations; none states this definition.

## WANTED

None.

## Source error

The imported statement referred to `pur9-thm-smooth-purity`, `pur9-lem-upper-shriek-composition`, `pur9-rg-lem-smooth`, `pur9-rg-lem-dimension`, and `pur9-cp-lem-twist`, but those IDs are not nodes in the current DAG. The corresponding current statements are `def-pur-smooth-purity-map` together with `thm-pur-finite-coefficient-smooth-purity`, `pur9-def-upper-shriek-composition` with `thm-sf-comp-composition` and `def-weil-pbc-adjunction-conjugate`, `lem-pur-regular-immersion-smooth-structure`, and `lem-pur-immersion-twist`. I also made the regular closed immersion, smoothness, coefficient ring, and pro-etale derived-category hypotheses explicit so the definition is self-contained. The mathematical composite and its direction are unchanged.

## Not duplicates

`pur9-rg-def-phi` vs `def-pur-smooth-purity-map`: the latter defines the smooth-morphism tensor map and its orientation for one morphism; this item composes the two structure-morphism orientations with the exceptional composition comparison for a regular immersion.

`pur9-rg-def-phi` vs `pur9-def-upper-shriek-composition`: the latter defines the general exceptional composition mate; this item specializes it to `a_Z = a_X \circ i` and includes the smooth-purity orientations and twist cancellation.

`pur9-rg-def-phi` vs `thm-pur-finite-coefficient-smooth-purity`: the theorem proves smooth purity maps are isomorphisms; this item defines the regular-immersion comparison assembled from those maps.

## Review by Q95

I read the item source `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-regular/pur9-rg-def-phi.md`, the chapter and unit records, and the current statements of every dependency. The regular-immersion and component dimension hypotheses come from `def-pur-regular-immersion` and `lem-pur-regular-immersion-smooth-structure`; the latter also supplies smoothness of both `a_X` and `a_Z` and the equality `m=N-c`. The finite coefficient and pro-etale setting are supplied by `def-pur-conventions` and `def-weil-pbc-proetale-site`, while `def-weil-exceptional-inverse-image` supplies the meaning of `Ri^!`.

The orientations `Pi_{a_X}` and `Pi_{a_Z}` are exactly the canonical orientations named by `def-pur-smooth-purity-map`; `thm-pur-finite-coefficient-smooth-purity` supplies their smooth-purity isomorphism context. The comparison `c_{a_X,i}` is the specialization of the mate defined by `pur9-def-upper-shriek-composition`; `thm-sf-comp-composition` states the compact-support composition map is an isomorphism, and `def-weil-pbc-adjunction-conjugate` states that its mate is therefore an isomorphism. Finally `lem-pur-immersion-twist` states precisely that Tate twists and even shifts pass through `Ri^!`, which is the final cancellation using `N-m=c`.

I checked the edge cases relevant to a definition: rank/dimension zero structure morphisms, identity immersion, empty components, and `m=0`; the displayed composite remains well-typed componentwise. The Mathlib searches were run for the project-specific comparison and found only unrelated generic smoothness or immersion declarations, so no Mathlib leaf or new node is appropriate. No proof steps exist, hence no citation entries are required.
