Files written:

- `lem-sc-torsor-h1-functoriality`, repaired statement split, no Mathlib match.
- `lem-sc-torsor-h1-boundary-representative`, statement-only, no Mathlib match.
- `lem-sc-torsor-h1-ext-pushout`, repaired statement-only node, no Mathlib match.
- `lem-sc-closed-pushforward-boundary-naturality`, statement-only, no Mathlib match.
- `lem-sc-torsor-h1-ext-pushforward`, repaired statement-only node, no Mathlib match.
- `citations.json`, verbatim statement citations for all four proof steps.

Attachments: none. The source declaration `CategoryTheory.Sheaf.Torsor.classH1_lifts` gives the boundary formula for a given short exact sequence, but does not assert that every torsor arises as the fibre of an extension. It therefore does not state the entire new boundary-representative node.

WANTED: `literature/stacks-project/cohomology.tex`, Lemmas 02FQ and 02UV, for `lem-sc-torsor-h1-functoriality` and all four new nodes. This checkout contains the literature indexes but not the Stacks source files. I read the official Stacks pages for tags 02FQ and 02UV directly.

The returned delivery used the proof, rather than the statement, of `lem-sc-torsor-h1`, cited the etale-only `lem-sc-ext-torsor` for a Zariski result, and put the whole second clause inside a new node. The repair removes that citation and conclusion. The two old helper statements now define their sheaf operations and have the full field set. The split follows the boundary-of-one construction of 02FQ and the exact closed pushforward and Leray comparison of 02UV.

Nothing remains unfinished in this one-level split.

## Review by F1

I read Stacks 02FQ, especially its free-abelian-sheaf pushout and boundary-of-one construction, and 02UV, which derives the closed-immersion cohomology comparison from exact direct image and Leray. For the new boundary-representative node, 02FQ supplies both existence of an extension for a torsor and its boundary class; its converse follows by the same lifting-torsor construction. For ext-pushout I checked the quotient formula on sections and the fibre over one. For the closed-boundary node I checked that exact direct image gives the morphism of long exact sequences, and that the Leray comparison is induced by the identification of global sections. For ext-pushforward I checked direct image of the fibre square and the pullback along the restriction map from the constant integer sheaf. None of these four nodes states either clause of the item.

Step 1 cites the boundary-representative statement for an extension of $T$, ext-pushout for its pushed-out short exact sequence, and the natural long exact cohomology sequence in the topological-cohomology definition for the commuting boundary square. Step 2 cites ext-pushout for the contracted-product fibre and the converse part of boundary-representative for its class. Step 3 cites boundary-representative for $[T]=\delta_E(1)$ and closed-boundary naturality for the image class of the pulled-back direct-image extension. Step 4 cites ext-pushforward for the $i_*T$ fibre and boundary-representative for its class. I opened each cited node statement; every quoted part in `citations.json` is copied verbatim from the relevant statement.

The Zariski site is fixed in every helper. Exactness of $i_*$ comes from `lem-sc-closed-immersion-pushforward-exact`, which applies to the underlying closed inclusion of topological spaces. The quotient of $i_*E$ is $i_*\mathbf Z_Z$, so Step 3 explicitly uses its pullback along $\mathbf Z_X\to i_*\mathbf Z_Z$. The direct-image fibre is calculated after that pullback. On the identity coefficient map, the pushout and contracted product recover $E$ and $T$; on the identity closed immersion, the pullback is the original extension; on an empty closed subset both torsor classes are trivial. The four helper statements were searched in the DAG, blueprint and Lean source before creation or repair. The two new nodes also record Mathlib searches. The earlier tautological sentence and the etale Ext citation are gone.
