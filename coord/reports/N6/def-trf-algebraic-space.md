# Stage 1 report: def-trf-algebraic-space

## Files written

- `dag/nodes/sec-trace-formula/def-trf-algebraic-space.json`: existing definition, audited and marked split; no new nodes.

## Attachments

None. No declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures` states this algebraic-space definition, and the source trees contain no `(blueprint: def-trf-algebraic-space)` declaration.

## WANTED

None.

## What was checked

The item is the definition used by the ancestor's polarized descent convention. I read the item, `sec-trace-formula` and `sk-i-curve-zero`, and the source passages in `literature/stacks-project/spaces.tex` (Tag 025Y), `spaces-properties.tex` (Tag 03G7), and `sites-modules.tex` (Tags 0409 and 0B8Q). Tag 025Y gives exactly a sheaf on the big fppf site, representable diagonal, and a surjective étale scheme atlas. Tag 03G7 defines the structure sheaf on the small étale site by `T ↦ Γ(T,O_T)`. Tag 0409 defines invertibility on a ringed site, and Tag 0B8Q identifies locally free rank-one modules with invertible modules in the locally ringed setting. The item's phrasing of a line module as locally isomorphic to the structure sheaf is the rank-one formulation required by the downstream descent nodes.

I checked every notion used by the statement against its cited DAG node. `def-pc-scheme` supplies schemes and morphisms; `def-weil-size-convention` supplies the universe bound; `def-pc-fppf-site` supplies the big fppf site and its coverings; `def-weil-pbc-sites-and-cohomology` supplies the generic site and sheaf-of-sets meaning; `def-pc-fibre-product` supplies scheme fibre products; `def-weil-etale-morphism` supplies étale morphisms; and `def-weil-sheaf-of-modules-category` supplies sheaves of modules and module morphisms. I added the generic site/sheaf and fibre-product dependencies because the original imported dependency list omitted those notions. The representability and surjectivity clauses are defined directly in the item's statement, so no child lemma is appropriate. The small étale site and structure sheaf are likewise part of this definition, following the cited Stacks passages.

The Mathlib searches were rerun with `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch. The hits concern schemes, étale morphisms, and scheme small étale topologies; none states algebraic spaces, representable diagonals/atlases, or line modules on algebraic spaces. The four exact queries and results are recorded in `mathlib_searches` and `searches.jsonl`. Edge cases checked include the representable algebraic space `h_U`, empty covering families only where the site permits them, and the fact that a line module is local rank one rather than merely a nonzero module.

## Review by N6

I checked the source and all statement dependencies as described above. The item is a definition, so there are no proof steps and `citations.json` is empty. I verified that each added dependency says the fact taken from it: the generic sites node defines sheaves on a site, and the fibre-product node defines the scheme fibre products used in representability and the localized site. I checked that no existing DAG node states the full algebraic-space definition and that no sorry-free project declaration attaches to it. I corrected the imported metadata by adding the omitted generic-site/sheaf and fibre-product dependencies, recording the four current Mathlib searches, and adding the required split report.

## What was wrong or incomplete in the imported node

The statement itself agrees with the Stacks definition and its downstream use. The imported `stmt_deps` omitted the generic sheaf notion and fibre products, and its Mathlib search records did not match the current required `msearch.py` log; both were repaired. No statement dispute or source error was found.

## What could not be finished

Nothing remains for stage 1. The definition has no proof steps or child nodes.
