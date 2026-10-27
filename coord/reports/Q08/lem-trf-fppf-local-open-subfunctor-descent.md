# Stage-1 delivery: lem-trf-fppf-local-open-subfunctor-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fppf-local-open-subfunctor-descent.json: statement item, split into eight proof steps; no exact Mathlib match.
- citations.json: verbatim statement excerpts for every use in every proof step.
- searches.jsonl: actual Mathlib searches, retaining the command's records.
- report.md: this report.

## Attachments

None for the item. Searching the live WeilConjectures source for the exact blueprint tag, open subfunctors, fppf and local representability found no declaration with all its hypotheses and conclusions. Representability.lean proves Zariski local representability and Picard open-subfunctor statements, not this assertion about arbitrary fppf sheaves. The existing dependency lem-weil-pbc-open-subscheme-fpqc-descent is already attached to AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc; its source proof was read and its DAG audit is closed.

## WANTED

None. All sources used are present locally.

## Corrections and route

The imported statement is correct and is unchanged. Its source field cites spaces.tex with tags from three different files; the proof now gives each actual document and label. The imported node had no proof. The eight steps supply its argument rather than move a clause to a new node. The item's existing blueprint provenance and created record are retained; whole-blueprint searches for open subfunctor, subfunctor descent, fppf covering, fpqc covering, 03N0 and 022C found no exact blueprint duplicate. The nearest ancestor remains lem-trf-local-term-locality, through the supplied etale-relation-finding-opens chain. The chapter and sk-i-curve-zero unit were read; this generic sheaf-descent tool does not replace their contracting-correspondence route.

The fppf-to-fpqc passage uses the existing lem-pc-fppf-affine-refinement, not the existing 022C node lem-weil-pbc-fpqc-finer-than-etale, whose statement is only about small etale covers. The affine-refinement tool is explicitly declared in split_report.tool_uses. The other nontrivial tool, compatible open descent, is already Lean-closed. No maintainer fields, unit records, Lean files, repository files or launcher files were edited.

## Unfinished work

None within this stage-1 item. This delivery supplies natural-language proofs, not Lean code or a build.

## Not duplicates

No new nodes. In particular, the existing lem-weil-pbc-open-subscheme-fpqc-descent supplies exactly Tag 03N0, and the existing lem-pc-fppf-affine-refinement supplies exactly the needed finite affine refinement. Neither is recreated. The Picard open-subfunctor blueprint nodes concern a specified Picard functor; none states the present arbitrary-sheaf descent assertion.

## Mathlib searches

Read the five actual queries in this sandbox's searches.jsonl and their returned hits. The first semantic query about a monomorphism of fppf sheaves becoming an open subscheme after a locally surjective scheme map returned LocalRepresentability and monomorphism/base-change lemmas. The second phrasing about a subsheaf on a test scheme and descending compatible opens again returned Zariski local representability. Loogle with IsOpenImmersion and Presheaf.IsLocallySurjective found the same Zariski results. LeanSearch also returned FlatDescent results, which require an already given scheme morphism; they cannot construct the scheme representing our fibre product. Reading Mathlib/AlgebraicGeometry/Sites/Representability.lean shows the Zariski sheaf hypothesis and the already representable open immersions. The source grep also found Fpqc.lean:66, fppfPrecoverage_le_fpqcPrecoverage, which supplies the cover-comparison fact but not the item. I retained the item's earlier logged search records rather than pretending to have rerun them; the new actual searches are appended with their exact query texts. No new Mathlib leaf is claimed.

## Review by Q08

I read Stacks spaces.tex Tag 02WU (lemma-finding-opens), including the local representatives, overlap-open equality, descent, and both directions of the representing-property proof. Its original assertion concerns quotients of equivalence relations. Our node assumes directly the local pullback square that the quotient proof constructs, so I marked the proof origin as agent and wrote the corresponding generalization explicitly. I also read descent.tex Tag 03N0 (lemma-open-fpqc-covering) and topologies.tex Tags 022C (lemma-zariski-etale-smooth-syntomic-fppf-fpqc) and 021P (lemma-fppf-affine). For open factorization and base change I read schemes.tex Tag 01HI (lemma-restrict-map-to-opens) and Tag 01JY (lemma-base-change-immersion). No SGA source is used.

Step 1 uses the actual universal property in def-pc-fibre-product, the open-immersion base-change statement in lem-weil-pbc-open-immersion-base-change, and the unique factorization statement in lem-weil-pbc-morphism-factors-through-open-subscheme. Evaluating the assumed isomorphism and using sectionwise injectivity constructs precisely the unique section needed. Step 2 compares the two overlap opens by applying that criterion to their inclusion maps, rather than infer equality from pointwise equality in the sheaf. Its citation def-weil-open-immersion says that an open subscheme has the restricted structure sheaf, so equal underlying opens are equal open subschemes.

Step 3 cites def-pc-fppf-site for flatness and joint surjectivity, def-weil-pbc-sites-and-cohomology for base change of covers, the base-change-open lemma to identify the inverse-image open, lem-pc-fppf-affine-refinement for finite affine opens over every affine open of the target, and def-weil-pbc-fpqc-covering for the exact resulting condition. Each cited statement was opened. This verifies the fpqc hypothesis required by step 4 without assuming any individual covering morphism is quasi-compact. Step 4 then cites the full statement of lem-weil-pbc-open-subscheme-fpqc-descent, which has arbitrary schemes and covering families and gives both existence and uniqueness, exactly what this step uses.

Step 5 cites the sheaf equalizer and covering base-change axioms from def-weil-pbc-sites-and-cohomology. It writes out equality of the local G sections using injectivity of alpha, glues those sections, then checks their image equals the specified F section using separatedness of F. Thus it invokes no unstated theorem about descent of membership in a subsheaf. Step 6 cites the same site definition and def-pc-fppf-site for joint surjectivity, and the open-factorization node for the unique global morphism into the descended open. The image argument chooses a preimage of each point; it does not assert that an arbitrary immersion admits such factorization.

Step 7 writes down the maps in both directions of the sectionwise bijection and checks naturality by the uniqueness already proved; its open-factorization citation supplies the uniqueness of the map into the open. Step 8 cites the covering base-change axiom, the open-base-change lemma, and the description of open subschemes. It proves independence by mutual factorization and checks the base-change isomorphism on each test map using the unique G section. The final use of q's local-surjectivity hypothesis is explicitly for every pair (T,a), so no scheme or algebraic-space presentation hypothesis was added to F or G.

For delivery-errors B through E, I checked self-contained meaning, TeX escaping, existing definitions, actual source labels, exact citation statements, all hypotheses at each application, no cycles introduced, and no omitted compatibility hidden in words such as transports. The citations file copies statements verbatim. All eight steps have fewer than 1000 characters, so no step crosses the 2000-character long-step threshold; each elementary step is a direct evaluation, inclusion argument, or explicit use of the sheaf equalizer and earlier steps. The non-elementary affine-refinement and open-descent steps cite their actual lemmas. There are no new statements needing separate node searches or small-case tests.

I tested the item on W empty and W equal to U, on T empty (including an empty covering), on an identity cover, on different lifts of the same section, and on a noninjective q. The proof uses injectivity only for alpha, never for q. On the empty scheme the sheaf equalizer over the empty cover supplies the unique section, so the local-to-global argument remains valid. Opens are not required to be quasi-compact, and no separatedness of the covering schemes is used. No statement dispute or source error was found.
