# Stage-1 delivery: lem-sfb-stack-proper-locally-quasifinite-composition

## Files written

All node files are under `dag/nodes/sec-six-functors-basics/` in the Q100 item sandbox.

- `lem-sfb-stack-proper-locally-quasifinite-composition.json`: item, statement, split into eight steps; statement unchanged.
- `lem-sfb-stack-separation-composition.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-stack-finite-type-calculus.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-dm-etale-atlas-calculus.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-dm-lqf-atlas-test.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-representable-stack-diagonal-criterion.json`: statement-only input, unsplit; no Mathlib match.
- `lem-sfb-representable-stack-universally-closed-test.json`: statement-only input, unsplit; no Mathlib match.

`citations.json` contains twenty-one verbatim quotations, one for each step/node citation. `searches.jsonl` is the unmodified command log. `research/mathlib-results.json` preserves the full outputs of the thirty-five actual searches, grouped by their intended nodes. `research/blueprint-searches.json` preserves the whole-blueprint duplicate searches. Auxiliary research scripts and outputs are sandbox-only.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint tag and by proper/quasi-finite and stack/DM terminology, and also read the relevant local Sheaf definition modules. The scheme results do not state this stack item. The project definitions for stable-pointed moduli give stack vocabulary, not a finished proof of this assertion.

## WANTED

None: the Stacks TeX files needed for this split are local. No SGA source is used.

## Problems found and corrections

The item is mathematically consistent with its cited source; I retained its complete statement and every hypothesis. No STATEMENT-DISPUTED correction was necessary.

The inherited `blueprint.from.node` was null. The required ancestor command also returns None because the creation chain ultimately reaches a Lean module identifier rather than a DAG id. The inherited place explicitly names `det-thm-sf-ctf-stability-direct-images`, its paragraph (3), and the alteration/moduli prerequisite; the already-reviewed definition `def-sfb-stable-pointed-moduli-groupoids` repairs precisely the same chain to that node. The first dry run rejected that repair for the new nodes because the gate recomputes ancestry through created.item, rather than consulting the explicit from field. I restored from.node = null for the item and all six new nodes, exactly the required ancestor command result, while retaining the complete intended blueprint place in from.place. No creation record or unowned ancestor was changed. This leaves the inherited provenance defect documented rather than inventing a machine-resolvable chain. The main-20261015 blueprint record and its unit and chapter were read; their route and statement are unchanged. This item is not the unit's key statement, so no unit realization record is delivered.

I corrected draft source-label lookups against `literature/stacks-project/tags/tags`: 06FM is lemma-local-source-target; 05W3 is algebraic-space etale permanence; 0CL3 is universally-closed-local; 0515 is composition-universally-closed; 01TL is scheme quasi-finite composition. The delivered sources use those verified tags, not guessed section numbers.

Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` does not include local finite type. I read the Mathlib source and the project's `WeilConjectures/AlgebraicGeometry/QuasiFiniteMorphism.lean` comparison conventions. No scheme-only search hit was promoted to a stack leaf. The generic category theorem `CategoryTheory.MorphismProperty.diagonal_isStableUnderComposition` does not by itself supply the bicategorical representable-property results for 2-fibre products, so it is not a one-line match for the separation input.

## Work left

The six new nodes deliberately have statements only, empty proof and proof-dependency lists, and status unsplit. They are the non-elementary inputs for later workers, not claims that their Lean proofs are complete. There are zero new Mathlib leaves. No Lean was written and no compiler, Lake, or local DAG gate was run.

## Review by Q100

I read the item's Stacks source: 0CL7 and its three component references (050K, 06FT and 0515), 06UD, 06UA, the discussion after 0CL5, and the definitions and characterization in 06PU and 06UF. I also read spaces-morphisms.tex 03XJ and 040Z, especially the every-compatible-chart clause (7). The proof uses the DM etale-presentation version of 06UF rather than repeating 06UD's longer quasi-DM flat-presentation proof. This stays within the same local-quasi-finiteness argument and does not change the alteration route above the node.

For the separation input I read 050K: its diagonal factorization reduces the assertion to composition and pullback of proper representable maps; it requires no properness of the original maps. For the finite-type input I read 06FT, 06FU and the compatibility paragraph preceding definition-locally-finite-type, together with the local-source-target argument 06FM. Quasi-compactness remains part of finite type: it was not confused with merely locally finite type.

For the atlas input I read algebraic.tex 04T2, the relative DM separation facts 050F/050K/050N, 06N3, the etale stability statements 0CIM/0CIN and the representable-property transfer statements 045B/045C. I read 05W3 for the compatible-chart clause: after base change to a scheme, the two maps to the common base are etale, so the map between them is etale. In particular an arbitrary compatible chart need not be surjective. The source and target of a representable etale map are allowed to be algebraic spaces; I did not assert that every such algebraic space is a scheme.

For the atlas-test input I read 06UF conditions (1), (2), (4), as well as 06UC and 06N3. It is a genuine intrinsic-to-presentation criterion for a single arbitrary DM morphism, with both an every-chart test and an existence test. It does not assert composition or properness. Although the printed proof of the most general 06UF forward implication cites 06UD, the DM etale specialization has an independent smaller route: use base change 06UB and the over-field statement 06UC on the field fibres of an etale chart; combine local finite type with the scheme discrete-fibre criterion. Conversely an etale target atlas has a point above any field point after a finite separable extension; the discrete fibres of the scheme presentation descend through the surjective open maps of point spaces. Thus a later split of this input need not cite the present composition item, and there is no intended hidden circular dependency. This is why its source also names 06UC. I have left that argument in this report, not in the unsplit node's statement.

For the representable-diagonal input I read 04YQ (including scheme representability, the monomorphism, and local quasi-finiteness) and 04YS (proper diagonal iff closed diagonal iff representable separatedness). For universal closedness I read 0512 and 0CL3, including arbitrary algebraic-stack base changes, and the algebraic-space counterpart 03XD. I expanded the universal-closedness input to say arbitrary algebraic stacks, with that notion defined inline, so the compatibility step does not quietly restrict which base changes properness tests.

Step 1 uses exactly the statements of `lem-a1-scheme-lqf-affine-criterion`, `lem-trf-quasi-finite-composition`, and `pqf-def-quasifinite`. I opened all three. The first gives finite type and quasi-finiteness at every prime on the compatible affine pair; the second gives both properties for the composite ring map; the third turns those witnesses into scheme local quasi-finiteness. Selecting nested affine neighbourhoods and composing their restriction maps is the elementary argument written in the step. This is not a new scheme lemma node.

Step 2 uses the finite-type-composition and separated-composition clauses of the two new inputs; their statements explicitly cover arbitrary DM stack morphisms, so no representability assumption is being smuggled into composition. Step 3 uses only the definition of universal closedness and the explicit 2-fibre-product groupoid definition in `def-sfb-stable-pointed-moduli-groupoids`: the image of a closed subset remains closed after each of two maps. No theorem about the topology of stack fibres is used in that elementary composition argument.

Step 4 uses the atlas input to produce W, V and U over the correct successive 2-fibre products, and uses the forward (a) to (b) clause of the atlas test twice. V maps to B, which is exactly the scheme-target hypothesis needed for the second application. Step 5 uses etale composition and base change from the atlas input and the (c) to (a) implication of the atlas test. The intermediate canonical equivalence is the direct associativity map on triples, not an unproved identification of underlying point-space fibre products. The scheme composition has already been proved in step 1.

Step 6 uses the precise compatibility clauses of the finite-type, diagonal and universally-closed inputs. A map of algebraic spaces is representable by algebraic spaces because their sheaf fibre products are algebraic spaces. I checked this convention in `def-trf-algebraic-space` and explicitly cited `lem-trf-space-fibre-products-etale-covers`, whose statement gives closure under sheaf fibre products; no scheme representability of f is assumed. The final C1 check added that citation rather than treating algebraic-space closure as a definition. Properness is the conjunction of those three compatible conditions, and the diagonal input gives the claimed closed immersion. Step 7 uses the compatible-chart clause of the atlas input and both directions of the atlas test. For the reverse implication I chose genuinely surjective atlases so that (c) applies; for the forward implication (b) explicitly permits nonsurjective U. Taking the identity target chart proves the final scheme-target clause. Step 8 uses the explicit triples and arrows in `def-sfb-stable-pointed-moduli-groupoids` and the discrete-sheaf interpretation in `def-trf-algebraic-space`: a 2-isomorphism composes the connecting isomorphism in a triple, with inverse given by its inverse; a stack equivalence gives mutually inverse equivalences on fibres. Choosing the transported atlas identifies the defining topology and each scheme-chart test. No mere equivalence of object sets was substituted for an equivalence of stacks.

I checked B--E of delivery-errors.md against the files. Every new node introduces its own objects and definitions, has Stacks tags and labels, single-escaped mathematical TeX, empty proof fields and actual logged searches of all four required services, with a second semantic wording. None is an exact clause or restatement of the composite assertion: the inputs concern proper diagonals, finite type, presentations, or arbitrary representable morphisms; the item performs the composition argument and the algebraic-space specialization. In particular I did not create nodes saying simply 'proper stack maps compose' or 'locally quasi-finite stack maps compose'. The algebraic-space properness clause is assembled from three strictly smaller compatibility facts. The same-tag comparisons are below. Every quoted citation is a literal substring of its current node statement. No new statement depends on the item; the dependency lists have no intended cycle. The two cross-unit scheme lemmas and the fibre-product lemma are declared as generic tool uses in split_report, not as maintainer-approved tool_uses.

Edge cases checked: empty schemes, empty atlases over the empty stack, identity maps, nonsurjective charts, and non-quasi-compact locally quasi-finite maps. For a finite constant group G over a field, BG to the field is a nonrepresentable proper locally quasi-finite DM example; its scheme atlas and nontrivial finite diagonal satisfy the new tests, so the proof has not silently reduced all stack morphisms to representable ones. For A^1 to a point, finite type holds but the scheme presentation is not locally quasi-finite, as it should be. No assumption of reducedness, perfectness, a field base, finite stabilizers, or Noetherian schemes was added to the general inputs. All eight proof steps are below 2000 characters, and each inline comparison was inspected for a hidden independent lemma.

## Not duplicates

lem-sfb-dm-etale-atlas-calculus vs lem-sfb-algebraic-stack-dm-point-stabilizer: the existing result detects the DM open at a point through its stabilizer; the new result gives relative fibre-product atlases and etale base-change, composition, and compatible-chart calculus.

lem-sfb-dm-etale-atlas-calculus vs lem-sfb-algebraic-stack-open-dm-locus: the existing result constructs the largest open with unramified diagonal; the new result gives relative fibre-product atlases and etale base-change, composition, and compatible-chart calculus.

lem-sfb-dm-etale-atlas-calculus vs lem-sfb-curve-stack-infinitesimal-dm-locus: the existing result locates the DM open of the stack of curves via infinitesimal automorphisms; the new result gives relative fibre-product atlases and etale base-change, composition, and compatible-chart calculus.

lem-sfb-dm-etale-atlas-calculus vs lem-sfb-dm-isom-space-unramified: the existing result proves unramifiedness of the Isom algebraic space for two objects; the new result gives relative fibre-product atlases and etale base-change, composition, and compatible-chart calculus.

lem-sfb-dm-etale-atlas-calculus vs lem-sfb-dm-open-finite-etale-permanence: the existing result assumes a smooth finite-type stack over a field with finite diagonal and treats an open substack and finite-etale decorations; the new result has no such restrictions and gives relative fibre-product atlases and etale base-change, composition, and compatible-chart calculus.

lem-sfb-dm-etale-atlas-calculus vs lem-sfb-representable-finite-stack-properties: the existing result assumes a finite scheme-representable morphism and concludes DM, proper and locally quasi-finite; the new result gives relative fibre-product atlases and etale base-change, composition, and compatible-chart calculus.

lem-sfb-dm-etale-atlas-calculus vs lem-sfb-unramified-diagonal-etale-atlas: the existing result equates an unramified structural diagonal with existence of an etale atlas for one stack; it does not give the new relative fibre-product atlases and etale base-change, composition, and compatible-chart calculus.

lem-sfb-dm-lqf-atlas-test vs lem-sfb-curve-stack-infinitesimal-dm-locus: the existing result locates the DM open of the stack of curves via infinitesimal automorphisms; the new result gives intrinsic local-quasi-finiteness versus universal relative chart tests and the existence of one compatible presentation for an arbitrary DM morphism.

lem-sfb-dm-lqf-atlas-test vs lem-sfb-dm-coarse-proper-locally-quasifinite: the existing result is properness and local quasi-finiteness of a finite-diagonal coarse morphism over a field; the new result gives intrinsic local-quasi-finiteness versus universal relative chart tests and the existence of one compatible presentation for an arbitrary DM morphism.

lem-sfb-dm-lqf-atlas-test vs lem-sfb-dm-isom-space-unramified: the existing result proves unramifiedness of the Isom algebraic space for two objects; the new result gives intrinsic local-quasi-finiteness versus universal relative chart tests and the existence of one compatible presentation for an arbitrary DM morphism.

lem-sfb-dm-lqf-atlas-test vs lem-sfb-representable-finite-stack-properties: the existing result assumes a finite scheme-representable morphism and concludes DM, proper and locally quasi-finite; the new result gives intrinsic local-quasi-finiteness versus universal relative chart tests and the existence of one compatible presentation for an arbitrary DM morphism.

lem-sfb-dm-lqf-atlas-test vs lem-sfb-unramified-diagonal-etale-atlas: the existing result equates an unramified structural diagonal with existence of an etale atlas for one stack; it does not give the new intrinsic local-quasi-finiteness versus universal relative chart tests and the existence of one compatible presentation for an arbitrary DM morphism.

lem-sfb-representable-stack-diagonal-criterion vs lem-sfb-stack-proper-locally-quasifinite-composition: the item composes proper locally quasi-finite maps and specializes to algebraic spaces; the new result is the strictly smaller general representable-diagonal theorem, including monomorphy, scheme representability and equivalence of proper diagonal with separated base changes, with no properness hypothesis on f.

lem-sfb-stack-finite-type-calculus vs lem-sfb-dm-open-finite-etale-permanence: the existing result assumes a smooth finite-type stack over a field with finite diagonal and treats an open substack and finite-etale decorations; the new result has no such restrictions and gives composition, arbitrary base change and representable compatibility for finite type and locally finite type of arbitrary DM morphisms.

The six new nodes were also compared with one another: the atlas-calculus node states existence and etale permanence, the atlas-test node characterizes intrinsic local quasi-finiteness, and the remaining four concern distinct finite-type, separation, diagonal and closedness statements. Sharing a source tag for supporting vocabulary does not duplicate their conclusions.

## Validation and repair

The first required dry run exited 1: all six diagnostics were B9 ancestry mismatches, because the computed ancestor is None. I repaired only the sandbox metadata to use the exact computed null ancestor, with the named intended blueprint passage retained in from.place; all mathematical statements and proof steps were unchanged. The final dry run is required again before push.
