# Stage-1 report

## Files written

Item: dag/nodes/sec-proper-base-change/lem-weil-pbc-field-curve-completion-insep.json, split into seven steps without changing its statement.

New statement-only nodes, all unsplit, no Mathlib match:
- lem-weil-pbc-curve-projective-dense-completion: ordinary projective completion, without any normalization or field change.
- lem-weil-pbc-normalization-geonormal-insep: geometric normality after field change, in arbitrary dimension, without projective completion or smoothness.
- lem-weil-pbc-normalization-projective-components: projective normalization and its integral components, without field change or smoothness.
- lem-weil-pbc-geonormal-dim-one-smooth: smoothness from geometric normality and low dimension, and irreducibility of connected geometric normal schemes.
- lem-weil-pbc-finite-separable-base-refinement: smoothness and projectivity after refining a field of definition through a finite separable extension; no normalization or completion.

citations.json quotes the complete statements read for every citation. searches.jsonl is the command's actual log; search-results.json holds the actual returned hits. Extra searches of constant fields and baby Stein were made before discovering existing nodes and therefore produced no new files. Extra etale-base-change searches likewise produced no new node: the existing lem-weil-pbc-etale-scheme-base-change is reused.

## Attachments

None. Project source searches by the item tag, normalization/completion/inseparability/geometric-normality keywords found no declaration asserting this item. The existing perfect-field normalization theorem requires a perfect base and cannot supply the finite inseparable preparation. Master was only read as reference.

## WANTED

None: the Stacks tex sources required here are present.

## Corrections and gaps

No statement dispute. The imported statement agrees with Tag 0GK5, with explicit componentwise normalization and the empty-index and finite-presentation clarifications. The source's omitted reduction from a projective completion to the original open is now step 6. We do not assert that normalization commutes with inseparable base change: first change the field, then normalize, then restrict to an open.

The constant-field and baby-Stein candidates were discarded as duplicates of lem-pc-h0-proper-variety, lem-pc-proper-geometrically-reduced-global-sections-separable, and lem-weil-pbc-stein-factorization-affine. Ordinary projective completion is strictly weaker than the item, and geometric normality preparation applies in arbitrary dimension; no new node restates the item's conclusion. The chapter and unit records are unchanged. Generic off-unit tools are declared in split_report.tool_uses, as required by the worker brief.

## Unfinished work

None for this one-level split. The five new nodes are searched statement-only inputs for subsequent workers, not claimed proofs or completed leaves.

## Review by NJ

I read varieties.tex, lemma-dim-1-projective-completion-after-insep (0GK5), including its five assertions and whole proof, against the unchanged statement. The chapter route is proper base change and the item expands the constructibility input below that route; its blueprint ancestor and via chain are preserved. I read the unit's three steps and did not replace any of them.

For the completion input I read 0BXV and its scheme-theoretic-image construction: a reduced source has reduced scheme-theoretic closure, since the structure sheaf injects into the direct image of a reduced sheaf. Dimension at most one and the finite boundary follow as in that proof; the empty completion is allowed. This is not the existing compactification of a smooth curve over an algebraically closed field, which has stronger base and smoothness hypotheses.

For geometric normalization I read 0BXT and the nearby normalization section. The new statement keeps finite type, finite purely inseparable extension, and all-extension geometric normality, with normalization defined componentwise. I read the geometric-normality criterion (lemma-geometrically-normal) to check that local normality after every field extension has the intended meaning.

For projective normalization I read 0BXR and 0GK4 and properties.tex 033M. Finiteness is needed here, not only integrality. Projectivity of the normalization and the closed components is supplied by 0GK4 and projective composition. Nonempty normal integral components are precisely the components of the componentwise normalization. The dimension assertion is justified by the existing finite-surjective-dimension statement, whose hypotheses hold on a nonempty component and its reduced image. There is no claim of smoothness over an imperfect field.

For geometric normality implying smoothness I read properties.tex 0BX2, varieties.tex 038X, algebra.tex 00P3, and properties.tex 033M. Over every extension the finite type scheme is locally Noetherian, dimension remains at most one, and normality makes it regular. Then 038X gives smoothness. A normal Noetherian scheme is a finite disjoint union of integral schemes, so connected nonempty ones are irreducible. Empty schemes satisfy the smoothness clause, but the irreducibility clause expressly requires nonempty connectedness. Zero-dimensional components are allowed and not treated as dimension-one DVRs.

For the refinement input I read more-morphisms.tex 0G80 and morphisms.tex 0C4Q, 087S and 01W9. A finite separable extension defines an etale separated spectrum morphism; 0G80 gives smoothness of the refined structural map. Projectivity follows from projective permanence, and over a field projectivity is H-projectivity by 087S. Properness is the consequence of 01W9. This is about an already specified structural factorization, not a construction of any new field or curve.

Step 1 uses exactly the definition of reduction, the Noetherian finite-type theorem, and the coproduct theorem. The nilradical is nilpotent on a Noetherian affine chart, remains nilpotent on scalar extension, and the two reductions therefore agree. I checked the empty case separately. Step 2 uses the completion and preparation statements, the homeomorphism for inseparable base change, and projective base change; these statements give respectively the completion, extension, preservation of generic points and dimension, and projectivity. No perfectness assumption is inserted.

Step 3 uses precisely the projective-components input and geometric-normality input; the latter applies componentwise because these are open and closed. Step 4 reads the proper-variety global-sections statement, the separability statement, affine Stein factorization, and base refinement: the schemes really are integral proper varieties, their global functions really form fields, and geometric reducedness was proved in step 3. Stein's statement explicitly gives geometrically connected fibres, unlike its definition node. I also read the proper-variety blueprint proof, 0BUG(4), and more-morphisms.tex 03H2 to confirm those interfaces.

Step 5 uses the singleton case of the etale-coproduct theorem, the existing etale-scheme-base-change theorem (02GO), and the etale-section-clopen theorem. These give the open-and-closed summand selected by the multiplication map. The spectrum map is separated: for fields its diagonal is the surjective multiplication map on tensor products. Its section is explicit, not guessed from a set-theoretic image. Thus each base change over k_i has normal local rings inherited from the base change over k'. The connectedness clause of the geometric-normality node then proves irreducibility. This verifies all extension fields, not just an algebraic closure.

Step 6 reads the exact open-localization clause of lem-weil-pbc-reduced-algebraic-normalization-field-change. It is applied to a reduced component over k', not to the nonreduced scalar extension. The open contains its generic point, so the function field is unchanged; taking all such restrictions gives exactly the normalization demanded by the item. This repairs the 'details omitted' sentence without a new restatement node. Step 7 uses locally-finite-type implies locally-finitely-presented over a locally Noetherian base, the finite-type Noetherian theorem and the finite-presentation definition, together with the already obtained projective components. Open subschemes of these Noetherian schemes are quasi-compact. All morphisms are restrictions of structural maps and the normalization; no compatibility is assumed for a new arbitrary choice.

I checked B1-B9 (complete standalone statements, inline normality definitions, undoubled TeX, exact labels/tags, genuine executed searches, blueprint attribution), C1-C8 (each non-elementary input is cited and quotes the statement, no definition used as a theorem, no dependency on the parent item), D1-D5 (five smaller generic facts, not the clauses of 0GK5; restriction details written out), and E1-E7 against the hypotheses above. Small cases checked: empty X; finite separable and purely inseparable zero-dimensional spectra; nonreduced spectra; reducible nodal curves with several components; and characteristic zero, when k'=k. Smoothness is never inferred merely from normality over an imperfect field. LeanSearch's HTTP 500 is recorded as unavailable. The actual Finder results give integral-normalization and projective-spectrum properties, not any new statement; Loogle likewise gives no full match. In particular the global-functions Mathlib hit was not duplicated because a DAG node already supplies it.

## Not duplicates

lem-weil-pbc-normalization-projective-components vs lem-weil-pbc-reduced-algebraic-normalization-field-change: The new statement gives projectivity of the componentwise normalization of a projective scheme over any field; the existing statement does not assert that projectivity.

lem-weil-pbc-normalization-projective-components vs lem-weil-pbc-reduced-curve-normalization: The new statement gives projectivity of the componentwise normalization of a projective scheme over any field; the existing statement does not assert that projectivity.

lem-weil-pbc-normalization-projective-components vs lem-sc-smooth-connected-curve-local-rings: The new statement gives projectivity of the componentwise normalization of a projective scheme over any field; the existing statement does not assert that projectivity.

lem-weil-pbc-geonormal-dim-one-smooth vs lem-pc-dim-base-change: The new statement proves smoothness from geometric normality in dimension at most one and irreducibility of connected geometric normal schemes; the existing statement does not supply that implication.

lem-weil-pbc-geonormal-dim-one-smooth vs lem-weil-pbc-dimension-preserved-field-extension: The new statement proves smoothness from geometric normality in dimension at most one and irreducibility of connected geometric normal schemes; the existing statement does not supply that implication.

lem-weil-pbc-geonormal-dim-one-smooth vs lem-weil-pbc-relative-global-complete-intersection-base-change: The new statement proves smoothness from geometric normality in dimension at most one and irreducibility of connected geometric normal schemes; the existing statement does not supply that implication.

lem-weil-pbc-geonormal-dim-one-smooth vs lem-sc-smooth-connected-curve-local-rings: The new statement proves smoothness from geometric normality in dimension at most one and irreducibility of connected geometric normal schemes; the existing statement does not supply that implication.

lem-weil-pbc-geonormal-dim-one-smooth vs base-change-dimension: The new statement proves smoothness from geometric normality in dimension at most one and irreducibility of connected geometric normal schemes; the existing statement does not supply that implication.

lem-weil-pbc-finite-separable-base-refinement vs lem-weil-pbc-grothendieck-existence-projective: The new statement refines a specified smooth projective structural map through a finite separable field; the existing statement concerns Grothendieck's existence theorem for closed subschemes of projective space over a complete Noetherian ring.

lem-weil-pbc-finite-separable-base-refinement vs lem-weil-pbc-projective-ample-invertible: The new statement refines a specified smooth projective structural map through a finite separable field; the existing statement concerns A closed immersion into projective space supplies an ample invertible sheaf.

## Second reading by NJ

I am a fresh second reader, not the author of the split. I opened delivery-errors B–E, GOAL.md and coord/dag-sync.md, the item and every cited statement, the five new files and their definition interfaces, and the Stacks TeX below. Only the sandbox was edited; no Lean or compiler was used. The item agrees with varieties.tex, lemma-dim-1-projective-completion-after-insep (0GK5), hypotheses and clauses (1)–(5); its explicit componentwise normalization, nonempty components, finite presentation and empty-index convention are valid clarifications. No statement dispute was found.

- Step 1: checked against scheme-reduction and coproduct statements and 0GK5's reduction paragraph; PASS after replacing the unnecessary Noetherian-nilpotence assertion by the finite-sum nilpotent calculation. The two reductions coincide after every field extension, including nonreduced and empty inputs.
- Step 2: checked against 0BXV (lemma-dim-1-projective-completion), 0BXT (lemma-finite-extension-geometrically-normal), lem-pc-homeo-pure-insep and lem-pc-projective-base-change; PASS. The completion is reduced, purely inseparable base change preserves its generic points and dimension, and both cited projectivity conventions are H-projectivity. No normalization/base-change commutation is assumed.
- Step 3: checked against 0BXR (lemma-normalization-locally-algebraic), 0GK4 (lemma-normalize-projective), and the two new component/smoothness statements; PASS. Components are open and closed, so their scalar extensions inherit normal local rings; dimension zero and the empty component family cause no exception.
- Step 4: checked the complete statements of lem-pc-h0-proper-variety, lem-pc-proper-geometrically-reduced-global-sections-separable, lem-weil-pbc-stein-factorization-affine, and finite-separable-base-refinement against varieties.tex 0BUG and more-morphisms.tex theorem-stein-factorization-general (03H2); PASS. Each input is an integral proper variety, geometric reducedness has already been established, and the canonical affine Stein map has the geometrically connected fibres actually required.
- Step 5: checked etale-coproduct-etale, etale-scheme-base-change (02GO), etale-section-clopen-immersion and the connectedness clause of geonormal-dim-one-smooth; PASS after spelling out the multiplication section, the affine diagonal proving separatedness, the fibre-product identification and the inverse images of the complementary opens. Normality over every extension of k_i is now proved before applying that clause; dimension at the base is supplied by step 3, and finite type over k_i by step 4.
- Step 6: checked the exact open-localization clause of reduced-algebraic-normalization-field-change (035K), reduction and coproduct statements against 0GK5's omitted restriction argument; PASS after explicitly writing W as the reduction of the base-changed open. Each reduced component D meets W at its generic point, and the restriction of D's normalization is precisely the normalization of D intersect W.
- Step 7: checked finite-type-over-noetherian, pqf-lem-lft-fp-locnoeth, scheme-conventions, normalization-projective-components and the newly cited existing noetherian-open-subscheme-noetherian; PASS after citing quasi-compactness of opens and writing the finite generating sets after scalar extension. Separatedness supplies quasi-separatedness, all maps are the specified restrictions, and surjectivity proves the nonempty-index direction.
- New node lem-weil-pbc-curve-projective-dense-completion: checked varieties.tex lemma-dim-1-projective-completion (0BXV), its scheme-theoretic-image proof and the definition of reduction; PASS, retained. Reducedness follows because the structure sheaf injects into the direct image of the reduced open's sheaf. Empty schemes and zero-dimensional finite schemes have empty boundary. DAG/tag and whole-blueprint searches find no existing arbitrary-field, nonsmooth completion statement.
- New node lem-weil-pbc-normalization-geonormal-insep: checked varieties.tex lemma-finite-extension-geometrically-normal (0BXT), including algebraic = finite type, with componentwise normalization as in 0BXR; PASS, retained. It works in arbitrary dimension and does not construct a projective completion or claim smoothness. Purely inseparable field spectra and nonreduced inputs are allowed.
- New node lem-weil-pbc-normalization-projective-components: checked varieties.tex lemma-normalization-locally-algebraic (0BXR) and lemma-normalize-projective (0GK4), properties.tex lemma-normal-Noetherian (033M), and algebra.tex lemma-integral-sub-dim-equal (00OK); PASS, retained after defining scheme normality inline and replacing the vague dimension source by exact tags/labels. Closed components inherit projective embeddings; finite normalization of each reduced nonempty image preserves dimension. Empty C gives empty I. Existing reduced-algebraic-normalization-field-change supplies finiteness and localization but not projectivity, and reduced-curve-normalization assumes an algebraically closed field.
- New node lem-weil-pbc-geonormal-dim-one-smooth: checked properties.tex lemma-normal-dimension-1-regular (0BX2), varieties.tex lemma-geometrically-regular-smooth (038X), algebra.tex lemma-dimension-preserved-field-extension (00P3), and properties.tex lemma-normal-Noetherian (033M); PASS, retained. Every scalar extension is locally Noetherian, has dimension at most one and is regular; connected nonempty normal Noetherian schemes have one integral component. No imperfect-field regular-implies-smooth inference is made. This is not the dimension-preservation node or the algebraically closed smooth-connected-curve statement.
- New node lem-weil-pbc-finite-separable-base-refinement: checked more-morphisms.tex lemma-smooth-etale-permanence (0G80), morphisms.tex lemma-projective-permanence (0C4Q), lemma-projective-over-quasi-projective-is-H-projective (087S) and lemma-H-projective (01W9); PASS, retained. A finite separable field spectrum is etale and separated; projectivity of the already specified composite and the given factorization are exactly the hypotheses needed. Empty Z and L=k also satisfy the assertion. No DAG node found states this combined refinement.

Independent duplicate/Mathlib checks: I ran whole-blueprint searches for normalization, projective completion and geometrically normal, read the same-tag existing nodes listed above, and searched upstream Lean sources (including the normalization and smoothness modules) read-only; their normalization finiteness/dimension declarations and perfect-field results do not state these five inputs. My independent msearch.py queries, all logged verbatim in searches.jsonl, were grep `compactification|compactify` in AlgebraicGeometry (0 hits), grep `geometrically.?normal|geometricNormal` in AlgebraicGeometry (0 hits), grep `normalization.*projective|projective.*normalization` in AlgebraicGeometry (0 hits), Finder `A geometrically normal algebraic scheme of Krull dimension at most one is smooth` (8 hits: smoothness definitions, standard smoothness and smooth loci, no geometric-normality criterion), and Finder `If a composite morphism of schemes is smooth and the second morphism is etale then the first morphism is smooth` (8 hits: etale implies smooth, etale cancellation and composition of smooth maps, no smooth cancellation or combined projective refinement). These rephrase the first reader's searches. None justifies a Mathlib leaf. The first reader's actual three-kind search records remain intact.

Changes: expanded elementary reduction and the clopen base-change argument; corrected the reduced-open notation; cited the existing Noetherian-open theorem and expanded finite type under field extension; made normality self-contained and its dimension source precise; refreshed citations.json from all cited statements. Five genuinely non-elementary geometric inputs remain, no new nodes were added or deleted, no Mathlib leaves were found. The existing Review by NJ and other first-worker sections are preserved. split_report.tool_uses is a worker declaration under the current coord/brief-stage1.md final paragraph, not the maintainer's top-level tool_uses field.

## Not duplicates (second-reader source expansion)

lem-weil-pbc-normalization-projective-components vs lem-zl-noether-normalization-dimension: the existing statement computes the dimension of a finite polynomial normalization, with no projectivity claim; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs lem-sc-finite-surjective-dimension: the existing statement supplies only equality of dimensions for a given finite surjection, not a projective normalization; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs lem-weil-pbc-integral-injective-dimension-equal: the existing statement concerns only dimensions of integral injective ring maps; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs lem-zl-noether-normalization-field: the existing statement constructs a finite polynomial subalgebra, not a scheme normalization or projectivity; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs thm-sc-serre-duality-curve: the existing statement is coherent duality on an already smooth proper curve over an algebraically closed field; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs lem-sc-deg-principal-zero: the existing statement is the degree formula for a principal divisor; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs lem-weil-pbc-noether-normalization-field: the existing statement constructs a finite polynomial subalgebra, not a projective scheme normalization; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs thm-sc-affine-torsion-cd: the existing statement bounds torsion cohomological dimension of affine schemes; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs lem-sc-normalization-exists: the existing statement gives finite proper normalization of an integral finite-type scheme but does not assert projectivity; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

lem-weil-pbc-normalization-projective-components vs lem-sc-base-change-curve: the existing statement assumes algebraically closed base fields and concerns preservation of curve properties under base change; the new input supplies projectivity and the finite integral component decomposition over an arbitrary field.

