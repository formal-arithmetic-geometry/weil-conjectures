## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-decent-algebraic-field-image-closed.json: item, split, statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-decent-space-etale-generalization-lifting.json: statement-only input, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-algebraic-residue-closed-point.json: statement-only input, unsplit, no Mathlib match.
- citations.json: verbatim statement quotations for every step/node pair.

Attachments: none. Searched all lean/WeilConjectures for the item tag, decency, 01TE and algebraic-residue closed-point phrases; no project declaration states this item. Scheme-only closed-point declarations do not give an attachment for algebraic spaces.

WANTED: none.

The imported statement is correct against Stacks 07U5. The source's U' in the sentence choosing u' is an evident typographical error: it is the chosen chart U. No mathematical correction or extra hypothesis was needed. Existing quasi-separated specialization nodes cannot be applied to an arbitrary decent space, and existing finite-residue scheme nodes cannot be applied to arbitrary algebraic residue extensions or arbitrary scheme morphisms. The split does not use the finite-field-map node 08AL, which needs a finite rather than algebraic extension. No unfinished part remains in this one-level split; the two new nodes deliberately have no proof.

## Sources and searches

Read decent-spaces.tex, lemma-algebraic-residue-field-extension-closed-point (07U5), including its whole proof; lemma-decent-specialization (03IL); lemma-UR-finite-above-x (03JV), especially condition (4); and definition-very-reasonable (03I8). Read morphisms.tex, lemma-algebraic-residue-field-extension-closed-point-fibre (01TE), statement and proof, and lemma-etale-over-field (02GL). Read spaces-properties.tex, lemma-points-cartesian, and the statements of all cited DAG nodes. Read the latest blueprint direct-images proof (3), as well as the chapter/unit records and inherited blueprint place. The item remains an auxiliary tool on its existing adequate-moduli branch, without replacing any unit step.

Whole-DAG searches covered the source tags, decency, specialization lifting, algebraic residue closedness and field towers. blueprint_refs.py search was run for decent, algebraic residue, specialization, 03IL, 01TE and closed point; no blueprint node states either new input. blueprint_refs.py ancestor returns None on this inherited chain: the new nodes retain that value, put the item first in via, and specify exactly which supporting argument they serve. The newest blueprint direct-images proof is read through literature/blueprint/latest, not a dated snapshot.

All new Mathlib queries were actually run through msearch.py and their returned records are retained in searches.jsonl and mathlib_searches. Two semantic phrasings per input, Loogle and Mathlib grep were read. The scheme candidates isClosed_singleton_iff_isClosedImmersion (ClosedImmersion.lean:423) and isClosed_singleton_iff_locallyOfFiniteType (Finite.lean:222) do not prove the algebraic-residue criterion in one line: the former still requires the desired geometric argument, the latter assumes a Jacobson scheme. Finite.lean:209 states a different direction and assumes local finite type; Smooth.lean:356 uses algebraicity to prove a smooth-locus fact. There is no algebraic-space decency or generalization-lifting declaration among the hits. Thus neither new node is a Mathlib leaf. The existing algebraic-element-tower Mathlib leaf is reused.

## Not duplicates

lem-sfb-decent-space-etale-generalization-lifting vs lem-sfb-quasiseparated-space-etale-specializations: the existing result assumes a quasi-compact relative diagonal; the new result assumes only the strictly weaker explicit decency condition and states lifting, without the existing result's separate no-fibre-specializations clause.

lem-sfb-scheme-algebraic-residue-closed-point vs lem-trf-finite-residue-tower-local-geometry: the existing result concerns locally finite-type schemes over a field, finite extensions and Noetherian local geometry; the new result concerns arbitrary scheme morphisms and arbitrary algebraic residue extensions over a closed image.

lem-sfb-scheme-algebraic-residue-closed-point vs lem-trf-finite-residue-point-closed-in-fibre: the existing result assumes local finite type and a finite extension and concludes only fibre closedness; the new result needs neither finiteness assumption and concludes closedness in the total scheme when the base point is closed.

lem-sfb-scheme-algebraic-residue-closed-point vs lem-trf-etale-completed-local-ring-iso: the existing result is an etale-completion comparison for locally finite-type schemes over an algebraically closed field with rational residue points; none of those hypotheses is present in the new result.

lem-sfb-scheme-algebraic-residue-closed-point vs lem-pc-dense-separable-points: the existing statement is density of finite-separable closed points in a smooth scheme over a field; it does not address a prescribed algebraic-residue point for an arbitrary morphism.

lem-sfb-scheme-algebraic-residue-closed-point vs lem-sfb-projective-generic-map-graph-alteration: the existing statement constructs a projective graph alteration from finite separable generic data; it does not state the arbitrary-scheme closed-point criterion.

lem-sfb-scheme-algebraic-residue-closed-point vs lem-weil-pbc-etale-fibre-discrete-separable-points: the existing statement describes etale fibres, hence needs etaleness; the new closedness criterion requires only algebraicity over a closed base point.

## Review by Q102

I checked the proof against the full 07U5 argument, rather than inferring it from the title. Condition (4) of 03JV is exactly the field-monomorphism hypothesis written in the item, so the new 03IL input uses precisely that hypothesis without assuming that the relative diagonal is quasi-compact. Its statement introduces its own S, X, U, morphism and points and defines both quasi-compactness and specialization. Its source was read at decent-spaces.tex:2661. The other input is precisely part (2) of 01TE, read at morphisms.tex:3565; I did not import a local finite-type hypothesis from the later Nullstellensatz lemma. Both new files contain statements only, with definition dependencies, sources and actual search results; neither is a clause of the item: lifting has no field-map closedness conclusion, and the scheme criterion has no algebraic-space conclusion.

In step 1, def-trf-algebraic-space explicitly supplies the representable surjective etale atlas; the point-topology convention identifies its surjectivity with coverage of point classes. The new lifting statement explicitly supplies u specializing to the prescribed u0. This is the only use of decency. In step 2, the representable-etale definition explicitly says that the pullback by the scheme Spec L is a scheme and its projection is etale. lem-a1-space-fibre-product-point explicitly supplies a point over the compatible pair, and lem-weil-pbc-etale-fibre-discrete-separable-points explicitly supplies a finite separable residue field extension at any point of an etale fibre. Here the fibre over the unique point of Spec L is W itself. No quasi-compactness of W is needed.

In step 3, def-weil-residue-field states the induced field maps and their origin in the local maps; def-pc-field-extension supplies injectivity. The compatible towers come from the commutative square, not from an assumed equality of unrelated coefficient structures. lem-sfb-algebraic-element-tower gives exactly elementwise algebraic transitivity. Descent from kappa(w) to kappa(u) is written out using an annihilating polynomial and injectivity; it is not a hidden subextension lemma. In step 4, the new scheme criterion has exactly the hypotheses established: the same closed s and algebraic residue extension. A closed u has no other specialization; projecting u=u0 gives x=x0. This proves the closure equals the singleton without invoking T0 or sobriety. def-weil-affine-spectrum states that a field spectrum has one point, so this singleton is the whole image. Every cited statement is included verbatim in citations.json, and each proof dependency occurs in a step.

I checked the small cases: the empty X admits no a and hence is vacuous; U need not be affine or quasi-compact; the source field extension may be infinite algebraic or purely inseparable. For the scheme input, Spec of an infinite algebraic field extension over Spec k still gives a closed singleton and is allowed. A transcendental generic point of A1/k fails algebraicity, as required. For a nonclosed base point, the identity map on a trait at its generic point shows why closedness of s must remain. For lifting, an empty U gives no u0, and the identity chart gives the same specialization. No claim assumes all decent spaces are quasi-separated. I corrected the tempting but invalid use of the existing stronger-hypothesis specialization lemma by introducing the general 03IL input.

I reviewed B--E explicitly: no proof is hidden in a new statement; no new node is elementary, a duplicate, or a restatement of the whole item; each non-elementary invocation has a matching cited statement; each map is the actual residue-field map of the chosen diagram. All proof steps are under 600 characters, so none reaches the 2000-character hidden-lemma review threshold. The generic off-unit tools are declared in split_report.tool_uses and do not alter the unit route. No SGA route, Lean writing or compiler was used.

Dry-run repair: the first search check found that the lifting node omitted the already executed zero-hit Mathlib grep from its JSON search list. Added the exact logged query; no search was invented or repeated.
