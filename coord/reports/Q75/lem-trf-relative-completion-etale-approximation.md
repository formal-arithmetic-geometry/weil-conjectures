# Worker report — repair of fd3b71f0bbe5

The item statement is unchanged. This repair follows Stacks 0GDX and replaces the invalid arbitrary-model descent by descent with X_j=X×_S S_j and Y_j=Y×_T S_j fixed throughout. There are five new statement-only nodes, no Mathlib leaves, no Lean writing and no compiler runs.

Files: the item JSON (nine proof steps), the four retained auxiliary JSON files, the new `lem-trf-fixed-family-etale-span-descent.json`, this report and citations.json. The original report is retained as report-prior.md in the sandbox, and searches.jsonl has been retained and appended. Node layout and historical ancestry are preserved, with the complete ancestry via chain supplied for each auxiliary node. No target, unit, chapter, or maintainer-owned field is changed.

Attachments: none. I searched the exact item tag and completion/approximation terminology under WeilConjectures in the read-only slopmaster2 source; no declaration states the item. The upstream master is reference material only.

WANTED: none.

Unfinished: the five auxiliary nodes intentionally remain unsplit, with statements only and empty proof/proof_deps; that is the required one-level split, not claimed proofs of those nodes.

## Repairs to every return point

1. C4/E3/E5: arbitrary models are removed. Step 5 defines the actual X_j and Y_j before descent. Step 6 descends only U and its two arrows using the new fixed-family pointed-span lemma. Step 8 writes both Cartesian squares and verifies their universal properties. Step 9 computes the marked fibre and its residue field. In the review's R=Fp[t], S_j=Spec R[z], z↦0 example, the models X_j=Y_j=S_j are now fixed; V(z) is forbidden as either target. With V=V(z−t), the corrected final map is a base change of a genuinely etale map into S_j. Thus the bad W=Spec R/(t) example no longer meets the hypotheses used in step 6.
2. Long-step rule: the independent finite-stage fixed-family/pointed-span descent argument is extracted as `lem-trf-fixed-family-etale-span-descent`. It assumes neither completions nor G-rings nor smooth stages nor a slice, and concludes neither a base etale neighbourhood nor the item. It is a separate inverse-limit tool. Its statement keeps both target models fixed, specifies the two arrow equalities under actual pullback, and defines marked points as images. The item has no proof step longer than 2000 characters; no length-only paragraph splitting is used to hide the comparison.
3. C1, completed base: step 2 now cites `lem-weil-pbc-local-completion-local-ring` for locality, the maximal ideal, and the residue field, and `lem-weil-pbc-adic-completion-mod-ideal` for completeness with respect to that ideal. Only then is the complete-local G-ring theorem applied. The lft base-change citation is used for the two structure morphisms to B, never for the projection arising from completion.
4. C1, limits and finite presentation: step 3 cites `lem-weil-pbc-limit-affine-transition` for Spec of the ring colimit and the scheme limit. Steps 1 and 5 give affine finite-presentation hypotheses and cite the ring finite-presentation base-change/composition theorem. The extracted lemma encapsulates object descent and eventual etaleness with fixed targets; it does not incorrectly attribute object descent, point descent or arbitrary-model identification to the finite-diagram-lift statement.
5. B3: the immersion-slice statement now cites `def-weil-pbc-separable-algebraic-extension`, rather than a separable-polynomial definition for the extension notion. Finite field extension means finite-dimensional explicitly. The two completion tools now cite the locally Noetherian definition. Statements use mathematical TeX delimiters throughout. The finite-residue node's blueprint place now correctly describes the one-way implication of 01TE and distinguishes the converse 01TF.
6. B7: all historical searches and the log remain. Failed Loogle parser requests are labelled unavailable/failed query, not negative results. I found the reason for the impossible old grep result: the caller supplied `Mathlib/AlgebraicGeometry` where msearch expects a subdirectory of Mathlib, and the script suppressed rg's invalid-path error. The old records now explicitly disclaim any absence conclusion. Valid replacement searches use `AlgebraicGeometry` or the Mathlib root, and their exact outputs are recorded. The closed-point search really returns `AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType`, Finite.lean:221, and the fibre Jacobson instance is at Fiber.lean:144. That theorem requires local finite type of the residue-point inclusion; the finite-extension hypothesis still needs comparison with that inclusion, so this is a partial candidate, not a certified one-line match. Two different semantic phrasings plus Loogle, grep and LeanSearch were run for the new fixed-family lemma; no exact result states it.
7. Stale entries: the unused spreading-out, diagram-lift, eventual-etale and finite-type-composition citations have left the item's direct uses. Their mathematical content belongs to the future split of the new inverse-limit lemma. In particular `lem-sfb-finite-type-composition-base-change` is absent from split_report.tool_uses. The remaining off-unit statements are declared as generic tools in split_report, not as maintainer-accepted tool_uses.

## Not duplicates


`lem-trf-smooth-point-etale-immersion` vs `lem-sbc-smooth-separable-point-etale-slice`: the new node gives an immersion with singleton fibre; the existing node gives only an affine map whose composite to the base is etale.

`lem-trf-finite-residue-point-closed-in-fibre` vs `lem-weil-pbc-isolated-fibre-point-residue-finite`: the new node proves finite residue extension implies closedness; the existing node proves the opposite implication from an isolated fibre point.

`lem-trf-finite-residue-point-closed-in-fibre` vs `lem-weil-pbc-lft-over-field-isolated-point-residue-finite`: both cite Tag 01TF, but the new node is the finite-residue-extension-implies-closed direction for a fibre point, whereas the existing node is the converse isolated-point-implies-finite-residue-field statement over a field.

`lem-trf-isomorphism-completion-approximation` vs existing nodes: no existing DAG node states the Tag 0CAV completed-local approximation with elementary neighbourhoods.

`lem-trf-completed-local-base-change` vs existing completion nodes: the new node is a scheme-point completed-local-ring base-change identification, while existing nodes concern completions of modules, quotients, or affine formal objects.

`lem-trf-completed-local-base-change` vs `lem-trf-relative-completion-etale-approximation`: the new node is only the completed local-ring identification after base change, while the item is the full relative approximation diagram.

`lem-trf-completed-local-base-change` vs `lem-pod-adic-limit-finite-modules`: scheme-point local-ring base change versus inverse limits of finite modules.

`lem-trf-completed-local-base-change` vs `def-weil-pbc-coherent-formal-modules-affine-quotient-cone`: local scheme completion versus a formal coherent-module quotient cone.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-affine-formal-map-limit-dictionary`: local-ring isomorphism versus an affine formal-map dictionary.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-affine-global-formal-comparison`: pointwise local statement versus global affine comparison.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-coefficient-subring-principal-source`: no coefficient-subring or principal-source hypotheses occur in the new node.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-coherent-formal-modules-affine-complete`: scheme local rings versus affine complete coherent modules.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-coherent-formal-modules-affine-quotient-cone`: completed stalk base change versus a module quotient cone.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-complete-local-quotient`: base change of a scheme local ring versus completion after quotienting a local ring.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-completed-affine-coherent-iso-lift`: no coherent-module lifting data is asserted.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-completion-exact-finite-modules`: local scheme base change versus exactness for finite-module completion.

`lem-trf-completed-local-base-change` vs `lem-weil-pbc-completion-finite-extension`: finite-type scheme-point identification versus completion of a finite ring extension.

`lem-trf-finite-residue-point-closed-in-fibre` vs `lem-pc-dense-separable-points`: the new node is the finite-residue-field criterion for closedness; the existing node proves density of finite separable closed points in a smooth scheme.

`lem-trf-finite-residue-point-closed-in-fibre` vs `lem-weil-pbc-etale-fibre-discrete-separable-points`: the new node concerns arbitrary locally finite-type fibres; the existing node concerns the discrete fibres of an etale morphism.

`lem-trf-smooth-point-etale-immersion` vs `lem-sbc-closed-fiber-power-series-test`: the new node is Tag 057G itself; the existing node is a later power-series test that uses 057G.

`lem-trf-smooth-point-etale-immersion` vs `lem-sbc-smooth-closed-point-local-section`: immersion slice versus a flat local section construction.

`lem-trf-smooth-point-etale-immersion` vs `lem-sbc-smooth-local-depth-two-closed-fiber-flat`: the new node has no depth or finite-morphism hypotheses and asserts only the Tag 057G slice.

`lem-trf-smooth-point-etale-immersion` vs `lem-sbc-smooth-local-depth-two-finite-flat`: immersion slice versus finite-flat extension under depth hypotheses.


`lem-trf-fixed-family-etale-span-descent` vs `lem-trf-relative-completion-etale-approximation`: inverse-limit pointed span descent with fixed targets; no formal isomorphism, regularity/Popescu construction, smooth slicing, or final etale base neighbourhood is asserted by the new node.

`lem-trf-fixed-family-etale-span-descent` vs `thm-pd-spreading-out`: 01ZM supplies object/morphism/equality descent, but does not assert etaleness at a stage, a simultaneous pointed span with fixed target families, or residue-field isomorphisms.

`lem-trf-fixed-family-etale-span-descent` vs `lem-weil-pbc-finite-diagram-lift-of-models`: the existing lemma explicitly excludes object descent and etaleness; the new node supplies a model for U and stage etaleness with pointed residue comparisons.

`lem-trf-fixed-family-etale-span-descent` vs `lem-weil-pbc-descend-etale`: eventual etaleness assumes an initial arrow already exists; the new statement constructs the source model and both arrows to the prescribed targets and retains their pointings.

`lem-trf-fixed-family-etale-span-descent` vs `lem-weil-pbc-etale-limit-finite-diagram-descent`: the latter concerns objects etale over the limit base; P_B and Q_B in the new statement need only be finitely presented, and generally are not etale over B.

`lem-trf-fixed-family-etale-span-descent` vs `lem-weil-pbc-etale-finite-data-descent`: all diagram objects there must be etale over the base; that excludes the possibly positive-dimensional families P_B and Q_B here, and it does not give the residue-field conclusion.

`lem-trf-fixed-family-etale-span-descent` vs `lem-sbc-smooth-pushout-filtered-colimit-stage`: this ring result detects eventual smoothness of one given pushout; it does not descend a source and two arrows with fixed targets and pointings.

`lem-trf-fixed-family-etale-span-descent` vs `new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux`: this is an epimorphic comparison of residue triples for prime localization, not a fixed-target scheme-span descent theorem.

`lem-trf-fixed-family-etale-span-descent` vs `lem-sbc-affine-limit-smooth-stage`: eventual smoothness of a pre-existing morphism, with Noetherian stages, does not construct the two pointed etale arrows to fixed families.

`lem-trf-fixed-family-etale-span-descent` vs `lem-sbc-generic-open-finite-etale-model`: spreading out a finite G-torsor from a generic fibre requires an integral Noetherian base and concerns a single finite cover, not the present general inverse-limit span.

`lem-trf-fixed-family-etale-span-descent` vs `new-lem-sbc-etale-triples-prime-localization-cocone-restriction`: this asserts restriction of compatible cocones for prime-localized residue triples, not descent of two prescribed families and their common neighbourhood.

`lem-trf-fixed-family-etale-span-descent` vs `lem-sbc-galois-cover-base-change`: this is base change of a given finite G-torsor, not finite-stage descent of a general etale span.

`lem-trf-fixed-family-etale-span-descent` vs `new-def-sbc-etale-triples-prime-localization-cocone-relation`: this defines a cocone compatibility equation; it asserts no geometric descent theorem.

`lem-trf-fixed-family-etale-span-descent` vs `lem-sbc-galois-cover-stage-descent`: this descends a finite G-torsor over the base, not arbitrary etale arrows to two possibly non-etale fixed targets, and does not give the pointed residue comparisons.

`lem-trf-fixed-family-etale-span-descent` vs `lem-sc-cofiltered-affine-etale-model`: the source is etale over the limit base in that statement; here only the two arrows to the possibly non-etale families are etale.

`lem-trf-fixed-family-etale-span-descent` vs `new-lem-sbc-etale-triples-prime-localization-comparison`: this is a universal cocone comparison for prime localization with prescribed ring-algebra structures; it is not geometric stage descent with fixed target families.

`lem-trf-fixed-family-etale-span-descent` vs `new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-pointing`: this preserves a residue-triple pointing equation after a ring-map model is supplied; it does not construct the common etale source and fixed-target scheme arrows.

`lem-trf-fixed-family-etale-span-descent` vs `lem-sc-generic-pointed-etale-cofinality`: initiality for geometric pointed neighbourhoods of the generic field of an integral scheme; it has no two fixed finite-presentation target families or actual span descent assertion.

`lem-trf-fixed-family-etale-span-descent` vs `lem-sc-generic-pointed-etale-extension`: extends a single geometrically pointed neighbourhood of a function field after integral-base restriction; it does not descend a two-target elementary span in a general affine inverse system.

`lem-trf-fixed-family-etale-span-descent` vs `lem-nagata-one-affine-subring-extension`: extends finite affine gluing subring models across one added affine chart; it asserts neither stage etaleness nor pointed spans with prescribed target models.

`lem-trf-fixed-family-etale-span-descent` vs `thm-pqf-immersion-descent`: factors an open in a relative normalization through an immersion into one finite approximation stage; it does not construct a common etale source for two fixed target families.

`lem-trf-fixed-family-etale-span-descent` vs `lem-pc-bounded-complex-base-change-enlargement`: base change of bounded module complexes is a different type of object and explicitly asserts no inverse-limit descent.

`lem-trf-fixed-family-etale-span-descent` vs `lem-pc-proper-flat-single-noetherian-descent`: a proper morphism with a flat module is spread to a Noetherian model after an open restriction; the present statement needs no properness or module, and keeps both supplied targets fixed.

`lem-trf-fixed-family-etale-span-descent` vs `lem-pd-finite-separable-datum-refinement`: refines a scheme descent datum over a separable closure to a finite separable extension; the new lemma concerns etale span descent over affine inverse systems with residue comparisons.

`lem-trf-fixed-family-etale-span-descent` vs `lem-pd-finite-separable-scheme-model`: constructs a single scheme model over a finite separable subfield; there are no prescribed target models, two etale arrows, or marked residue comparisons.

`lem-trf-fixed-family-etale-span-descent` vs `lem-pd-finite-separable-universal-transport-model`: descends a universal transport for a separable-closure descent datum; it does not give fixed-family pointed etale spans over an affine inverse limit.

## Review by Q75

I read the complete returned review.md for immutable head fd3b71f0bbe5, compared every retained sandbox node against its returned snapshot and the current shared DAG, and retained the work rather than replacing it with a rebase-only push. The four tools are absent from current main; the item there is unsplit. The item statement in this repair is byte-for-byte unchanged. I read the chapter/unit records and the three-level route requirements; this is the historical geometric auxiliary, following 0GDX, with no claim to settle the ancestor's separate trace-formula argument.

For the item I reread more-morphisms.tex Tag 0GDX (`lemma-relative-map-approximation-pre`), all its hypotheses, conclusion and proof, including its explicit definitions X_i=X×_S S_i and Y_i=Y×_T S_i. For the retained tools I read Tag 0CAV (`lemma-isomorphism-approximation`), Tag 057G (`lemma-slice-smooth`), and morphisms.tex Tags 01TE/01TF. For the completed-local base-change tool I checked the first paragraph of 0GDX and the completion algebra statements: this is not an application of finite-module completion to an arbitrary finite-type algebra as if it were a finite module. Modulo the r-th power of the stalk maximal ideal, the base maximal ideal acts nilpotently, so the action factors through A/m^r; completion leaves that quotient unchanged. Passing to these local quotients and their inverse limit is the intended independent proof of this statement-only tool. No proof is hidden inside its statement.

For the new fixed-family lemma I read limits.tex 01ZM (`lemma-descend-finite-presentation`), in particular its affine-algebra first paragraph and clauses (1),(2), and 07RP (`lemma-descend-etale`) with its qcqs/locally-finite-presentation hypotheses. Its future proof descends the affine finitely presented algebra of U only, then its two maps to the fixed finitely presented target algebras, passes to a common stage, and applies eventual etaleness to those maps. For affine finitely presented algebras C,D over R, any R-algebra map C→D is finitely presented: choose finite presentations over R and adjoin the finitely many equations identifying the generators of C with their images in D. Thus both initial stage arrows meet 07RP. The marked points are images, not an additional output of an unpointed descent lemma. Since kappa(s_j)→kappa(b) is an isomorphism, the fibres of the actual pullbacks are identical, giving the point residue isomorphisms. Their compatibility with the two arrows yields the elementary neighbourhood conclusions. This is a nontrivial independent descent lemma and is deliberately statement-only here.

I opened every statement used in the nine item steps. Step 1 uses exactly the integer-excellence/permanence, Noetherianity, finite-type-to-finite-presentation and open-immersion/composition statements it cites, with excellence expanded by its definition. Step 2 checks all completion hypotheses before 0CAV; the point x_B is the one over (x,b), and the isomorphism is inverted into 0CAV's direction. Step 3 checks the Noetherian fibres needed by regular composition and both Noetherian rings for Popescu; its filtered category is small before directed reindexing, and the affine-limit node supplies the scheme limit. Step 4 is the elementary field sandwich with its actual maps. Step 5 applies the finite-presentation limit factorization over Spec Z, checks finite presentation on the chosen affine charts, fixes both canonical families, and shrinks U without losing etaleness. Step 6 supplies each hypothesis of the new fixed-family descent node and uses precisely its conclusions, with no arbitrary-model comparison. Step 7 checks closedness of the fibre point and the identity finite separable residue extension before the 057G slice; the immersion definition gives the open shrink on which it is closed. Step 8 explicitly proves the two Cartesian identifications by their test-scheme universal property before invoking etale base change/composition. Step 9 is the elementary quotient tensor calculation giving the marked point and residue field. I regenerated one verbatim full-statement quote for every citation in every step.

Small cases checked: identity families over Spec Z; the smooth affine line at a rational point; a finite separable point for 057G; a purely inseparable finite residue extension for 01TE; a generic point of A1 over a field, where the finite-residue hypothesis fails; and a point not closed in a finite-type fibre for completed-local base change, which must not gain a finite-residue hypothesis. For the new lemma, constant systems and identity spans work, and a nontrivial base residue extension is excluded exactly by its explicit residue-isomorphism hypothesis. I reran the review's Fp[t,z] counterexample and verified that the invalid source/target models are excluded, rather than assuming etale permanence could repair them. There is no SGA source and no coefficient-category or base-change-mate identification in this algebraic-geometric auxiliary.

The comparison of source tags and candidate node statements is recorded above. The new lemma is neither elementary nor a clause of the item: it is the independent fixed-family pointed descent fact requested by the review. All five new nodes are self-contained statements, all three blueprint fields are filled, searches have actual logged commands and inspected results, and no long proof step hides a comparison. The initial retained-version dry run was run before editing; final server checks and push follow this report.
