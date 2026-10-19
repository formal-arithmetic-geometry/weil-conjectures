# Worker report: lem-pur-diagonal-base-change

## Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-diagonal-base-change.json`: statement, split into five proof steps; Mathlib searches find no match for the complete assertion. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every node used in each proof step.
- `report.md`: this report. `searches.jsonl` was written by the required search command. The temporary preparation script was removed after the explicit source/citation audit.

## Attachments

None. I searched all of `WeilConjectures/` in the read-only slopmaster2 checkout for the item id, the diagonal/dualizing terminology, and the possible base-change declarations. The three tagged declarations are `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_pullbackFst` (Smooth/Basic.lean:178), `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_pullbackSnd` (:192), and `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_diagonal` (:209), in `WeilConjectures/EtaleCohomology/Purity/Smooth/Basic.lean`. Their bodies contain no direct `sorry`, but each reaches the `sorry` in `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek` (:132–143). I traversed the dependency entries in `local/sorry_map_slopmaster2_7d675a26.jsonl.gz` to confirm this, rather than treating a body without `sorry` as finished. Each reaches two directly sorried declarations.

There is also a statement mismatch: these are `Nonempty` existence assertions in the ordinary small-etale category, whereas the item concerns the specified base-change comparisons in the chapter's pro-etale coefficient framework. The file's Implementation notes expressly say the canonical transformation has not been provided. I therefore do not assert an attachment, and have not used master-reference `sorry` declarations as proof evidence.

## Wanted sources

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-smooth-purity/lem-pur-diagonal-base-change.md`, statement and Proof, for lem-pur-diagonal-base-change. Its complete imported statement and proof were read in the DAG JSON; the separate source file is absent from this checkout.

WANTED: `literature/stacks-project/morphisms.tex`, Tags 01VB (lemma-base-change-smooth), 02NK (lemma-base-change-relative-dimension-d), and 01T4 (lemma-base-change-finite-type); `literature/stacks-project/schemes.tex`, Tags 01JP (definition-fibre-product), 01KK (definition-separated), 01KU (lemma-separated-permanence); `literature/stacks-project/sites-cohomology.tex`, Tag 0D6D (lemma-derived-pullback-composition), for the source checks underlying the cited existing geometric and pullback-composition interfaces. These files are absent locally. Their precise statements and source labels were read in the existing nodes; no unobserved source reading is claimed and nothing was downloaded.

## Corrections and route

The mathematical hypotheses and conclusions are retained. I introduced the diagonal explicitly, identified the existing definition of the section invariant, and repaired the reference that treated `def-pur-co-smoothness` as a proof that smooth morphisms satisfy cohomological smoothness. The theorem actually supplying the canonical base-change isomorphism is `thm-pur-cohomological-smoothness`, clause Base change. Its statement supplies exactly the orientation-free comparison needed here, without using the later smooth-purity identification with a twist and shift.

The original dependency lists omitted the section-invariant definition and cited an unused etale-local normal-form theorem. I added the actual notion dependencies, used the theorem and the existing pro-etale composition interface, and removed the unused normal-form and direct tensor dependencies. The statement's direct references to general scheme properties were replaced by the actual definitions of separatedness and the fibre product, rather than using the properties index as a definition. All imported `blueprint_*` metadata and `import_flags` were preserved.

This is exactly Step 1 of unit `sk-thm-smooth-purity`, not a replacement of that unit's diagonal/deformation/vector-bundle route. The item is not the unit's key theorem, so I changed no unit realization fields. Its blueprint identity is itself, `from` remains null, and `same_as=[]` records the whole-blueprint searches. Searches for “co-smooth”, “smooth base change”, “section invariant”, “pullback composition”, “derived pro-etale module pullbacks”, and “dualizing object of a projection” located the existing tools and no second blueprint node stating the whole item. Generic off-unit smooth-permanence, derived-pullback-composition and isomorphism-inverse-image tools are declared in `split_report.tool_uses`; the geometric separated-finite-type permanence node is already a Mathlib leaf.

## Mathlib searches

All six recorded queries were actually run with `/home/ubuntu/weil-launcher-nt/msearch.py NV lem-pur-diagonal-base-change`, and the actual hits were read. LeanFinder was tried with two different formulations. The first returned diagonal and affine-pullback descriptions; the second returned sheaf-module pullback/free-unit comparisons. Loogle found `AlgebraicGeometry.instSmoothFstScheme` for the geometric smoothness ingredient; its type proves smoothness of a pullback projection only. A second Loogle query for “dualizing” returned zero hits, and the source grep for `dualizingComplex|sectionInvariant|upperShriek` returned zero hits. LeanSearch returned Internal Server Error and is recorded as unavailable, not as negative evidence. No result states exceptional base change or the complete diagonal dualizing assertion. The existing smooth-permanence node already supplies the geometric ingredient, so its presence in Mathlib does not justify a new duplicate leaf.

## Not duplicates

No new nodes. Every non-elementary ingredient is an existing statement; the few-line diagonal identities and functorial image of an isomorphism remain proof steps. In particular I created no node that restates either projection formula or the final diagonal conclusion.

## Review by NV

I read the chapter and unit records, the imported item statement and complete original proof, the complete statements of all nodes cited below, and the Lean source described above. The missing original literature is disclosed under Wanted sources; this is an agent-written expansion, not a claim to have read an unavailable Stacks file. No new statement requires an unverified new source or a new-node search.

Step 1 uses `def-pc-fibre-product` for the universal pair and its two projection equations; substituting both identity maps explicitly proves the two section identities. `def-weil-proper-morphism` defines separatedness by this very diagonal being closed, so there is no inference from set-theoretic image containment to factorization. `lem-sbc-smooth-relative-dimension-permanence` clause (1) states preservation of the SAME fixed relative dimension under ANY base change. `lem-pod-separated-finite-type-base-change` states the required separatedness and finite-type preservation. `def-weil-exceptional-inverse-image` is cited for the ambient typing: the finite-type setting is the one already required by the chapter's exceptional-inverse-image notation (finite-type schemes over the fixed field), not an extra properness or finite-presentation hypothesis on the item. Both projections are base changes of f; the square and the second copy are labelled consistently.

Steps 2 and 3 both use the Base change clause of `thm-pur-cohomological-smoothness`. I checked the entire clause, not its definition: it explicitly gives `Lu^* omega_f -> omega_f'` as an isomorphism for arbitrary base map v. The first substitution is `(u,v,f')=(p2,f,p1)`, the second `(p1,f,p2)`. Taking the inverse accounts for the orientation in the item's displays. Smoothness, separatedness and relative dimension are hypotheses on the original f exactly as in the theorem. There is no claim that smoothness alone implies proper base change, no use of an unbounded pro-etale ambient right adjoint, and no later twist/shift purity theorem is invoked.

Step 4 uses only the displayed formula in `def-pur-section-invariant`: `C(g,s)=Ls^* omega_g`. Step 1 supplies its smooth map and closed-section hypotheses. The rest is elementary: applying the pullback functor to the mutually inverse maps of Step 2 gives mutually inverse maps. The definition is not cited as a theorem about arbitrary base change.

Step 5 uses `def-pur-conventions` to specify the finite-coefficient claim and its separately transported higher versions. `lem-weil-pbc-proetale-derived-pullback-composition` states the canonical derived MODULE pullback composition on the pro-etale site itself, with the correct constant ring sheaves and the compatibility of the composite identification as a hypothesis. `def-weil-proetale-inverse-image` explicitly constructs the coefficient structure map by extending the constant-presheaf map sending a to the constant section a. This makes the composite identification correct: the maps agree on that presheaf and therefore on its sheafification. `lem-weil-proetale-isomorphism-inverse-image` clause (1), specialized to the identity scheme isomorphism, gives an objectwise natural identification with the same sheaf; I do not merely infer an identity comparison from an abstract equivalence. `def-weil-derived-pullback-tensor-hom` states that finite-level derived pullback is exact inverse image applied termwise to any representative, so this sheaf-level identity gives the derived identity without a new resolution theorem. This closes the calculation on the actual pro-etale coefficient category, with no silent identification with the Lean source's etale category. The canonical comparison is the explicit composite of these maps.

For sections B–E of delivery-errors: there are no new nodes, so no statement-only, duplicate, or leaf-declaration obligations are hidden. Each actual use has a verbatim quote in citations.json; proof_deps is exactly their union. The only wholly elementary step is applying a functor to the already obtained isomorphism. I checked the dependency graph from every used statement for a return path to the item; there is none. The geometric and coefficient hypotheses above are all in force in their applications. Small cases checked: f is the identity (d=0), an etale f (d=0 with a possibly non-surjective diagonal), the empty source, and a smooth projection of positive dimension. Both projection equations and the final pullback along the diagonal still have the displayed types in all these cases. In particular no nonempty fibre, connectedness, or surjectivity hypothesis was introduced. I paired every search summary with its exact logged tool and query, correcting an initial completion-order mismatch. I corrected the definition-for-theorem citation, the missing notion dependencies, the unused proof dependency, and the previously unstated identity-pullback argument during this self-review.

### Resumption self-review by NV, 2026-10-16

I reread the chapter and unit records, the live imported item, and every direct statement and proof dependency. The route is still the unit's first step: orientation-free cohomological smoothness for the projections, followed by restriction along the diagonal. In particular `thm-pur-cohomological-smoothness` supplies arbitrary base change as a theorem; the definition of cohomological smoothness alone cannot establish that a smooth morphism has this property. Both substitutions into its Base change clause are correctly typed, with the same original smooth separated morphism and no properness assumption.

For Step 1 I opened the actual sandbox Stacks sources at `schemes.tex` labels `definition-fibre-product` (01JP), `definition-separated` (01KK), `lemma-separated-permanence` (01KU), and `morphisms.tex` labels `lemma-base-change-smooth` (01VB), `lemma-base-change-relative-dimension-d` (02NK), `lemma-base-change-finite-type` (01T4), and `definition-finite-type` (in section 01T0). I matched these with the complete statements of the existing geometry nodes. The source's relative-dimension result assumes locally finite type, which holds for the smooth original map; both projections are its base changes. The separatedness definition supplies the closed diagonal directly. I found one implicit typing argument and repaired it: since the exceptional inverse image is defined for finite-type schemes over the fixed field, Step 1 now proves that the self-product has this property by a finite affine cover, with finitely generated coordinate algebras. This cites `def-weil-finite-type-morphism`; the elementary union-of-generators argument replaces an unstated use of finite-type composition. No additional lemma node is justified.

Steps 2 and 3 use precisely the complete Base change clause quoted in citations.json, with `(u,v,f')=(p_2,f,p_1)` and `(p_1,f,p_2)`. Step 4 uses precisely `C(g,s)=Ls^*omega_g` from `def-pur-section-invariant`; applying the already constructed isomorphism and its inverse through a functor is elementary. For Step 5 I read `sites-cohomology.tex`, `lemma-derived-pullback-composition` (0D6D), including its K-flat-complex argument, and compared it to the full pro-etale derived module composition node. I checked the required composite ring identification against the definition of the constant-coefficient structure maps: both send each constant to itself under the explicitly given fibre-product identification. The inverse-image-isomorphism node gives the objectwise identity comparison on sheaves and the coefficient compatibility, while the finite-level derived-pullback definition computes it termwise on complexes. Thus this last step remains on the pro-etale module category of the item; the small-etale Lean existence results are not being substituted for it.

I reran the required Mathlib searches with two fresh LeanFinder phrasings, Loogle `"dualizing"`, and grep `dualizingComplex|sectionInvariant|upperShriek`. The two semantic searches returned only ordinary structure-sheaf module pullback/pushforward comparisons and relative differentials, whose printed types I read; none provides this item. Loogle and grep returned zero hits. The new LeanSearch request returned Internal Server Error, recorded as unavailable. The exact fresh queries and observed results are in the node and the command's log. Whole-blueprint searches for dualizing and section invariant identify the existing theorem and definition already used, with no second node for this item; no new nodes were created.

For B--E, every new non-elementary use is still a citation of an existing statement, and the sole added citation is the finite-type definition with its complete verbatim statement. The original 13 pairs and the added pair give 14 citation pairs. Their quotes were checked as literal substrings, all direct dependencies exist and are unmerged, and proof_deps is precisely the union of step uses. The dependency traversal finds no path back to the item; the 11 inherited missing transitive ids are baseline defects, not introduced dependencies. All imported flags and blueprint metadata remain unchanged. The statement is unchanged from the previous sandbox split and has no additional hypothesis or weakened conclusion.

I checked the identity map, a two-sheet finite etale map, the empty source, and the affine-line projection. The equations for both diagonal composites and the comparison types work in each case; no diagonal surjectivity, positive dimension, or nonempty-source hypothesis is used. The newly explicit affine-cover argument handles an empty cover, and uses only finitely many algebra generators for each nonempty affine chart. All finite coefficient indices n>=1 remain allowed.

The previous report's stage-2 routing diagnosis is historical. This invocation follows the current explicit stage-1 brief, which requires no Lean work and no push. The historical second-reading section is retained as provenance, and is not a substitute for the fresh second reader required after this handoff. No agents were started, no live file was written, and no direct git or compilation command was run.

## Unfinished work

No split argument is left unfinished. Original literature verification remains limited by the absent files listed above; the next reader can assess the explicit argument and every cited statement independently. Nothing has been pushed; the sandbox is for the required fresh second reader.


## Earlier second reading (a previous round; superseded)

Item statement: checked every hypothesis and both projection comparisons against the imported item and the unit `sk-thm-smooth-purity`, first paragraph, Step 1; the explicit diagonal and section-invariant references only bind previously implicit notation. The finite-type-over-a-field and finite-coefficient ambient hypotheses come from `def-pur-conventions` and `def-weil-exceptional-inverse-image`; no properness, surjectivity, nonempty-source, or extra smoothness assumption is needed. PASS. The separately named blueprint Markdown source remains absent: the exact pinned raw-GitHub path returned HTTP 404, so this review uses its imported statement/proof and does not claim to have read that missing file.

Step 1: read the complete statements of `def-pc-fibre-product`, `def-weil-proper-morphism`, `lem-sbc-smooth-relative-dimension-permanence` clause (1), `lem-pod-separated-finite-type-base-change`, and `def-weil-exceptional-inverse-image`; checked against Stacks 01JP `schemes-definition-fibre-product`, 01KK `schemes-definition-separated`, 01VB `morphisms-lemma-base-change-smooth`, 02NK `morphisms-lemma-base-change-relative-dimension-d`, 01KU `schemes-lemma-separated-permanence` clause (3), and 01T4 `morphisms-lemma-base-change-finite-type`. Both projections have the required smoothness, dimension and separated finite-type hypotheses, and the diagonal is a closed section by its two projection equations. Expanded the reversed Cartesian square explicitly. PASS after repair.

Step 2: read `thm-pur-cohomological-smoothness`, including its relative-dimension hypothesis and Base change clause; the substitution `(u,v,f')=(p_2,f,p_1)` has the required Cartesian square, and inversion gives the direction displayed in the item. This is the orientation-free theorem in the unit's cited `sk-prop-cohsm`; no Tate-twist purity is used. PASS.

Step 3: checked the same theorem's full statement with `(u,v,f')=(p_1,f,p_2)` and the explicitly reversed square of Step 1; inversion gives the other projection comparison without assuming a proper base map. PASS.

Step 4: read `def-pur-section-invariant` in full: its required smooth morphism and closed section were established in Step 1, and its displayed formula is exactly the formula used. The inverse equations for the isomorphism from Step 2 remain inverse equations after applying a functor, by preservation of identities and composition; this is a few-line elementary step. PASS.

Step 5: read the full statements of `def-pur-conventions`, `lem-weil-pbc-proetale-derived-pullback-composition`, `def-weil-derived-pullback-tensor-hom`, `def-weil-proetale-inverse-image`, and all three clauses of `lem-weil-proetale-isomorphism-inverse-image`; compared the composition claim with Stacks 0D6D `sites-cohomology-lemma-derived-pullback-composition`, including its K-flat proof. The cited composition node concerns module pullbacks on these pro-etale sites and gives the composite coefficient identification as a hypothesis. Expanded the direct-image fibre-product identification and agreement on constant sections before taking adjuncts, and made the identity comparison's compatibility with the module action explicit. Exact termwise finite-level pullback then gives the identity on complexes and hence on the derived category. The assertion is made at finite coefficients as the conventions require; no extra coefficient-transport theorem is asserted. PASS after repair.

New nodes: none. Thus B1--B7 introduce no additional statement, definition, source, Mathlib-leaf, or self-containment obligations. The existing generic dependencies are strictly smaller facts, not renamed clauses of this item; there is no new fact to delete or convert to a leaf. The geometric permanence leaf was reused. The requests for the maintainer to recognize generic off-unit tools remain in `split_report.tool_uses`, not in the maintainer-owned top-level `tool_uses` field.

Independent searches: ran the logged LeanFinder query beginning “Pullback functors on derived categories of sheaves compose canonically”, Loogle `CategoryTheory.Functor.mapIso`, and the logged grep for dualizing/exceptional terminology. LeanFinder found ordinary sheaf-module comparisons (`SheafOfModules.pullbackComp`, `pullback_id_comp`); I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` at lines 139, 167--183 and 208--216. They do not state smooth exceptional base change or the complete item. Loogle's `mapIso` is the elementary functor argument of Step 4 and warrants no node. The ten grep hits concern duality in unrelated contexts. No new Mathlib leaf is justified. Whole-DAG blueprint keyword searches for dualizing, section invariant and pullback composition found no additional blueprint statement equal to the item. Read the three tagged declarations in `WeilConjectures/EtaleCohomology/Purity/Smooth/Basic.lean` at lines 178, 192 and 209, and their sorried base-change dependency at 132--143: their existential small-etale assertions do not provide the canonical pro-etale comparison required here and are not finished-proof attachments.

Small cases: for the identity of `Spec(k)` and a finite etale map (dimension zero), both diagonal equations and all three comparison types hold; a finite etale map with two sheets confirms that no surjectivity of the diagonal is used. For the empty source they remain valid with vacuous dimension conditions. For `A^1_k -> Spec(k)` (dimension one) the self-product is `A^2_k`, and the two coordinate projections and diagonal give the stated compositions. The zero module complex is fixed by the identity/composition comparisons. The coefficient index is `n >= 1`; `n=1` is permitted throughout and no inverse uniformizer is used.

Dependency and citation audit: independently traversed statement and proof edges below every used node and found no return path to this item. Opened every cited statement and kept each citation quote verbatim; enlarged the identity-inverse-image quote to include its module and coefficient clauses. Every non-elementary inference is supplied by a cited statement, and the only wholly elementary step remains Step 4.

Changes: expanded the reversed Cartesian-square lift to avoid an implicit factor-swap argument; expanded composition of coefficient maps and compatibility of identity pullback with module actions; enlarged its citation quote; recorded the independent searches and this reading; updated `proof_origin` to distinguish verified Stacks sources from the unavailable blueprint file. The worker's other sections and conclusions are retained. I located the complete Stacks sources read-only at `/home/ubuntu/c1-stacks-review/` and verified tag/label pairs in its `tags/tags`; also retrieved the three relevant `.tex` files into this sandbox's `sources/`. This resolves the Stacks-only source limitation reported by the first reader; the blueprint limitation remains disclosed. No live files were modified and no Lean files were written; no compilers, builds, or agents were started.


## Historical returned-delivery audit by NV (2026-10-16)

I read the complete immutable review of head 5275494abfd9, not just the
condensed return. Finding 1 requests a substantive stage-2 formalization;
finding 2 requests the exact worker heading and a fresh independent reading
of that formalization; finding 3 requests declaration docstrings and successful
per-file compilation. The exact `## Worker report` heading is now present.
The other findings are NOT repaired by the existing natural-language split,
its citation file, or its historical second reading. In particular no Lean
signature record, docstring, independent Lean reading, or compile evidence
is claimed.

The dispatched brief still explicitly says “only stage 1” and “Never write
Lean or run any compiler/Lake/build tools”, and directs the worker to
`deliver.py ... --no-push`, while the return and the production launcher
README demand stage 2. The launcher also has `STOP_STAGE1`, whose content
says to keep stage-1 dispatch/review stopped. This is a stage-routing
contradiction, not a mathematical counterexample or a missing attachment.
I have left the stage-1 payload intact apart from this report rather than
fabricating a stage-2 declaration record or compiler evidence.

For the allowed source audit I reread the current chapter and unit, every
statement cited in the five proof steps, and the three tagged upstream
assertions in `WeilConjectures/EtaleCohomology/Purity/Smooth/Basic.lean`.
The upstream assertions remain ordinary small-etale `Nonempty` comparisons
and use the directly sorried base-change theorem. They do not attach this
canonical pro-etale statement. The current side pro-etale `Derived/UpperShriek`
defines the exceptional inverse image through etale transport, so replacing
it by an arbitrary ambient adjoint would not repair the return.
The finite-coefficient convention, closed diagonal, both factor orderings,
and the composition/identity comparisons used in the split agree with the
current cited statements. No new node or Mathlib leaf has been created.

The prescribed stage-1 dry run completed with:

```text
OK (not pushed) deliver/NV/lem-pur-diagonal-base-change at a0498896ea: preflight passed
```

All 13 step/node citation pairs were checked against the current dependency
statements; their quotes are verbatim after whitespace normalization. This
stage-1 preflight result does not resolve the stage-2 return. No delivery was
pushed, and no compiler was invoked. The dispatcher must route this return
to a stage-2 worker with the corresponding authorization and delivery wrapper.


## Dispatch repair recheck by NV (2026-10-16)

This invocation received the same stage-2 return for immutable head
5275494abfd9, together with the explicit instruction that only stage 1 is
authorized and that Lean writing and all compilation are forbidden. The
return is not satisfied; this is a BLOCKED routing result, not READY.

H1/H2: the sandbox has zero Lean files and the item has no `lean` record.
A complete canonical pro-etale signature, usable Lean dependency interfaces,
and a verbatim signature record require stage-2 work. The supplied
`deliver.py` is a stage-1 packager: it collects `dag/nodes/*/*.json` and
`report.md`, preserves maintainer-owned `lean` fields from the baseline, and
runs preflight without `--stage 2`. It cannot deliver the requested Lean
payload. Its stage-1 success therefore cannot repair H1/H2.

H1/H11: the exact `## Worker report` heading is present. The historical
`## Earlier second reading (a previous round; superseded)` section reads the natural-language split and
sources; it is not a reading of a Lean file. This invocation is the repair
worker, not a fresh independent second reader. No new Lean reading is
claimed. Required declaration docstrings and per-file `scompile.py`
evidence likewise remain absent because producing them would violate the
explicit stage-1 restriction in this invocation.

For the permitted stage-1 check, I reopened all statements cited by the five
steps and reread the available source excerpts in `sources/schemes.tex`
(fibre products, separatedness, and its base-change permanence),
`sources/morphisms.tex` (finite type, smoothness, and relative dimension
under base change), and `sources/sites-cohomology.tex` (derived pullback
composition). They support the existing geometric and composition steps.
In steps 2 and 3, `thm-pur-cohomological-smoothness` explicitly supplies the
canonical dualizing base-change comparison for arbitrary base map; the
two projection substitutions use its actual hypotheses. Step 4 uses the
section-invariant formula and functoriality; step 5 uses the pro-etale
module-pullback composition interface, not an etale replacement. The
identity, empty-source, and positive-dimensional projection cases introduce
no extra hypothesis. I reread the three tagged slopmaster2 declarations and
their sorried base-change dependency: they remain existential small-etale
assertions, so they cannot attach this canonical pro-etale item.

The current citation audit passes all 13 step/node pairs and confirms that
`proof_deps` is exactly the union of step uses. No present dependency has a
return path to the item. A stronger traversal requiring every inherited
transitive dependency to exist stopped at an unrelated missing baseline id;
a subsequent traversal recorded 11 such inherited missing ids. I do not
claim that the entire shared DAG is free of missing dependencies. None of
the item's direct dependencies is missing or merged. No new node, Mathlib
leaf, search record, or mathematical statement was created in this repair.
Only this report was changed, and no delivery is authorized to be pushed.

Stage-1 dry-run evidence for this invocation: the required command
`python3 /home/ubuntu/weil-launcher-nt/deliver.py NV lem-pur-diagonal-base-change --no-push`
exited successfully and printed
`OK (not pushed) deliver/NV/lem-pur-diagonal-base-change at c856a1241c: preflight passed`.
This is DAG preflight evidence only; no `scompile.py`, Lean compiler, Lake,
or build command was run. The report is rerun through the same dry run
after recording this result. That was the previous invocation's routing diagnosis. The current explicit stage-1
brief requires an accepted dry run and handoff to a fresh reader, and does not
require repairing stage-2 Lean deliverables. It therefore does not block this
stage-1 handoff. No stage-2 repair or compilation is claimed.

## Current stage-1 validation

The final sandbox payload is checked with `python3 /home/ubuntu/weil-launcher-nt/deliver.py NV lem-pur-diagonal-base-change --no-push`. This handoff is stage 1 only: no new nodes, no new Mathlib leaves, and nothing pushed.

The current first dry run failed at DAG delta preflight with findings on unrelated nodes, including `lem-sc-valuation-closed-fibre-divisibility` (a step use absent from proof_deps), `new-module-cup-derived-homology-tensor` (a missing dependency), `def-weil-pbc-strict-henselization-limit` (several step uses absent from proof_deps), and missing dependencies under `lem-exc-etale-lift-separably-closed-factorization` and the `lem-sc-square-zero-*` family. None is in this payload, which changes only this item and its report. I have not edited unrelated nodes or tool code. The required command is retried once to refresh its delivery base.


## Second reading by NV

This is a fresh independent stage-1 reading of the sandbox split. The imported statement and unit `sk-thm-smooth-purity`, Step 1, agree with both projection comparisons and the diagonal conclusion, hypothesis by hypothesis; the diagonal and section-invariant references only bind existing notation. The original blueprint Markdown is absent, so I checked its imported statement/proof and the read-only slopmaster2 docstrings, without claiming access to that Markdown. I read the sandbox Stacks sources and independently matched all seven tag/label pairs against `/home/ubuntu/c1-stacks-review/tags/tags`.

Step 1 — PASS against complete statements of `def-pc-fibre-product`, `def-weil-proper-morphism`, `lem-sbc-smooth-relative-dimension-permanence` (1), `lem-pod-separated-finite-type-base-change`, `def-weil-exceptional-inverse-image`, and `def-weil-finite-type-morphism`; Stacks 01JP `schemes-definition-fibre-product`, 01KK `schemes-definition-separated`, 01KU `schemes-lemma-separated-permanence` (3), 01VB `morphisms-lemma-base-change-smooth`, 02NK `morphisms-lemma-base-change-relative-dimension-d`, and 01T4 `morphisms-lemma-base-change-finite-type` support precisely the uses. Smoothness supplies local finite type for 02NK. Both Cartesian squares and both section equations are explicit; finite type over the field follows from the written finite-cover union-of-generators argument.

Step 2 — PASS against the full statement of `thm-pur-cohomological-smoothness`, Base change, and unit `sk-thm-smooth-purity` Step 1: `(u,v,f')=(p_2,f,p_1)`, with the original smooth separated dimension-d map, gives the canonical isomorphism; taking its inverse accounts for the direction in the item. No properness or orientation is required.

Step 3 — PASS after making the hypotheses explicit, against the same full Base change statement: the reversed Cartesian square has `(u,v,f')=(p_1,f,p_2)`; the original map remains smooth separated of pure relative dimension d, and the base map is arbitrary. This is the second comparison, with its inverse direction recorded.

Step 4 — PASS against the complete `def-pur-section-invariant`: Step 1 supplies its smooth morphism and closed section. Applying a functor to the isomorphism and its inverse gives inverse maps because their two composites are the functorial images of identities. This is elementary and does not make a new lemma necessary.

Step 5 — PASS against full statements of `def-pur-conventions`, `lem-weil-pbc-proetale-derived-pullback-composition`, `def-weil-derived-pullback-tensor-hom`, `lem-weil-proetale-isomorphism-inverse-image`, and `def-weil-proetale-inverse-image`, and Stacks 0D6D `sites-cohomology-lemma-derived-pullback-composition` including its K-flat argument. The written fibre-product maps identify composite direct images, both constant-presheaf maps send a to a, and taking adjuncts supplies the required composite coefficient identification. The identity inverse image is naturally the identity on module sheaves; exact finite-level pullback computes it termwise on complexes. The finite-level convention is now included in the verbatim quote.

New nodes — NONE; no statement-only, definition-reference, TeX, source, duplicate or Mathlib-leaf defect is introduced (B1–B7). The two projections and the final diagonal comparison are proved in steps, rather than moved into new nodes. Existing generic tools remain declared in `split_report.tool_uses` for maintainer review.

Small cases — PASS for the identity of Spec(k), a two-sheet finite etale map (d=0 with nonsurjective diagonal), the empty source, and the affine-line projection (d=1). The projection and section equations are correctly typed in each; no positive-dimension, nonempty-source, diagonal-surjectivity or extra properness condition is used. The zero complex remains zero, and n=1 is allowed.

Search and attachment check — I independently ran the three fresh logged queries (LeanFinder composite module pullback/unit, Loogle `SheafOfModules.pullbackComp`, grep `dualizingComplex|sectionInvariant|rightDerivedUpperShriek|baseChange.*[Ss]mooth`) and read `PullbackContinuous.lean` lines 139–216. These give ordinary module comparisons and smoothness permanence, not the full assertion. Read slopmaster2 `Purity/Smooth/Basic.lean` lines 132–216: the three tagged existential small-etale comparisons still depend on the explicit sorry at the base-change theorem, so no finished-proof attachment is justified. No compiler was run.

Citation and dependency check — All 14 step/node quote pairs are verbatim after whitespace normalization, and proof_deps is exactly the union of the five step uses. All direct dependencies exist. Traversing statement and proof edges below them finds no return path to this item; the 11 inherited missing ids already disclosed by the worker remain baseline defects, not introduced edges.

Changes in this reading — Expanded Step 3's original-map, base-map and finite-type hypotheses instead of referring to the preceding application; expanded the conventions quote to include “For Lambda=A”; recorded the three independent searches and their actual results, updated the second-reading metadata, and appended this review. All worker and historical review sections are retained. No mathematical statement changed, no node was added, and no live-project or launcher file was written.

Validation for this second reading — The prescribed dry run exited 0 and printed `OK (not pushed) deliver/NV/lem-pur-diagonal-base-change at ddd54b5c80: preflight passed`. This supersedes the historical baseline-failure and stage-routing diagnoses above for this explicitly authorized stage-1 delivery. The requested delivery command follows; no Lean writing or compilation is involved.
