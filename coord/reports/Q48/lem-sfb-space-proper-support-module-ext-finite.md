# Stage-1 report: lem-sfb-space-proper-support-module-ext-finite

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-support-module-ext-finite.json: existing statement, unchanged; split into six proof steps, with complete citations and scalar compatibility. Retained all inherited searches and blueprint provenance.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-support-below-coherent-image.json: statement-only input, unsplit; bounded-below coherent direct image with proper cohomology supports, Stacks Tag 0D0R, auxiliary base S=Y. Mathlib searches found no match.
- citations.json: verbatim statement excerpts for every proof-step use.

## Attachments

None. Read-only searches of lean/WeilConjectures for the exact blueprint tag, proper-support Ext, coherent Ext and derived coherent images found no exact completed project declaration. ModuleCat.finite_ext is a Mathlib result for ordinary finite modules, not an attachment and not the result for sheaves on an algebraic space.

## WANTED

None. All sources used are available under literature/stacks-project/.

## Problems and corrections

The original item is a correct proper-support variant of Tag 0D0T; its statement and statement dependencies are unchanged. The existing proper-space coherent-derived-image node has an additional properness hypothesis on the ambient map. It cannot be applied to this item: the one new node records the more general source result with proper supports. The bounded-coherent proper-support node has an upper bound absent from derived Hom here, and cannot be applied either. In particular finite presentation does not imply that M has finite projective dimension.

The source 0D0R says that the supports are proper over its auxiliary S. In this delivery S is expressly the target Y, so no inference from properness over an unrelated base is made. This also avoids inheriting a potentially misleading base in the wording of that source.

While reviewing the draft I corrected slice restriction on a possibly nonschematic open complement to restriction on every etale scheme chart in that complement; the cited slice theorem now applies literally to objects of the small site. I also replaced draft source-tag slips for scheme finite-module support and affine etale derived realization by 056J and 071Q, checked against tags/tags. These were proof-source corrections, not statement changes.

The inherited blueprint ancestor is null: tools/blueprint_refs.py ancestor reports None. I retained this provenance and its existing via chain, with the place specified precisely. I read the latest blueprint (latest points to main-20261023-1620), det-thm-sf-ctf-stability-direct-images proof (3), and the chapter and unit records. This is an inherited moduli/alteration prerequisite of that route, not a replacement for the unit's constructibility argument. Searches of the whole DAG by 0D0R and by proper/coherent/support/derived-image notions, and blueprint_refs searches for 0D0R, proper coherent, bounded below coherent, proper support Ext, and derived image found no blueprint node stating the missing lemma. The generic site and scheme tools from other units are declared in split_report.tool_uses and do not change the route.

## Not duplicates

lem-sfb-space-proper-support-below-coherent-image vs lem-sfb-proper-space-coherent-derived-image: the existing node requires f proper; the new node assumes only f locally of finite type and individual cohomology supports proper, allowing a nonproper and non-quasi-compact ambient X.

lem-sfb-space-proper-support-below-coherent-image vs lem-sfb-space-proper-support-module-ext-finite: the item concludes finite-dimensional global Ext for two finitely presented modules over a field; the new input concerns coherence of a derived direct image of an independently specified bounded-below complex, over an arbitrary Noetherian scheme. It contains no Ext conclusion, internal Hom, or passage to global sections.

lem-sfb-space-proper-support-below-coherent-image vs lem-sfb-space-proper-support-bounded-coherent-image: the existing 08GK node assumes cohomology vanishes outside a finite interval and concludes two-sided boundedness; the new 0D0R input permits infinitely many positive cohomology sheaves and concludes only a lower bound. RHom here may have unbounded positive cohomology, so the distinction matters.

## Review by Q48

I read spaces-perfect.tex, lemma-coherent-internal-hom (0D0S), lemma-direct-image-coherent-bdd-below (0D0R), and the proof of lemma-ext-finite (0D0T). For the new node I checked the literal 0D0R hypotheses: locally finite type ambient map, Noetherian target, bounded-below coherent input, and proper support in each degree. Specializing the auxiliary scheme to Y gives precisely the new statement; no properness or quasi-compactness of the map is imported. I also read its preceding bounded version 08GK and the proper-support closed-subset lemma 0CZE. The new node carries no proof, proof dependencies or hidden proof inside its statement.

In step 1, the finite-type algebra Noetherianity node gives the actual chartwise implication, since each coordinate ring is a finitely presented k-algebra. A field is Noetherian directly by its ideals. The affine-chart calculus node says both that quasi-coherent modules are associated to chart sections and that finite presentation is tested there; thus the finite sections satisfy exactly the coherence convention stated in the internal-Hom node. This is a local argument and does not assert any finite atlas or global quasi-compactness of X. I compared this with spaces-cohomology.tex 07UB, including its equivalence of coherent, finite-type quasi-coherent and finitely presented modules.

Step 2 uses only the statement of the existing algebraic-space coherent-internal-Hom node, which expressly accepts a bounded-above coherent first argument and bounded-below coherent second argument. The two degree-zero modules satisfy these hypotheses. The output is a bounded-below coherent complex, not necessarily bounded above. This is why I did not substitute the bounded proper-support theorem in the next step.

For step 3 I opened each of its six cited node statements. Canonical module direct image is the explicit chart limit, giving zero on charts disjoint from the closed image. The general ringed-site internal-Hom restriction node states the slice isomorphism for every object and without boundedness hypotheses, so it applies to those scheme charts. I checked sites-cohomology.tex lemma-restriction-RHom-to-U (08JB), rather than borrowing a ringed-space-only statement. The etale-chart-support node gives the equality of inverse-image support with ordinary scheme support; the scheme finite-type-module support node gives V(Ann), read in morphisms.tex 056J/056I. The atlas-topology definition tests closedness on those charts. The proper-support closed-operations node states both the equivalence of a proper closed model with properness of the closed point set and inheritance by a smaller closed subset. Its local finite type hypothesis holds for f. Thus each cohomology support, not just N itself, satisfies the next theorem's hypothesis. No identification of the whole RHom complex with a closed direct image is assumed.

Step 4 checks the target Noetherianity separately: the affine qcqs node supplies quasi-compactness and quasi-separatedness of Spec(k), and the one affine chart is Noetherian. The new node then applies exactly as stated to G and these supports. The proof never applies the stronger proper-ambient specialization.

In step 5 I read the statements of the closed symmetric monoidal ringed-derived theorem, internal-Hom sections model, and derived-pushforward composition. Closedness and symmetry provide the adjoint required by the sections model. Its explicit cohomology comparison is the Ext comparison, while pushforward composition gives the comparison of derived sections in D(k), including its K-injective representative normalization. The coefficient action is the structure-morphism action. The small-site universe assumptions are inherited from the item. The supporting text read was sites-cohomology.tex 08JA, 08J9 and 0D6E as used in the displayed equalities of 0D0T; no scheme-only global-Hom comparison was substituted.

In step 6 the affine etale derived-module realization node is a genuine derived equivalence with quasi-inverse RΓ, cohomology compatibility and the sections identity, all stated explicitly. I read spaces-perfect.tex 071Q and perfect.tex lemma-affine-compare-bounded behind it. Applied to the coherent output P this yields the finite chart module in each degree. Finally the sections-model statement explicitly gives naturality in K-injective target maps, so multiplication by any scalar is taken to postcomposition by that scalar. Together with the D(k) composition comparison this proves k-linearity of the Ext identification; an additive group isomorphism alone would not suffice.

I checked small cases: M=0, N=0, and empty Z yield zero Ext and empty proper supports; X=Spec(k) gives ordinary finite vector-space Hom and zero positive Ext; a disjoint union of arbitrarily many finite-type components with N supported on one proper closed component is allowed, confirming that the proof uses no quasi-compactness of X. A finitely presented module over a singular affine chart can have arbitrarily high Ext, which is compatible with this proof's lower-bound-only input. I checked no circular dependency through the item is introduced and no new node is elementary or a renamed clause of the item. Every cited use has a verbatim quote in citations.json. No step exceeds 2000 characters. I checked delivery-errors B--E against the actual statements and sources, correcting the slice and source-tag issues described above.

The Mathlib searches were all run by msearch.py and their actual query strings and results are retained in searches.jsonl and the JSON records. Two semantic phrasings were tried for each new question. The ordinary-module candidate ModuleCat.finite_ext was read at Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean:27--34; it does not apply to module sheaves. The derived-image searches found abstract truncation/representative results, scheme local Noetherianity, sheafification for coherent topologies, and ordinary affine quasi-coherent pushforward. None asserts algebraic-space coherent direct-image finiteness with proper supports. All services answered in this run; no unavailable answer was classified as absence.

## Unfinished work

The new input is intentionally statement-only and awaits its own stage-1 split. Nothing is left incomplete in the item's assembly proof. No Lean files were written, no compiler or Lake/build command was run, and all writes are in the assigned sandbox.
