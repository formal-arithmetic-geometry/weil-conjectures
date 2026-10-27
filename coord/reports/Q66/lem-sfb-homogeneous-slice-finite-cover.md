# Stage-1 report: lem-sfb-homogeneous-slice-finite-cover

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-slice-finite-cover.json: statement node, now split in eight steps; no Mathlib match for the whole statement.
- citations.json: one verbatim statement quotation for each of the 18 step/node citations.
- searches.jsonl: actual Q66 msearch results. The original item's NH search records are retained unchanged; five Q66 searches are appended to the item.
- report.md: this report.

No new nodes and no new Mathlib leaves. No Lean was written or compiled, and no repository, launcher, unit or chapter file was edited. On resumption the sandbox contained only the four brief markers; there were no saved nodes, report, search log or active Q66 delivery processes to resume.

## Attachments

None. The exact blueprint-tag search and the affine-cone, punctured-cone and homogeneous-slice concept searches under lean/WeilConjectures found no declaration proving this statement. The unrelated perfect-complex affine-cone and pro-affine-cone declarations are different notions. No Mathlib declaration is treated as a project attachment.

## WANTED

None: this split uses the local Stacks sources and elementary chart calculations, rather than the GIT book mentioned by the parent. No SGA source is used.

## What changed and what was wrong

The item was statement-only. Its statement and statement dependencies remain unchanged. Its inherited mathematical statement is correct, including empty opens, nonreduced schemes, arbitrary fields and inseparable degrees. There is no statement dispute.

The proof is an explicit agent reconstruction from the chart sources already named by the item. It does not pretend that Stacks 01M4 alone proves the whole cone or cyclic-slice assertion. The genuinely substantive existing inputs are cited separately: scheme-theoretic homogeneous equations, Proj charts and twisting generators, monic quotient basis, finite-free algebra spectrum, affine fibre product, faithfully-flat spectrum-surjectivity and finite-locally-free descent. No elementary Laurent-coordinate identity is promoted to a new node, and no clause of the item is moved into a new statement.

The nearest-ancestor command returned None. The inherited null root and full via chain are retained; its precise textual place already points through the parent projective-stability argument to the alteration/moduli input of det-thm-sf-ctf-stability-direct-images (3). I read the latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. Their direct-image route is unchanged. The older dag/units record belongs to sec-six-functors whereas this inherited node is filed in sec-six-functors-basics; I did not rewrite either record to conceal that inherited mismatch.

## Not duplicates

No new nodes were created. The existing homogeneous-ideal node gives scheme-theoretic Proj realization and the existing quotient-chart-kernel node gives its affine quotient presentation; both are cited. The existing projective-affine-cone-dimension node concerns topological closed cones and dimension, with its own convention for the empty cone, and does not give this scheme-theoretic tautological-line and cyclic-level assertion. The monic-quotient-free and finite-free-algebra-spectrum nodes already give exactly the general algebraic inputs, so no specialized replacement was created. Whole-DAG/blueprint searches for punctured cone, homogeneous ideal and monic quotient were inspected; no blueprint node states the full item in another form. The inherited blueprint.same_as remains [].

## Search results

All additional Mathlib searches used msearch.py with Q66 and this item's id. Loogle with `"Proj", "IsFinite"` returned an unrelated finite-measure declaration. The AlgebraicGeometry grep for cone/homogeneous/Proj with finite or finite-locally-free returned no hits. LeanSearch returned homogeneous-polynomial notions and Proj open covers. The first LeanFinder phrasing returned Proj.awayι, its chart constructions, affineness and finite-type facts; the second cyclic-root-cover phrasing returned the same open-cover constructions, universal polynomial factorization finiteness, Weierstrass coordinate bases and an analytic polynomial covering map. None proves this item; these are not one-line specializations of the punctured-line-bundle plus finite cyclic-slice theorem. Both semantic phrasings and the actual outputs were read. The item keeps all inherited search records as well.

## Review by Q66

I checked the proof against delivery-errors B through E with the cited statements open. There are no new unsplit statements, hollow objects or unsearched proposed nodes. Each proof step is under 2000 characters and every uses entry has a verbatim quotation in citations.json. I checked that the cited dependencies do not reach this item, avoiding a cycle. The item retains the exact hypotheses of the inherited statement, and proof_deps is the union of uses.

For step 1 I read constructions.tex, Tag 03GL (lemma-closed-in-projective-space), its kernel definition and chart proof, as well as Tags 01M4 and 01NG. I read the full statements of lem-sfb-projective-closed-subscheme-homogeneous-ideal, def-pc-proj, lem-weil-pbc-projective-space-standard-charts and lem-sfb-homogeneous-quotient-chart-kernel. The first applies over an arbitrary ring and includes nonreduced and empty subschemes; it therefore applies to k and this closed immersion without integrality. The chart-kernel node gives exactly the ideal generated by the homogeneous fractions, rather than merely a set-theoretic zero locus. The standard-charts node supplies both the covering and the pulled coordinate frames. Selecting a basis identifies the symmetric algebra with the displayed degree-one polynomial algebra.

For step 2 I used only the quotient presentation from that kernel node and the fraction relation in def-weil-ring-localization-away. The inverse Laurent maps are written on generators. Homogeneous relations vanish as t^degree times their dehomogenizations; both composites fix generators. No regular-element cancellation or reducedness is invoked. This is an elementary presentation calculation, rather than a hidden general torsor theorem.

For step 3 I checked the sign of the dual frames against the chart node and the O(1) transition convention: e_j=(x_j/x_i)e_i implies epsilon_i=(x_j/x_i)epsilon_j, hence t_j=(x_j/x_i)t_i, as required for the tautological line rather than its dual. I read the statement of lem-weil-pbc-scheme-morphism-gluing, which gives both existence and uniqueness on the open cover. Applying it to the inverse chart maps also proves the global inverse. The relevant local source is constructions 01MS with 01NG; gluing is the scheme gluing of schemes.tex, Tag 01JA, rather than an assumption of a global trivialization.

Step 4 uses the uniqueness clause of the same gluing statement. The linear-form formula t_ell=ell(v) and normalized vector v/ell(v) checks overlaps between arbitrary bases. I made preservation of the homogeneous ideal explicit by pullback of vanishing sections. This ensures the naturality assertion is about the closed scheme, including nilpotents. Preservation of f restricts the commuting diagram to f=c; no invariance under arbitrary unrelated automorphisms is claimed.

For step 5 I checked constructions 01MV (lemma-principal-open) and the localization definition. The constant c is a unit and d>0, so no point of T is the vertex. The local expression f=a_i t_i^d shows that the image lies on the nonvanishing open. In the two quotient presentations the respective inverses a_i^{-1}=t_i^d/c and t_i^{-1}=(a_i/c)t_i^(d-1) give inverse maps. This writes out the localization identification instead of saying only 'clear denominators'. It uses no new theorem about the entire slice.

For step 6 I read the statements of lem-weil-pbc-monic-quotient-free, lem-weil-pbc-finite-free-algebra-spectrum, lem-weil-pbc-fibre-product-affine-spectra and def-pc-finite-locally-free. The first really gives the full monomial basis for any monic polynomial; the second gives finite, flat and locally of finite presentation over any base ring; the third states the affine fibre ring, not merely its underlying topological set. I read morphisms.tex 02KB (lemma-finite-flat). The fibre basis computation is written explicitly, so rank d is proved rather than inferred from a finite map. Empty zero-ring charts are discarded before asserting that the monic polynomial has degree d, avoiding the zero-ring degree edge case. No Noetherian hypothesis is needed by these cited inputs.

For step 7 I read def-weil-pbc-faithfully-flat-ring-map and lem-weil-pbc-faithfully-flat-surjective-spectrum, and algebra.tex Tags 00HB and 00HQ (lemma-ff-rings). The former definition uses preservation and reflection of exactness. The coefficientwise direct-sum calculation proves that condition because d>0; the latter theorem therefore supplies scheme-surjectivity under precisely its stated hypothesis. This avoids assuming roots exist over k or that k-rational points detect all fibres.

For step 8 I read lem-weil-pbc-open-immersion-etale and lem-weil-pbc-finite-locally-free-degree-etale-descent together with descent.tex 02VO, including its degree clause. The W_i are open subschemes covering precisely Y_f, so the required etale covering exists; their base changes are exactly the affine maps in step 5. This is a genuine descent citation, not the definition of local freeness used as a theorem. Empty targets are handled by the empty cover and the explicit emptiness of T, and no step needs d invertible.

The five off-unit statement tools are declared in split_report.tool_uses: projective standard charts, finite-free algebra spectrum, affine fibre spectra, faithfully-flat spectrum-surjectivity, and degree descent. They supply generic geometry/algebra to this fixed below-unit argument; they do not replace the unit route. Other cited tools are definitions, Mathlib leaves or same-unit nodes. No top-level maintainer-owned tool_uses field was set.

I tested the following small cases in the written calculations. For dim V=1 and Y=P^0, the punctured cone is G_m and the slice is k[t]/(a t^d-c), of rank d when a is nonzero. For d=1, each local slice algebra is the base ring, as expected. If f vanishes on all of Y, then every a_i-localization is the zero ring and T is empty because f-c is a unit modulo I. For Y empty its vanishing ideal is all of P, so both cone and slice are empty. For the doubled point Y in P^1 given by x_1^2=0 on the x_0 chart, its cone chart is (k[u]/u^2)[t,t^{-1}], preserving its nilpotent. In characteristic p with f=x_0^p and c=1, the slice is k[u,t]/(u^2,(t-1)^p), which remains free of rank p despite inseparability and nilpotents. Over R, the slice x^2=-1 over P^0 is a surjective scheme morphism even though it has no R-valued point. These tests validate the exact edge cases explicitly required by the statement.

## Unfinished work

None mathematically. Server dry run and delivery results are recorded below when completed.
