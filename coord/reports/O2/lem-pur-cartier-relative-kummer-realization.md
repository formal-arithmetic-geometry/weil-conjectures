# Worker report

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-cartier-relative-kummer-realization.json: item split into seven steps; statement unchanged; no Mathlib match.
- citations.json: every step/node citation, with a verbatim statement quote.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, repository files, launcher files, chapter records or unit records were written. The item is not the unit key node.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint id, supported Kummer, Cartier and roots-projection concepts. The hits in Smooth/KummerClass.lean and TateTwist/Normalized.lean concern affine-coordinate purity, not this arbitrary-Cartier, two-site morphism identity; Normalized.lean also has a sorry. No declaration states every clause of this item.

## WANTED

None.

## Findings and corrections

The item had no proof. Its statement is retained, including the arbitrary coefficient index, arbitrary k-scheme S in the first paragraph, canonical source comparison, actual derived-morphism equality, and negative local sign. Added def-kun-derived-tensor to statement dependencies for the displayed derived tensor. Preserved inherited searches and all other existing fields.

The raw main-20261015 lemma-pur-divisor-class blueprint text says +boundary and calls the two-element tuple a frame for a sum of divisors. The live DAG has already corrected these issues: the Yoneda-normalized divisor class is minus the rank-one frame boundary, and the sum equation is a product. This delivery follows those live statements and the item's explicit normalization. No new statement dispute or unit-route replacement is required.

Source citation correction: lem-pc-bounded-above-flat-kflat-site currently names Tag 06YS for the bounded-above-flat criterion. Reading sites-cohomology.tex and tags/tags shows its statement is lemma-bounded-flat-K-flat, Tag 06YQ; 06YS is lemma-K-flat-resolution. The mathematical statement used here is correct. Our proof source cites 06YQ; the dependency file was not changed, as it is outside scope.

## Existing-node and Mathlib searches

Searched the whole DAG for supported Kummer, finite root, projection-induced comparisons, flat complexes, the source tags, and the named interfaces. Read the statements rather than relying on titles or proofs. Ran blueprint_refs.py ancestor and searches for Kummer, Cartier Kummer, relative.*Kummer, finite.*Tate.*comparison and root. The ancestor is thm-pur-rank-one-thom through lem-pur-line-zero-class-etale-realization. No imported blueprint node states the whole item in another form; same_as stays empty.

The necessary smaller statements already exist: finite-etale-twist-line, bounded-above-flat-kflat-site, derived-change-of-rings, finite-root-site-comparison, tate-root-projection-reduction, ordinary-supported-kummer, supported-root-scalar-site-comparison, cartier-boundary-existence, cartier-kummer-descent, supported-constant-exchange-normalization, cartier-class-agreement and divisor-class. Therefore no new node is justified. In particular this delivery does not create nodes for tensoring with R, cancelling an inverse comparison, or the coefficient-annihilation calculation.

Used only the prescribed msearch.py for Mathlib searches. searches.jsonl records two LeanFinder phrasings, Loogle, grep and LeanSearch. Read all returned signatures: the LeanFinder hits are standard etale algebra presentations/loci, and the LeanSearch hits are field-theoretic Kummer extensions. Neither is a sheaf relative-boundary comparison; Loogle and the algebraic-geometry grep have no hits. Recorded the actual results and kept the parent's historical searches without relabelling their unavailable LeanSearch as a no-match. No unrun search was added.

## Not duplicates

No new nodes; hence no new/existing tag pairs. The existing lem-pur-cartier-class-agreement proves the global supported-class clause and is cited for that clause. It does not replace the proof of the arbitrary-S root-flatness assertion or the explicitly normalized two-site equation. The item is not relabelled into a new lemma.

## Review by O2

I read the chapter and unit records, the current main-20261015 sk-prop-an/_section.md, thm-pur-rank-one-thom.proof.md Step 1, the complete relative Cartier Kummer construction in sec-six-functors-basics/sk-lem-geo-cartier/lem-amb-cartier-kummer-map.proof.md, and lemma-pur-divisor-class.md and its proof in sk-prop-an. I also read Stacks etale-cohomology.tex lemma-kummer-sequence (03PL) and lemma-cohomology-with-support-triangle (0A45), and sites-cohomology.tex lemma-bounded-flat-K-flat (06YQ) and definition-derived-tor (06YU) with its preceding construction. The blueprint alone does not prove every normalized comparison, so proof_origin is honestly agent, assembling the existing statement interfaces; no forbidden SGA source is used. There are no new-node sources to check.

Step 1 uses def-pur-frame-class, whose statement explicitly says ell is in the uniformizer ideal and ell^n kills A. The written equation ell^n=varpi^n b^n proves annihilation and the induced R-algebra structure directly. Characteristic distinctness makes N invertible on every k-scheme, without a finite-type restriction on S. This is the only elementary step.

Step 2 uses the flatness conclusion of lem-asd-finite-etale-twist-line with coefficient R itself. Its hypotheses allow any scheme with N invertible and any finite ring killed by N; R satisfies these. The unit tensor identifies its line with the root sheaf. The cited site version of the bounded-flat criterion, not the ringed-space version, gives K-flatness of its single complex. Derived-change-of-rings explicitly computes using any K-flat resolution, so the identity resolution gives the actual degree-zero tensor object. No flatness of A is assumed or deduced. The source tag was repaired as described above.

Step 3 uses the full root-tensor formula of finite-root-site-comparison and the projection formula in tate-root-projection-reduction, not merely the existence of isomorphic lines. Both statements allow arbitrary schemes with N invertible and arbitrary annihilating exponents. Their composite has the orientation from the etale root line to the prescribed pro-etale twist; def-pur-frame-class fixes exactly its inverse root-projection convention. Thus theta is specified, and not chosen up to a unit.

Step 4 reads ordinary-supported-kummer's last sentence for derived scalar extension of the actual supported arrow. The boundary definition explicitly retains the frame torsor, supported section one, and zero trivialization on W. Supported-root-scalar-site-comparison explicitly supplies Ri_*=i_* on these sources, the canonical scalar-extended source, and the degree-zero target. It applies to any closed immersion on separated finite-type T, so our Cartier pair satisfies every hypothesis. No purity theorem is inferred from the support-Hom description.

Step 5 uses the uniqueness assertion of cartier-boundary-existence to identify the two ordinary etale components, which have identical Yoneda boundary normalization. Cartier-kummer-data defines the realization equation; cartier-kummer-descent asserts existence and uniqueness of its normalized realization simultaneously at annihilating exponents. Cartier-kummer-map is the published family having this normalization. The supported-constant-exchange statement characterizes the actual exchange uniquely by its quotient-unit equation, so the source is epsilon_i. Step 3 already fixes the target as theta. Substituting and composing with epsilon proves the displayed actual-morphism equality; neither equality of Chern images nor local equality is used as a substitute.

Step 6 uses the statement of cartier-class-agreement, which expressly identifies the full global class with the published Cartier map under supported Hom. Its explicit relative/scalar/root normalization agrees with the earlier steps. Supported-hom applies because the target line is in degree zero and thus bounded below. Cartier-agreement-maps defines c_D by precisely these comparison composites; it is used only for that definition, not as an existence or compatibility theorem.

Step 7 uses divisor-class's explicit negative local-boundary clause, after checking smoothness over B, pure codimension one, and separated finite type. Frame-class defines the two maps and its positive rank-one frame class; the proof distinguishes this from the negative Yoneda divisor class. The arbitrary etale neighbourhoods are fibre-product neighbourhoods as in that definition; no open-immersion hypothesis is silently substituted.

Small cases checked: n=1; a ramified coefficient field with n=2 and ramification index at least two, where A is killed by ell and is not flat over Z/ell^2; empty S or D; a trivial Cartier equation that is a unit (empty support and zero supported arrow); and D=(t) in A^1. The root-line argument still works in the nonflat ramified case because the first factor is flat. In the empty cases the stated comparisons restrict to the unique maps of zero sheaves. For the local coordinate the sign is minus the positive frame boundary, as required by the live Yoneda convention. For nonempty S no assertion that A is a free R-module appears.

Checked B--E: self-contained unchanged item, all notions and source places recorded, proof_deps equals the union of uses, every used non-elementary statement read and quoted, no new statement-only node accidentally given a proof, no duplicate/clause node created, no inference from the proof of a cited node, no missing smoothness or finiteness hypothesis, and no cycle through the cited existing nodes. All seven steps are below 2000 characters (maximum 998), so no long step hides an extracted comparison lemma. Generic off-unit tools are declared in split_report.tool_uses with their actual purpose; they preserve the rank-one relative Kummer route. The server review_split check passed with zero new nodes before this report. Nothing was sent to a second worker, as required by the direct-delivery brief.

## Unfinished work

None within the one-level stage-1 split. Existing unsplit dependencies remain separate queued items. This is not a claim that Lean proofs were completed.
