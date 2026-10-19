# Worker report: lem-coef-quillen-fibrant-test

1. Files written: `dag/nodes/sec-six-functors/lem-coef-quillen-fibrant-test.json` (statement, split, no Mathlib match); `citations.json`; this report. There are 0 new nodes and 0 new Mathlib leaves. The existing statement, stmt_deps, source, ancestry and maintainer metadata are unchanged.
2. Attachments: none. Searches by the exact `(blueprint: lem-coef-quillen-fibrant-test)` tag, Quillen/right-Quillen keywords and fibrant/trivial-fibration terminology in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no project declaration stating the criterion.
3. WANTED: Hirschhorn, *Model Categories and Their Localizations*, Proposition 8.5.4, printed pp. 153–155, for this item. The cited Rochester PDF was read online at PDF pp. 166–168 (zero-based pages), but is not archived in literature/. The proof is marked agent-written: it explicitly writes the dual lifting construction and substitutes two-out-of-three and a concrete arrow retract for the source's homotopy-category argument. No Stacks tag states this generic model-category recognition result.
4. The original statement is correct. Its proof was empty; there were no imported proof steps to repair. The shared copy was briefly absent during the repository refresh, then appeared; work proceeded on the supplied node once it became available. No substitute statement was inferred. No unit or chapter route was changed.
5. Unfinished: none of the mathematical split. No Lean work, compiler or Lake command was used; no shared project or launcher file was edited. Delivery is reserved for the second reader.

## Sources and reuse

I read the item, the sec-six-functors chapter, its assigned sk-prop-sf-biduality-general unit, the current main-20261015 ancestor proof `prop-coef-integral-exceptional-adjoint.proof.md` paragraph 2, and the parent `lem-coef-bousfield-quillen-descent`. The historical unit/ancestry binding is inherited rather than changed. The recognition criterion is an ordinary model-category foundation used by that parent; no geometric, coefficient, purity or trace route is substituted.

I read Hirschhorn Proposition 8.5.4, including its statement and proof. Condition (3) is precisely the item's two hypotheses: preservation of every trivial fibration, without an endpoint condition, and preservation of fibrations whose two endpoints are fibrant. The source proves (2)⇒(1) and explicitly dualizes to (3)⇒(1). The proof here spells out that dual, with the final weak-equivalence calculation replaced by a direct retract argument.

I searched the whole DAG for Proposition 8.5.4 and its right Quillen recognition wording and the whole imported blueprint with `blueprint_refs.py search` for `quillen fibrant`, `right Quillen` and `trivial fibrations`; there was no blueprint duplicate. The parent applies the item and cannot be used to prove it. No new node is necessary: each auxiliary operation is a single factorization, lifting problem, adjunction bijection, two-out-of-three application or displayed retract, directly from the definition paragraph of `lem-coef-model-infinity-derived-adjunction`.

Fresh Mathlib searches were run only through msearch.py: LeanFinder in both right-adjoint and left-adjoint phrasings, LeanSearch, Loogle, and grep in ModelCategory and CategoryTheory/Functor. All ran successfully. I read the returned JoyalTrick.lean:44–99, IsCofibrant.lean:96–101 and Derived/Adjunction.lean:23–42. Joyal's lemmas do not state this adjunction recognition test, the fibrancy predicate lemma is only a one-category fact, and the derived-adjunction hit is a reference to Quillen. Thus the item is not a Mathlib leaf. Existing search entries were preserved; the six fresh logged queries and their actual result records were appended.

## Review by Q82

I checked delivery-errors B–E against the source and all eight steps. There are no new nodes, so no statement-only-node, duplicate-node or restated-clause issue arises. I kept the item's statement intact: in particular no cofibrancy of A or B, no properness, no enrichment and no combinatoriality were inserted.

For each step I opened the full statement of `lem-coef-model-infinity-derived-adjunction`, the sole cited node. Its first paragraph explicitly supplies completeness, cocompleteness, the two weak factorization systems, two-out-of-three, retract closure of W, and the fibrant-object definition. Those axioms, rather than that node's derived-adjunction theorem, are what every step uses. Citations.json quotes that paragraph verbatim for each step.

Step 1 uses the characterization C = LLP(F∩W). The right adjoint's assumed preservation of all trivial fibrations transposes the filler, so it proves L preserves every cofibration without presuming a Quillen pair. Step 2 uses the (C∩W,F) factorization twice: k makes Y fibrant, and p makes X fibrant because right lifting classes are closed under composition (the two successive lifts are described). Only this p is subjected to the restricted preservation test, so both endpoints are verified fibrant. Step 3 applies the other category's trivial-cofibration/fibration lifting axiom to i and R(p), then transposes back to h; both equations have the correct domains. Step 4 applies that same axiom in B to k and p, producing the strict section r with pr = identity and rk = h.

Step 5 checks (rp)j = r(kf) = (rk)f = hf = j. Since j and (rp)j are weak equivalences, two-out-of-three gives rp ∈ W directly. Step 6 checks the arrow retract explicitly: the maps from p to rp and back have pairs (identity,r) and (identity,p); the second square uses pr = identity and the composite is the identity on p. Retract closure therefore gives p ∈ W. Step 7 then applies two-out-of-three to pj = kf, using j,k ∈ W, so Li ∈ W; Step 1 supplies its cofibration property. Step 8 transposes arbitrary lifting squares against trivial cofibrations and gives preservation of every fibration, with no fibrancy condition. These are elementary steps from the cited axioms; no saturation, localization, homotopy invariance, Brown lemma or uncited existence theorem is hidden in them.

Small cases checked: the identity adjunction, the terminal category, a model structure with W equal to the isomorphisms, and an arbitrary trivial cofibration whose endpoints are not cofibrant. The construction never requires those endpoints to be cofibrant. The empty-source case also uses only the initial object and the same factorizations. All displayed equations and retract maps remain well typed in these cases. There was no source error or statement dispute to repair. The direct two-out-of-three/retract calculation removes any need to cite the source's homotopy-category detection theorem, and consequently introduces no potentially circular dependency.

## Not duplicates

No new nodes were created.

## Second reading by Q82

I reread the complete item against Hirschhorn, *Model Categories and Their Localizations*, Proposition 8.5.4(3)⇒(1), printed pp. 153–155, and opened the full statement of `lem-coef-model-infinity-derived-adjunction`. The two preservation hypotheses match the source criterion: all trivial fibrations, with no endpoint condition, and fibrations whose source and target are fibrant. The conclusion retains both Quillen clauses and adds no cofibrancy, properness, enrichment or combinatoriality hypothesis. The live DAG synchronization already has the same statement-only seed; this sandbox proof is the delivery's substantive split.

- Step 1: checked the adjunction transpose against the cited model-category definition and the characterization (C=\operatorname{LLP}(F\cap W)); PASS. The displayed lifting square has the correct orientations.
- Step 2: checked both `(C∩W,F)` factorizations, fibrancy of (Y), and fibrancy of (X) from closure of right lifting classes under composition; PASS. The restricted hypothesis is applied only after both endpoints are shown fibrant.
- Step 3: checked the transposed square against the full lifting characterization and the equations (hf=j), (ph=k); PASS. The adjunction bijection supplies exactly the required filler.
- Step 4: checked the square ((k,h;1_Y,p)), the section (r), and equations (rk=h), (pr=1_Y); PASS.
- Step 5: checked ((rp)j=j) and the two-out-of-three use; PASS. No homotopy-category saturation is hidden in this step.
- Step 6: checked the arrow-category retract maps ((1_X,r)) and ((1_X,p)), their commutative squares, and composite identity; PASS. Retract closure therefore gives (p\in W).
- Step 7: checked composition (pj=kf), two-out-of-three with (k\in W), and Step 1's cofibration conclusion; PASS. This proves preservation of trivial cofibrations.
- Step 8: checked arbitrary (q\in F_{\mathcal B}) against the transposed lifting square with an arbitrary trivial cofibration in (mathcal A); PASS. It establishes preservation of all fibrations and hence the stated Quillen adjunction.

The sole dependency node was checked for every cited definition and closure property; its statement supplies complete/cocomplete model categories, both weak factorization systems, two-out-of-three, retract closure, and fibrant objects. No proof step uses material from its proof. No new nodes require B1–B7 review, and a whole-DAG search found no duplicate criterion node. The recorded Mathlib searches were rerun and read: hits in `JoyalTrick`, fibrant-object predicates, and derived ordinary adjunctions do not state this recognition criterion, so no Mathlib leaf is appropriate.

Small cases checked were the identity adjunction, the terminal model category, (W) equal to isomorphisms, an arbitrary trivial cofibration with non-cofibrant endpoints, and the empty-source case. All factorizations and retract equations remain well typed, and no endpoint cofibrancy is used.

Changes made: added this independent second-reading record only; no statement, proof step, citation quote, dependency, or search result required mathematical repair. The proof remains eight explicit lifting/factorization steps, with the direct two-out-of-three and arrow-retract calculation replacing any omitted homotopy-category argument. No SGA source, Lean file, compiler, Lake command, shared repository file, or launcher file was touched.
