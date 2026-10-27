# Worker report: lem-trf-frobenius-contraction-scalar-pasting

## Files written

- dag/nodes/sec-trace-formula/lem-trf-frobenius-contraction-scalar-pasting.json: statement item, now split in three steps; no Mathlib match.
- citations.json: seven entries, one for each step/cited-node pair, with verbatim statement excerpts.
- report.md: this report. The search command also produced searches.jsonl.

No new nodes or Mathlib leaves. No unit record was changed: this is an intermediate assertion, not the unit's key statement.

## Attachments

None. Searches under lean/WeilConjectures/ for the exact blueprint id, Frobenius/coefficient/trivialization combinations, contraction, and the directImageScalarPullback comparison found no project declaration stating this whole contraction equality. The existing coefficient-naturality node is narrower: its equality is for H itself, without the v-compositor and subsequent contraction. Its existing Lean record is in Sheaf, so it is used as a DAG statement, not submitted as an attachment for this item.

## WANTED

None. The proof is agent-written, expanding the available blueprint's naturality assertion; it does not pretend to be a verbatim theorem in Stacks.

## Problems found and changes

The imported item was statement-only and correct. I retained its statement, original statement dependencies, source, provenance, and original search records, and added its actual proof and the searches run for this delivery. There is no STATEMENT-DISPUTED correction and no change to the unit's route. In particular, the argument never replaces the arbitrary endomorphism v by an automorphism or imposes prime-to-p coefficients.

The two substantive inputs already exist: det-prop-scalar-six-pullback clause (1), including its explicit composition law, and lem-trf-absolute-frobenius-coefficient-naturality. Creating another node for their formal pasting would duplicate a few lines of category axioms. The general square/cube lemma was inspected but not used: a Cartesian-square theorem would require an unnecessary square and is less direct than the explicit composition clause.

## Searches and reuse

I searched the whole DAG for Frobenius/contraction, scalar-pullback composition, and coefficient naturality, and read the relevant existing statements. The blueprint ancestor command identifies thm-trf-finite-coefficient-map. The whole-blueprint searches for 'scalar pullback' and 'Frobenius contraction' returned no matches; the broader 'Frobenius' search includes the known site and coefficient comparison nodes but no equivalent imported contraction statement. The item's existing blueprint.from.place and via list are precise and retained; same_as remains empty.

All new searches were made through the required msearch.py command and their actual queries/results are appended to mathlib_searches, preserving earlier records. The two LeanFinder phrasings covered both the geometric assertion and general functor pasting. Loogle's frobenius/pullback hit is CategoryTheory.Regular.frobeniusMorphism_isPullback (Mathlib/CategoryTheory/RegularCategory/Basic.lean:191): I read its statement and preceding definition; it concerns subobjects in a regular category, not absolute Frobenius of schemes. The LeanSearch hit SheafOfModules.pullbackComp (Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167) was read at lines 157–187: it identifies ordinary module pullback composites, but supplies neither the derived coefficient square nor the Frobenius trivialization. The other general pseudofunctor and CatCommSq hits package abstract squares; obtaining the specified geometric comparison remains precisely the two DAG inputs. Thus the item is not a Mathlib leaf. The Mathlib AlgebraicGeometry grep returned zero hits. No search or unavailable-service result was invented.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish.

## Review by Q111

I read the chapter and sk-p-trace-coeff unit records, the current main-20261015 proof of thm-trf-finite-coefficient-map (final coefficient-naturality sentence), and prop-trf-scheme-galois-comparison.proof.md (the displayed construction of kappa by pullback composition and the specified absolute-Frobenius trivialization). I also read lem-trf-absolute-frobenius-site.proof.md, especially its final paragraph constructing the functor trivialization and its iterates from relative-Frobenius maps. These justify the intended route, and the item's proof_origin is agent because the actual pasting calculation is expanded here. No SGA source is used. The underlying relative-Frobenius theorem is already inside the existing site/naturality inputs; I do not introduce an uncited application of its Stacks tag.

For Step 1 I opened the full statements of det-prop-scalar-six-pullback, lem-weil-pbc-proetale-derived-pullback-composition, both finite-discrete ring-constant lemmas, and def-sp-constant-scalar-pullback-comparison. The first explicitly says that the comparison for g composed with f is the composite of their comparisons. Substituting f=H and g=v, then taking the inverse comparison direction used by this item, gives T(d_A) after c_(vH) equal to c_H after P_B(c_v) after d_B. The compositor statement gives exactly L(vH)* to LH* Lv*, not the reversed order. The ring-constant lemmas give monoidal identifications first on profinite sets and then on the scheme site, including zero rings and empty schemes. The definition pins the inverse comparison to the ordinary scalar/pullback map, so transporting the same equality gives the same c, rather than an arbitrarily chosen isomorphism. This step is non-elementary only because it applies those cited comparison results. Their off-unit uses are declared as generic infrastructure in split_report.tool_uses.

For Step 2 I opened lem-trf-absolute-frobenius-coefficient-naturality. Its statement, not its proof, gives T(tau_A) after c_H equal to tau_B for every exponent b and every object. It uses exactly the same finite commutative rings, unital map, ordinary unbounded categories and transported inverse comparison. It therefore applies with object V_A K, without any boundedness, flatness or finite-Tor requirement. This is strictly a previously existing input, not a new node restating the item's v-contraction clause.

Step 3 uses the same node's specified trivialization between functors as a natural isomorphism. I wrote its naturality equality explicitly at the morphism c_v: V_B T K to T V_A K. Expanding e_A and e_B, functoriality and associativity turn Steps 1 and 2 and this equality into the conclusion. This is elementary category algebra; it hides no extra geometric assertion, descent theorem, or comparison identification. Every intermediate map has the source and target required by its neighbours: after d_B the object is P_B V_B T K; after P_B(c_v) it is P_B T V_A K; after c_H it is T P_A V_A K. Neither naturality nor pullback functoriality needs v invertible.

I checked delivery-errors B–E against the files. There are no new statement-only nodes to hide a proof, no invented definitions, no generic-square lemma used without its hypotheses, no cited proof used in lieu of a statement, no step longer than 2000 characters, and no uncited non-elementary fact. citations.json was constructed from the actual existing statements and each excerpt was checked as a verbatim substring before writing. The original statement dependencies are still the notions expressly named in the statement, and proof_deps is exactly the union of step uses. The six cited inputs' dependency lists were inspected to avoid introducing a reverse edge from this item.

I tested b=0 with the canonical identity-pullback unitor (not a literal equality of separately chosen identity functors), b=1, v=id, a noninvertible endomorphism v, empty Y, zero coefficient ring B, and the nonflat map Z/p^2 to F_p. The proof is a well-typed naturality/pasting calculation in each case. It uses no tensor exactness on underived modules and so does not accidentally exclude the nonflat example. Since no nodes were created, there are no separate new-node small-case tests or same-tag pairs. No mathematical statement correction was necessary.

## Unfinished work

None in the stage-1 split. The required server dry run and push are performed after this report is written; their final result is recorded by the delivery tool.
