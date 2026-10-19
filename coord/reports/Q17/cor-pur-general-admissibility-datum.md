# Worker report: cor-pur-general-admissibility-datum

## Files written

- `dag/nodes/sec-six-functors/cor-pur-general-admissibility-datum.json`: existing statement split into five steps using existing nodes; no Mathlib match.
- `citations.json`: eight verbatim statement quotations, one for every step/node use.
- `report.md`: this report. Real search logs and preparation scripts stay in the sandbox and are not delivery node files.

New nodes: 0. Mathlib leaves: 0. This corollary is not its unit's key statement, so no unit realization record changed. No second reading is claimed by this first worker.

## Attachments

None. Exact-id and concept searches of slopmaster2 `WeilConjectures/` found no exact declaration. I opened `WeilConjectures/SixFunctors/Etale/Derived/Stability/UpperShriek.lean:230–250` and `:318–365`. The related `AlgebraicGeometry.Etale.exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le` has a combined `constructibleTorAmplitudeIn` input predicate, an existential D, and works on the small etale site. It does not state the item's constructibility-only clause for arbitrary bounded constructible input, its chosen-chart constant, or its pro-etale comparison. The later `exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek` at line 328 further widens the interval symmetrically. Neither is an exact attachment. I did not certify their dependency closure or use master sorry declarations as completed proofs.

## WANTED

None. The shared checkout omits materialized blueprint literature, but existing read-only sources are at `/home/ubuntu/weil-launcher-nt/literature/`. I read the complete master source files for this item, `thm-pur-general-admissibility`, and `thm-pur-open-complement-unconditional`, under `blueprint/sec-six-functors/sk-prop-sf-rf-shriek-preservation/`; `lem-exc-open-complement-known.md` under `sec-smooth-purity/sk-prop-a1-kummer/`; and `cor-sf-ambient-adjoint-discharge.md` under `sec-smooth-purity/sk-prop-sf-existence/`. Canonical node paths remain unchanged. All substantive inputs already have DAG nodes; no new Stacks-source node is needed.

## Source error and corrections

STATEMENT-DISPUTED: the imported scope sentence calls the ambient exceptional right adjoint datum a theorem. Its cited `cor-sf-ambient-adjoint-discharge` explicitly asserts only the adjunction relative to the bounded constructible class, and denies the unrestricted datum. Its source and the current admissibility definition give the example of the structure morphism of an elliptic curve over an algebraic closure of a finite field, with coefficients F_r of different characteristic: the unrestricted all-pro-etale-sheaf cohomological-dimension condition fails. The direct inference also has a quantifier mismatch: a Hom bijection restricted to bounded-below etale-origin inputs cannot be used as one for all ambient derived inputs. I repaired the item to name the constructible exceptional inverse image and the analogues of preservation clauses (2)–(3), without asserting unrestricted clause (1). This is the unit's explicit intended scope. Neither preservation conclusion is weakened and no admissibility assumption is added.

STATEMENT-DISPUTED: X empty is allowed, but its permitted affine cover can have no charts, so both imported maxima are undefined. If Y is empty, its Krull dimension is minus infinity by the current dimension definition. I added D=c=0 for X empty, forming no chart constants, and prove both claims directly in the zero category in step 2. For nonempty X there are nonempty charts and Y is nonempty, so the original finite maxima and dimension expressions are unchanged. This completes the original universal statement rather than excluding a case.

I made explicit the fixed finite-type k-scheme setting, coefficient stage n>=1, integer pair a<=b, and the bounded constructible input in the Tor clause, as required by the unit and cited definitions. I replaced the old scheme-property collection by its actual finite-type and separated-morphism definitions, and added the precise interval, Tor, affine-space, dimension and exceptional-inverse-image definition dependencies. No target or other item was edited.

## What could not be finished

Nothing remains for the one-level split. The sandbox is for the fresh second reader; this worker does not push. No Lean, compiler, Lake, live source or launcher change was made, and no agent was started.

## Not duplicates

No new nodes, hence no new-node/tag pairs. Whole-blueprint searches by the exact id, `preservation`, and `open-complement`, and whole-DAG exact-id/concept searches found the existing conditional preservation theorem and both open-complement statements. The stronger `thm-pur-open-complement-unconditional` belongs to this same unit and its statement explicitly includes the chartwise bound and dimension comparison. Citing it avoids inventing chart-dimension or quasi-compact-complement nodes. It proves a hypothesis of this item, not its preservation conclusion. No equivalent complete blueprint statement was found, so `blueprint.same_as=[]`; the imported `blueprint.from` stays null.

## Review by Q17

I read the worker brief, stage-1 document, human's three blueprint levels, GOAL and DAG-sync instructions, delivery-errors B–E, the item's chapter/unit records and the sources above. The unit's fourth step composes the smooth and closed-immersion bounds after discharging the chartwise open-complement hypothesis. This split follows that route through existing nodes. The initial one-step draft left dimension and quasi-compactness implicit and missed the scope and empty-maxima problems; I corrected those before this review. The chartwise bound is now taken directly from an existing statement, and the enlargement argument is written out.

Step 1 uses only the current statement of `cor-sf-ambient-adjoint-discharge`. It supplies the bounded-class adjunction and explicitly denies the unrestricted ambient claim. No preservation fact is taken from its internal proof. This generic cross-unit scope input is requested in `split_report.tool_uses`; no maintainer-owned top-level tool field is set.

Step 2 is elementary from the actual covering criterion in `def-weil-pbc-proetale-site` and the interval and Tor definitions. Every scheme over the empty scheme is empty, and the empty covering has no matching data. The sheaf axiom therefore forces a unique section, zero. Every complex on the empty source is zero; zero cohomology sheaves are constructible using an empty stratification (or one empty stratum), and every derived tensor is zero. Thus both displayed interval conditions hold with D=c=0, also for empty Y. This is a few-line sheaf-axiom computation, not a new lemma.

Step 3 uses `thm-pur-general-admissibility` for the specified chart objects and the actual chartwise clause of `thm-pur-open-complement-unconditional` for its bound at A=A_{E,n} and comparison d_U+dim V <= d_U+dim Y. I opened both full current statements. The latter explicitly supplies these facts; a definition is not being cited for a dimension theorem. The present field is separably closed and coefficients are finite commutative with an annihilating power of ell, invertible on all the schemes. The source imprecisely calls varpi_E^n a power of the rational prime ell: the step correctly writes ell=u*varpi_E^e and chooses eN>=n to obtain the integer annihilator ell^N. No equality of those two powers is assumed. The existing chartwise statement includes the application to exactly these complements, so its underlying finite-type and quasi-compact-open facts are not silently deduced from a definition here.

Step 4 uses both actual clauses of `def-exc-open-complement-bound`, which I opened. For q>c_U>=b_U its vanishing clause at b_U applies; its constructibility clause is independent of the cutoff. These are precisely the same two clauses at c_U. This is elementary monotonicity, so it stays a proof step and does not become a new node. Both cutoffs are nonnegative integers in the nonempty case.

Step 5 uses the two conclusion clauses of `thm-pur-general-admissibility`. The first is cohomological-interval preservation for arbitrary bounded constructible input, with no Tor assumption; the second is the Tor bound for an input in D^b_ctf. These different input categories are preserved. Every chart condition has been proved with exactly the c_U appearing in its maximum, and both endpoints are identical. Arithmetic check: c_U+1+2(D-d_U)=2D+2dim Y+1, so the upper endpoint is b+2dim Y+1, agreeing with the unit. The lower endpoint is a-2D. I checked different chart dimensions, d_U=0, the identity of a zero-dimensional scheme, zero input, and empty chart complements. An empty complement has zero direct images and satisfies the same bound. No regularity, flatness, or smoothness of the original f is assumed.

For B there are no new node files or hollow definitions; import/audit fields are preserved and all notions in the expanded statement have existing definition nodes. For C1/C4 every proof dependency was opened and only its statement is used; all eight step/node uses have relevant verbatim quotations and `proof_deps` is their union. For D no clause is moved into a new node: the existing input theorem and conditional assembly theorem are reused. For E the exact coefficient, scheme, adjoint-scope, numerical and empty-case checks are those above. Source corrections are explicit.

Every Mathlib query recorded in the item was run through `msearch.py`; tool, exact query and grep subdirectory are copied from `searches.jsonl`. Both original Loogle patterns failed on unknown identifiers, so I retained that as invalid-pattern evidence and ran the successful `CategoryTheory.Adjunction, CategoryTheory.Functor` query. Its signatures define generic adjunctions and constructors, not geometric preservation. Both semantic phrasings returned general adjunction/exactness results or constructible-subset and morphism results. The broader grep found only Chevalley's theorem at `Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:117–124`; I opened its source and checked its objects are subsets. LeanSearch returned Internal Server Error and is recorded unavailable, not no match. No leaf or unrun search is claimed.

The standalone `review_split.py` in the shared checkout fails when resolving its symlinked DAG path relative to the shared root. I did not modify that script. The prescribed `deliver.py --no-push` validates the delivery in its own temporary worktree with maintainer preflight. All final preparation files are in this sandbox; an initial temporary preparation script was moved here. No project or launcher file was edited.

## Validation

The local check passed for JSON parsing, existing unmerged dependencies, exact statement-substring quotes for every step use, complete text-citation lists, and equality of proof_deps with the union of uses. The prescribed initial dry run printed `OK (not pushed)` at d5d7234559 with preflight passed. After completing this report and correcting the empty-cover sentence, the same `deliver.py Q17 cor-pur-general-admissibility-datum --no-push` command is repeated on these final files. Its stdout is the final acceptance record; no push is authorized for this worker.


## Second reading by Q17

I independently opened the item's blueprint source (order 2079), the unit's
_section.md clause (iv), the conditional theorem (order 2078), the unconditional
open-complement theorem (order 2080), the ambient-discharge corollary (order
1808), the open-complement definition (order 1914), and the older known-bound
lemma (order 1923). I read every current DAG statement cited in the five steps,
as well as all eleven statement dependencies. No new source by Stacks tag is
introduced: the proof inputs are existing blueprint nodes, whose statements,
rather than their internal arguments, are used here.

- Item statement: PASS against order 2079 and unit clause (iv): separated finite-type f between finite-type k-schemes, k the algebraic closure of a finite field, n >= 1, arbitrary bounded constructible input in clause 1, finite-Tor bounded constructible input in clause 2, and both original endpoints match. The two marked disputes faithfully repair the restricted-adjunction scope and undefined empty maxima; no target changes.
- Step 1: PASS against the complete current statement and source of cor-sf-ambient-adjoint-discharge: it asserts the class-relative adjunction and expressly denies the unrestricted datum. No all-object adjunction or preservation conclusion is extracted from it.
- Step 2: PASS against def-weil-pbc-proetale-site's covering criterion and the interval/Tor definitions: the empty family covers each object over the empty scheme, so every module sheaf has one section and is zero; all complexes, cohomology and derived tensors there are zero. The empty constructible stratification satisfies the finite-torsion definition. Thus D=c=0 works for empty X, including empty Y, without taking dim(empty).
- Step 3: PASS after removing a redundant coefficient calculation, against both entire theorem statements: thm-pur-general-admissibility supplies the finite chart family and complements, and thm-pur-open-complement-unconditional explicitly supplies the A_{E,n} specialization, bound 2(d_U+dim V), and comparison dim V <= dim Y for these charts. Nonempty U implies nonempty V and nonempty Y. Its chart-specific conclusion supplies the needed finite-type/quasi-compact setting directly.
- Step 4: PASS against both clauses of def-exc-open-complement-bound (and source order 1914): q>c_U>=b_U implies q>b_U, while constructibility in every degree is independent of the cutoff. This two-line implication is elementary; no new monotonicity node is justified.
- Step 5: PASS against the entire statement of thm-pur-general-admissibility: the separated finite-type and chartwise hypotheses are in force, its two input classes match, and its D and c are exactly those used here. Each expression c_U+1+2(D-d_U) equals 2D+2dim Y+1, so the output upper endpoint is b+2dim Y+1, as in unit clause (iv).
- New nodes: none; PASS B1-B7 and C5/D1-D2 without creating elementary, duplicate, Mathlib, or clause-restatement nodes. All eight citation records are verbatim substrings of the corresponding current node statements, and proof_deps is exactly the union of step uses.

I tested the conclusions on zero input; X empty with Y nonempty or empty;
f the identity of Spec k with d_U=0; n=1 and n>1; an empty chart
complement; and charts of unequal embedding dimensions. For Spec k the bound
[-2D, -2D+c]=[0,1] when D=0 contains the unchanged input degrees; the
bound is deliberately coarse. Omitting empty charts preserves the cover, and
nonempty X leaves a nonempty finite index set for each maximum. The endpoint
arithmetic also shows that all constants remain independent of n with charts
fixed. No smoothness, regularity, or flatness of f is assumed in the assembly.

I independently inspected slopmaster2 UpperShriek.lean:246-255 and 328-338:
the former quantifies an existential D and requires constructibleTorAmplitudeIn,
and the latter gives a symmetric enlargement. I also inspected the complete
statement of boundedConstructible_rightDerivedUpperShriek in
UpperShriekConstructible.lean:164 onwards: it preserves bounded
constructibility but states no cohomological interval. None states this item's
combination of chosen-chart constants, constructibility-only interval, Tor
interval, and pro-etale functor, so no exact finished attachment was found or
claimed. Master sorry declarations were not treated as proofs.

Changes made: removed the ramification calculation from step 3. It was
unnecessary because the cited theorem states the finite coefficient
specialization directly; removing it avoids introducing an auxiliary local-field
fact into the citation audit. The first worker's discussion of that calculation
above records its earlier draft; the delivered proof now uses the specialization
alone. The statement, other four steps, citation quotations, and original review
are retained. No new nodes or Mathlib leaves were added, so the required fresh
Mathlib searches for new nodes have no instances. All writes stayed in this
sandbox; no Lean or build tool was run.

Second-reader validation: the prescribed dry run printed `OK (not pushed)` at
`eb0fa6074e`, with preflight passed. After correcting the attachment source line
number in this report, the final report is dry-run again before delivery.
