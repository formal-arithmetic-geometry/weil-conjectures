# Q34: lem-pur-adic-unit-trace-transpose-reductions

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-adic-unit-trace-transpose-reductions.json`: statement node, now split into eight proof steps. The item is not a Mathlib leaf. No new nodes and no Mathlib leaves were created.
- `citations.json`: a verbatim statement excerpt for each of the 30 step/node citations.
- `searches.jsonl`: actual searches recorded by the required msearch command. `write_split.py` is a sandbox-only preparation script, not a delivered DAG file.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact blueprint identifier and by unit-trace, trace-transpose, purity and reduction terminology. The Adic module's `exists_iso_realization_twistShiftPullbackLevel` only reconstructs an isomorphism between given towers with given compatible finite maps. Its docstring explicitly disclaims the geometric operation identifications; it neither constructs this unit-trace family nor proves all its clauses. There is no exact attachment.

## WANTED

None. I read the current blueprint's transport unit, its proof and the coefficient-change proof under `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/`. This is an agent-written assembly of existing DAG statements, marked `proof_origin.by = agent`. I use no SGA source. The geometric orientation remains the diagonal/DNC orientation of the lecture-notes route.

## Corrections and scope

The imported JSON escaped the prime inequality as an actual newline in `\ell\ne p`. I repaired that TeX escape without changing its meaning. There is no mathematical statement dispute. The item originally had no proof. I retained its statement, existing historical searches, creation metadata and blueprint ancestry, and filled its proof and split report. Its source now points at the current blueprint route rather than the historical master snapshot. No claim of uniqueness of integral lifts has been added.

The whole-DAG/blueprint search found existing support for every substantive inference. In particular `lem-pur-tensor-trace-transpose` states the finite tensor/transposition identity in the needed tensor order; `prop-coef-integral-exceptional-adjoint` explicitly includes reduction of the counit; and `lem-pur-compact-support-integral-coefficient-comparison` explicitly includes its cofinal reductions. I did not introduce new restatements of those facts or move the item's clauses into child nodes. The source's abstract transposition argument is expanded as equalities of actual finite-coefficient morphisms, rather than inferred from an unsupported uniqueness claim.

## Mathlib searches

I ran leanfinder twice with different geometric/derived-complete phrasings, loogle for `CategoryTheory.Adjunction.homEquiv`, grep for `TateTwist|smoothTrace|exceptionalPullback|upperShriek`, and leansearch for the normalized trace/projection/exceptional-adjunction construction. The log and JSON contain the actual queries and returned records. Semantic results concern algebraic field traces or smooth commutative algebras. I read the abstract Hom equivalence in Mathlib/CategoryTheory/Adjunction/Basic.lean, lines 160-169, and its naturality declarations; it proves the elementary formal adjunction manipulations but does not give the specified geometric integral maps. I also read the returned normalized-trace source (Mathlib/FieldTheory/NormalizedTrace.lean); it is the field trace, not the geometric smooth trace. The exact grep returned zero hits. None is a one-line specialization proving this item.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to disambiguate. The searches `blueprint_refs.py search 'unit trace'` and `... 'tensor trace transpose'`, and the DAG statement searches, were used to reuse the finite tensor-trace lemma and all existing coefficient/reconstruction lemmas. Neither affine-space top trace nor linear trace invariance states this integral assembly.

## Review by Q34

I checked delivery-errors B through E against the node statements and the current source route. The chapter is smooth purity; the inherited compatibility unit permits the purity-transport coefficient argument. I read the chapter/unit records and the current transport proofs, rather than changing their route. No new node needs a separate source or definition audit. All eight steps are below 2000 characters, and the formal calculations are steps rather than artificial new elementary lemmas.

Step 1 uses the statement of `lem-pur-adic-operation-domains-source-comparison`: it explicitly puts the unit, its twist, and the three operations on the uniform finite-Tor domains, and explicitly provides linear exceptional Hom bijections. `thm-pur-adic-reconstruction` supplies an actual unit isomorphism with the prescribed reductions; I use it only at the prime coefficient field. I verified smoothness, separated finite type, pure nonnegative relative dimension and the completed coefficient categories match. I do not use the insufficient source Lean tower statement as this geometric theorem.

Step 2 uses `lem-coef-integral-compact-support` for the canonical compact-support reduction comparisons, `prop-coef-integral-exceptional-adjoint` for reduction of the actual counit, the reconstructed unit's prescribed reductions, and the displayed definition of smooth trace in `def-pur-smooth-trace`. The proof writes out how naturality of the compact-support comparison moves the reduced unit morphism past it. The necessary finite-Tor input is the twisted unit established in Step 1, not an arbitrary unbounded object.

Step 3 reads the actual statement of `lem-weil-finite-free-completed-scalar-comparison`, which gives the finite-free completed ring extension and identifies its canonical tensor model with strict-tower extension. Ordinary tensor associativity gives the cofinal reduction calculation. The Tate coefficient definition fixes the root/tensor comparison; its $d$-fold reassociation and shift give the unit comparison, without a new normalization choice. `lem-pur-compact-support-integral-coefficient-comparison` says that its own specified map reduces to the same finite-free compact-support map. `lem-pur-finite-universal-smooth-trace` gives exactly the required trace equality for this map. In particular, this is not a citation of a mere definition for an unproved scalar compatibility. I checked the ramified ring is $A_{E,er}$, not $A_{E,r}$.

Step 4 uses the purity equation of `det-sp-reduction-compatibilities` and the counit equation of `sk-lem-sp-reduction`, for $A_{E,er}\to A_{E,m}$. The first states precisely the equality of reduced purity maps, and the second states precisely the adjunction comparison equation. Substitution in `def-pur-smooth-trace` proves the quotient trace formula; successive integral compact-support reduction is explicitly part of `lem-coef-integral-compact-support`. Both finite rings are unital finite ell-power-torsion rings, and $er\ge m$; no flatness hypothesis is used or needed. This avoids assuming that finite-free trace compatibility alone covers a nonflat further quotient.

Step 5 uses projection naturality/invertibility from `fix-prop-projection-formula` and the operation-domain lemma's linear Hom adjunction. I checked the relevant pair is $(T_E,K)$, with $K$ finite Tor and $T_E$ constructible. The written naturality equation, inverse Hom formula, counit naturality and injectivity of the Hom bijection are a short elementary formal argument, so this step is marked elementary with its dependencies cited. Every component is already a coefficient-module morphism; the result is naturality in the linear categories, not a claim that object-indexed components constitute a linear map on objects.

Step 6 uses the completed tensor/pullback reduction formulas from `lem-pur-integral-operations-preserve-constructible`, the canonical source comparison of `lem-pur-adic-source-finiteness-reductions`, and the quotient-compatible line tensor comparison of `lem-pur-integral-line-reduction-restriction`. The Tate line meets that lemma's locally free rank-one hypothesis by the coefficient-twist datum. `fix-prop-projection-formula` explicitly includes finite reduction. The integral exceptional-adjoint and integral compact-support lemmas give the reduced counit equation used in the displayed transposition calculation. Thus the equality is established in the finite ring's derived category, not merely after restricting scalars and not by assuming that reduction is faithful on integral Hom groups.

Step 7 uses the exact equation of `lem-pur-tensor-trace-transpose`, specialized to the finite twisted unit. I read its hypotheses: $L$ is bounded constructible, $K_m$ has finite Tor amplitude, and the two projection maps are invertible by the cited projection formula. The smooth trace definition identifies its transpose with the unit purity map. The finite purity-map and co-smoothness definitions identify the unit tensor map with identity by the counit/adjunction identity, so that the unit purity map is the inverse diagonal orientation. The tensor-trace equation then gives the displayed finite purity composite, in the correct tensor order. I checked the reassociation and symmetry match the item's $j$, and the even shift gives no extra sign.

Step 8 invokes finite-coefficient smooth purity for the reduced morphism actually identified in Steps 6-7. The operation-domain lemma supplies derived completeness of both source and target. The statement of `sk-lem-pe-derived-nakayama` explicitly concludes an isomorphism from the first reduction for such objects. This is conservativity, not uniqueness of lifts. I tested $d=0$, the identity map, zero input, empty source/target, $E=\mathbf Q_\ell$ (identity scalar comparison), $m=1$, and ramification $e>1$ with $m$ not divisible by $e$. The quotient reduction handles the last case; no generator equality or division by a uniformizer appears.

The citation file is checked against the verbatim statements, and the selected dependencies were also inspected for paths back to the item; none was found. Every fact not handled by the displayed formal algebra is a cited existing node, with no proof-internal construction borrowed from a node whose statement fails to provide it.

## Unfinished work

None within the one-level stage-1 split. No Lean was written and no compiler or Lake command was run. Server dry-run and direct delivery results are recorded by the delivery tool.
