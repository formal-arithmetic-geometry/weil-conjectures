# Stage-1 report: thm-pur-open-complement-unconditional

## Files written

- `dag/nodes/sec-six-functors/thm-pur-open-complement-unconditional.json`: split statement; uniform constructibility and vanishing, finite coefficient stages, and chart specialization.
- `dag/nodes/sec-six-functors/lem-sf-noetherian-polynomial-dimension.json`: statement, exact Mathlib leaf.
- `citations.json`: one verbatim statement quotation for every step/node citation.

## New nodes

`lem-sf-noetherian-polynomial-dimension`, statement, Mathlib: `MvPolynomial.ringKrullDim_of_isNoetherianRing`, `Mathlib/RingTheory/KrullDimension/Polynomial.lean:120` (formula continues on line 121). This is the installed declaration name; the online Loogle snapshot also returns a newer `_of_finite` spelling, which is not the name recorded here. There are no new unsplit nodes. This leaf is the general ring dimension theorem, not a clause of the open-complement assertion.

## Attachments

None. The required read-only search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by blueprint ID and open-complement terminology found no declaration giving the whole item. The existing general vanishing node has an attached theorem, but it proves only vanishing and is therefore a reusable dependency, not an attachment of this item. The upstream master checkout is not evidence of completed proofs.

## Wanted literature

WANTED: `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-rf-shriek-preservation/thm-pur-open-complement-unconditional.md`, Proof Steps 1-4, for thm-pur-open-complement-unconditional. The shared repository has the imported node and verbatim chapter/unit records but no blueprint directory; `/home/ubuntu/weil-newtargets-master/blueprint/` is also empty. I used the imported proof and read the unit record, and marked the assembled argument as agent-written.

WANTED: local `literature/stacks-project/etale-cohomology.tex`, Theorem 03Q9 (`theorem-higher-direct-images`), for the item's imported strict-local proof provenance. I read the authoritative [Stacks Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9) online without downloading a document into the project. Its theorem states the strict-local stalk identity; the neighbourhood-colimit formula occurs in its proof. The delivered step does not claim that the statement of the existing strict-local node includes this colimit. It uses the independently existing general relative direct-image bound instead.

## Corrections and statement dispute

STATEMENT-DISPUTED: the chart expression `c_U=2(d_U+dim V)` is not a nonnegative integer when an empty affine chart base is admitted: with the DAG's topological dimension convention, `dim(empty)=-infinity`. For example choose an empty chart base and `d_U=0`; its complement and ambient scheme are empty, but the proposed constant is `-infinity`, outside the constants allowed by `def-exc-open-complement-bound`. I explicitly discard empty chart bases, which changes no covering; alternatively they are allowed with constant zero. All nonempty chart bases retain exactly the original constant. I also declare `d` to be nonnegative, make the assembly specialization's finite-type schemes explicit as in the fixed unit statement, and rename the chart base to `B` to avoid confusion with the original open `V`.

The imported proof said that `varpi_E^n` was a power of the rational prime ell. It generally is not, for example in a ramified extension. The repaired argument is `|ell|_E<1`, hence `ell=varpi_E*b` in the valuation ring, hence `ell^n` annihilates its quotient by `varpi_E^n`. No ramification theorem or uniform exponent in n is needed.

The imported step described every etale neighbourhood as finite type and asserted `dim U=dim T`; unrestricted etale neighbourhoods need not be quasi-compact and need not meet the top-dimensional components. The reusable relative bound avoids both errors and already quantifies over arbitrary module sheaves over a separably closed base. Its statement, not details of its proof, is invoked. Its source metadata mentions 0F0C, but [Stacks Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C) is a proper derived base-change theorem, not a direct statement of this relative vanishing bound. I do not use that tag as proof of the vanishing lemma; this existing node's exact relative bound and reviewed proof interface are what the split uses. That metadata defect is reported here without editing another node.

Removed unused proof-dependency entries and added actual generic geometry/dimension citations. Retained the imported `blueprint_*`, `import_flags`, audits, and historical comparison. The historical low-dimensional results are not inputs to the general vanishing/constructibility argument.

## Not duplicates

No existing node states the new Noetherian finite-variable polynomial dimension formula. I searched the full DAG for its declaration, polynomial/dimension terminology, and the entire blueprint via `blueprint_refs.py search` with `polynomial ring`, `affine space dimension`, `dimension of affine`, `Noetherian polynomial`, and `ringKrullDim_of_isNoetherianRing`. The existing finite-type-domain dimension/transcendence-degree nodes and polynomial-ring dimension-at-maximal-ideal nodes have different conclusions and assumptions. `lem-pc-localized-polynomial-tor-bound` mentions the Mathlib formula in its proof but states a Tor bound, not a dimension formula. The new leaf cites Mathlib itself as its exact source; no unverified Stacks tag is assigned to a theorem that is already in Mathlib.

`thm-pur-open-complement-unconditional` has no other blueprint node with the full separably closed-field statement and stage-uniform chart conclusion. `lem-exc-open-complement-known` is only the algebraic-closure-of-a-finite-field case, so is not recorded as `same_as`.

## Review by Q36

I read delivery-errors B-E, the worker rules, the three fixed blueprint levels in SETUP, the chapter and unit records, the imported item, every statement quoted in citations.json, and the installed Mathlib polynomial theorem. The unit's route is unchanged: direct-image finiteness and the finite-type torsion dimension bound discharge the open-complement hypothesis, then the constants are tracked in the affine assembly. Generic tools from other units are declared in `split_report.tool_uses`.

Step 1 uses the quasi-compact-open finite-type lemma exactly for j, the finite-affine-cover lemma after checking V is quasi-compact by a finite union, and the all-affine-pairs criterion for the structure map of T to the field spectrum. The open-immersion definition identifies the underlying open subspace, so the cited open-dimension monotonicity statement applies. This is an actual finite-type proof and does not assume a composition theorem hidden behind a definition.

Step 2 applies the direct-image input theorem with the positive annihilator N=ell^r, invertible in the field, and then unpacks precisely clause (1) of the input definition. Step 1 checked every finite-type hypothesis. The definition of higher direct image covers negative degrees. The coefficient objects throughout are ordinary small-etale module sheaves; the statement about finite coefficient rings makes no pro-etale comparison.

Step 3 uses the full statement of `lem-kun-relative-torsion-direct-image-dimension-bound`: I checked separable closedness (not just algebraic closedness), torsion of the additive coefficient group, local finite type and quasi-compactness of j, local finite type of the target structure morphism, its compositional compatibility, and dim(V)<=d. It proves vanishing for every module sheaf, not only constructible ones. The already reviewed node encapsulates the same neighbourhood/cohomological-dimension method as the unit. It is strictly more general than the vanishing clause here and was not created as a proxy for that clause. This use needs neither an unquoted stalk-colimit assertion nor a silent forgetful-coefficient comparison.

Step 4 unpacks exactly the two clauses of the condition and uses the finite-type dimension theorem only to choose a finite bound depending on T. The argument quantified over A before any stage is chosen, so the bound is independent of A and its annihilator. I checked the empty T case separately.

Step 5 uses the finite coefficient quotient, absolute-value restriction, maximal ideal and uniformizer data stated in the coefficient-extension definition, the ell-adic absolute value in the ell-adic-number definition, and the finite-field datum. The explicit equation ell^n=varpi_E^n*b^n fixes the ramified-extension error. Finiteness and commutativity of A_(E,n), n>=1 and ell!=p are all verified before specialization.

Step 6 checks the chart algebra R is finite type via the all-affine-pairs statement, and obtains Noetherianity of both R and R[x_1,...,x_m] from the affine finite-type theorem. The new Mathlib leaf gives exactly the polynomial dimension formula, with no integral-domain assumption. The spectrum/ring dimension comparison gives the ambient scheme dimension; finite-type dimension gives its finiteness; open-subspace monotonicity gives dim(B)<=dim(Y). The descending-chain assertion in the cited affine theorem proves quasi-compactness of each relevant open by the explicit finite-union argument. No definition of affine space is incorrectly cited as a dimension theorem.

Step 7 is the substitution into the assertion already proved in steps 1-5; it does not invoke a new node restating either clause. Step 8 cites `lem-exc-open-complement-known` only for its explicit historical comparison with the dimension-zero and curve computations, not for a general separably closed-field assertion.

For the only new node I read `Mathlib/RingTheory/KrullDimension/Polynomial.lean`, especially lines 118-132, and matched the local declaration and assumptions to the statement. I tested zero variables, a field, the zero ring (dimension minus infinity on both sides), a ring with nilpotents, and infinite Krull dimension. Finiteness of the variable set and Noetherianity are essential hypotheses and are present. The msearch log contains the exact LeanFinder, Loogle, LeanSearch and grep queries; LeanSearch returned HTTP Internal Server Error and is recorded as unavailable, while LeanFinder and Loogle found the formula and the final grep provided the installed file and line. The online theorem spelling differs from the installed snapshot; the match uses the installed theorem.

I checked C4 by reading and quoting each cited statement, C1 by supplying the geometry, coefficient and dimension tools, and D1/D2 by leaving the actual argument in the item. The new node is only a generic Mathlib dimension leaf. A dependency traversal of the existing inputs found no path back to this item. No Lean, compiler, Lake, live-project write or manual git command was used.

## Unfinished work

No mathematical subtask remains for this one-level split. The second reader must independently review it and deliver; this worker performs only the required no-push dry run.


## Second reading by Q36

- Item statement: compared hypothesis by hypothesis with the imported blueprint node and the fixed unit record `dag/units/sk-prop-sf-rf-shriek-preservation.json`, clauses (ii) and (iv); the worker's nonnegative dimension binder, explicit finite-type chart setting and empty-chart repair are faithful. Tested the empty scheme, empty open, identity open immersion, dimension zero and coefficient zero ring; pass. The blueprint markdown itself is absent, as the worker reported.
- Step 1: checked the statements of the quasi-compact-open finite-type lemma, finite-affine-cover lemma, all-affine-pairs criterion and open-dimension monotonicity, and read Stacks `morphisms.tex`, labels `definition-finite-type` and `lemma-locally-finite-type-characterize` (01T0/01T2), and `topology.tex`, `definition-Krull` and the following remark (0055); all hypotheses match and the finite-union argument supplies quasi-compactness; pass.
- Step 2: checked `thm-exc-direct-image-input-holds` and both clauses of `def-exc-direct-image-input`; the positive annihilator is invertible in the field and all three finite-type assumptions hold. Repaired the negative-degree sentence: the definition of a right derived functor does not itself state connectivity. Now cites the existing negative-vanishing theorem, checks both Grothendieck hypotheses with the existing module-sheaf theorem and left exactness with the direct-image definition, and explains why zero is constructible; pass after repair. Read Stacks `derived.tex`, 05TC, `lemma-negative-vanishing`, part (1).
- Step 3: checked every assumption of `lem-kun-relative-torsion-direct-image-dimension-bound` directly against its statement and its recorded Lean theorem signature: separable closedness, torsion coefficients, quasi-compactness, local finite type, compositional compatibility and the bound on the source dimension. Its conclusion covers all module sheaves and precisely the requested integer degrees; pass. Its source file is absent from the specified slopmaster2 checkout; it is reused as an existing DAG theorem, not claimed as an attachment of this item.
- Step 4: compared with both clauses of `def-exc-open-complement-bound` and the statement of `lem-kun-dimension-finite-type`; the coefficient quantifier remains unrestricted within the stated class and the empty case uses zero, not minus infinity; pass.
- Step 5: compared with the full coefficient-extension, ell-adic-number and finite-field definitions; `ell=varpi_E*b` gives `ell^n=varpi_E^n*b^n`, so even a ramified extension at n=1 is covered. Finiteness, commutativity and ell different from p are present; pass.
- Step 6: checked the affine-space chart definition, finite-type affine-pairs criterion, finite-type Noetherian theorem, polynomial dimension leaf, spectrum/ring dimension comparison, finite dimension theorem and open-dimension inequality. The finite generator argument applies also to nonreduced R; the ascending-open-chain argument checks quasi-compactness on every affine open; pass.
- Step 7: substituted the nonnegative integer m+dim(B) into the result of steps 1-5 and checked m=0, a zero-dimensional nonempty B and empty B separately; constants are stage independent and no conclusion of general admissibility is used; pass.
- Step 8: compared the final historical assertion with the complete statement of `lem-exc-open-complement-known`; it states precisely the independent dimension-zero and curve computations and is not used for the general case; pass.
- New node `lem-sf-noetherian-polynomial-dimension`: independently read installed Mathlib `RingTheory/KrullDimension/Polynomial.lean`, hypotheses at line 43 and theorem at lines 118-132; exact finite-variable Noetherian formula, including the zero ring, empty variable set, a field, dual numbers and infinite Krull dimension; pass. Its three definition dependencies define exactly Noetherianity, the polynomial ring and the extended-valued Krull dimension. Made n explicitly natural. Independent DAG/blueprint searches found no statement duplicate; nearby field-localization and Tor-bound nodes have different conclusions. Fresh LeanFinder, Loogle and grep searches used different phrasing and are recorded verbatim by msearch.py in searches.jsonl and summarized on the leaf.

Changes and reasons:

- Replaced the unsupported negative-degree appeal to a definition with two existing theorem citations and explicit hypothesis checks (C3/C4); added their generic-tool rationale in `split_report.tool_uses` and their complete verbatim statements in citations.json.
- Declared the leaf's cardinality n to be natural explicitly (B2), refreshed its quotation and recorded independent searches. No new mathematical node was introduced or removed: the single new node is an exact Mathlib leaf, neither elementary nor a restatement of the item.
- Preserved all first-worker report sections. The later human decision in SETUP.md (2026-10-10 evening, fourth decision) explicitly permits worker declarations in `split_report.tool_uses`; these are retained and no maintainer `tool_uses` field is written.
- Located a read-only Stacks checkout at `/home/ubuntu/c1-stacks-review/` and checked its tag registry and the TeX at 03Q9 (`theorem-higher-direct-images`, especially the affine-neighbourhood restriction in its proof), 01T2 and 0055. This supplies the local TeX check missing from the first worker's reading; no literature was downloaded or changed. The 03Q9 formula is not silently used as a neighbourhood-colimit statement in this split.

The citation file was regenerated from the repaired uses lists and exact current node statements. No Lean, compiler, Lake, manual git command, live-project write, launcher modification or sub-agent was used.

Dependency audit: none of the repaired proof dependencies has a path back to this item. A full transitive walk also encounters pre-existing baseline defects outside this delivery, including `thm-weil-pbc-hypercover-cohomology` ↔ `thm-weil-pbc-hypercover-cohomology-abelian-part` and the missing reference `lem-weil-pbc-category-colimit`. These are reported for the maintainer and are not repaired by editing unrelated nodes. All 25 citation quotations match and the item's proof dependency list is exactly the union of its step citations.

Validation: required `deliver.py Q36 thm-pur-open-complement-unconditional --no-push` completed successfully: `OK (not pushed) deliver/Q36/thm-pur-open-complement-unconditional at 87e66d894a: preflight passed`. No preflight repair was required after the second-reading changes.
