# Worker report: lem-sf-etale-smooth-stratified-ctf

## Files written

- `dag/nodes/sec-six-functors/lem-sf-etale-smooth-stratified-ctf.json`: split; replace the returned seventh step by four short steps. The statement and stage-2 Lean record are unchanged.
- `dag/nodes/sec-six-functors/lem-sf-etale-stratified-stalk-identification.json`: one new statement-only, unsplit helper; no Mathlib match.
- `citations.json`: statement quotes for every citation in all twelve steps.
- `report.md`: repaired report and Q51 review. The retained top-level item copy is synchronized; the search log is retained and extended.

## Attachments

None. Searching the item tag and smooth-stratification terms in the read-only source did not find an exact finished project declaration. Its existing stage-2 record is preserved, not asserted to be a finished proof.

## WANTED

None.

## What was repaired

The human returned the former step 7 (2155 characters) because its derived-stalk and constant-cone arguments were hidden. Starting with the repository's returned proof, I kept steps 1--6 and the two final localization steps, and replaced only step 7 by steps 7--10: local bounded finite-module models; their derived stalk identification; fixed-interval projective replacement and an actual cochain representative; and exact constant realization of that quasi-isomorphism. The final localization step's reference to old step 8 is now a reference to step 11. The replacement steps have lengths 595, 368, 505, and 640 characters. Every step is below 2000 characters.

I repaired defects left in the interrupted sandbox attempt. Its nested item cited a missing stalk-identification node, while the top-level copy instead tried `lem-sfb-connected-etale-perfect-constant`. That theorem gives a new perfect model under a sheafwise Tor hypothesis; it does not identify the particular finite model already chosen in step 7, and step 6 alone had established only stalkwise Tor. I therefore restored the original route and extracted its precise derived-stalk identification as the new helper. The acyclicity draft was unnecessary: the existing exact constant-realization statement and general exact-functor cohomology theorem already imply its entire assertion. I retained that draft as scratch material outside `dag/nodes`, and deliver no acyclicity node. Its searches remain in the log as historical work.

The required first dry run on the retained attempt failed its same-tag duplicate check for the acyclicity draft and `lem-constructible-constant-extension-cover`. The repair eliminates that draft from the delivery rather than merely adding a difference line. The delivered helper addresses the other hidden argument and is not a clause of the stratification theorem.

## Not duplicates

lem-sf-etale-stratified-stalk-identification vs lem-sf-etale-smooth-stratified-ctf: the new helper identifies a given constant local model with a specified geometric stalk, for an arbitrary scheme morphism and arbitrary commutative ring. It neither constructs strata nor asserts local constancy, finite projectivity, a Tor interval, or a localization tower.

lem-sf-etale-stratified-stalk-identification vs lem-sf-etale-generic-exchange-algclosed: the latter proves generic base change of exceptional inverse image and internal Hom over a smooth curve; the new helper concerns neither generic base change nor these operations.

lem-sf-etale-stratified-stalk-identification vs lem-sfb-connected-etale-perfect-constant: the latter constructs a perfect constant model from locally constant cohomology and a sheafwise Tor bound on a nonempty connected scheme. The new helper identifies an already supplied constant complex under an arbitrary morphism with its composite geometric stalk and requires no connectedness, finiteness, Noetherian hypothesis or Tor bound.

lem-sf-etale-stratified-stalk-identification vs lem-weil-pbc-constant-sheaf-geometric-stalk: the latter identifies the abelian-group stalk of one constant sheaf. The extracted helper applies to a derived isomorphism of module complexes and also identifies the inverse-image stalk with the original object's stalk over the specified coefficient ring.

lem-sf-etale-stratified-stalk-identification vs lem-weil-pbc-inverse-image-stalk-germ: the latter gives a natural isomorphism of abelian-group stalks with a unit/germ formula for one sheaf. The new helper gives the derived, module-linear comparison for a supplied constant complex, incorporating constant-stalk and localization compatibility.

The whole DAG was searched by the source tag and constant/stalk/complex concepts; whole-blueprint searches included `constant`, `stalk`, `geometric stalk`, `constant complex`, `stalk constant complex`, and `geometric stalk constant`. The relevant general exactness and derived-constant nodes were read and reused, not copied into new nodes. The explicit extraction requested by the return is the reason for naming the derived-stalk comparison; no proof has been moved into the new node's statement.

## Source error

None. No statement dispute or alteration of the target or item statement was needed.

## What remains unfinished

The new helper is intentionally unsplit, with a self-contained statement and no proof or proof dependencies, and enters the stage-1 queue. No Lean file was written or compiled.

## Review by Q51

I read the returned item and compared both retained sandbox versions with the current shared item. The statement and Lean record agree exactly, and remain unchanged. I read the unit and chapter records and the current supplied blueprint ancestor proof `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-biduality-general/thm-weil-etale-geometric-biduality.proof.md`: paragraph 3 needs preservation on smooth strata over arbitrary algebraically closed fields, which is what this supporting item supplies. The repair keeps the finite-ring local-model route; it does not replace it with the coefficient-scoped pro-etale flat-model route. I read Stacks `etale-cohomology.tex`, Tag 09BI (`lemma-connected-ctf-locally-constant`), including its comparison of constant models on overlaps, Tag 03PT (`lemma-stalk-exact`), Tag 03TT (`lemma-when-ctf`), Tag 03RX (`lemma-kernel-finite-locally-constant`), and Tag 095L (`lemma-ses-associated-to-open`); `sites-cohomology.tex`, Tag 094G (`lemma-locally-constant`); `sites-modules.tex`, Tag 03D8 (`lemma-push-pull-composition-modules`); and `more-algebra.tex`, Tag 0658 (`lemma-perfect`), including its prescribed-interval conclusion.

For the new helper I checked the actual comparison: the constant-section stalk maps are natural in the module maps and scalar actions, hence give an A-linear isomorphism of cochain complexes from the stalk of the termwise constant model to the ring complex. Exact stalks descend to the derived localization; the module-linear inverse-image composition identifies the other side with the original K at the composite point. Thus the conclusion is about a given model and a given point, and does not assume local constancy or Tor amplitude to establish the comparison. Its source is the comparison implicit in Tag 09BI's proof, extracted here as the human requested. I checked the zero complex, a complex in one degree, arbitrary unbounded complexes, the zero ring, and the empty U case (the assertion over geometric points is then vacuous). There is no change of coefficient rings: the constant-section stalk isomorphism identifies the ring with A. The new statement introduces every object, cites the notions it uses, carries no proof sketch, and is strictly smaller than the item. Recorded Mathlib searches are actual `msearch.py` calls: I read the retained logs and the new LeanFinder, LeanSearch, Loogle and source-grep results. The semantic hits concern Zariski structure-sheaf/localized-module or manifold stalks, not the ordinary etale derived comparison. The earlier phrasing and fresh general-morphism phrasing both found no exact match; no unavailable service is recorded as evidence of absence.

For unchanged step 1 I read the finite-type/Noetherian and finite-dimension statements, exact module inverse image, constructible pullback and the Tor/tensor definitions: the tensor unit calculation is written out and the finite ring is Noetherian. Step 2 uses the reduced-induced scheme and exact open/closed statements with the empty complementary open, so it treats nonreduced X correctly. Step 3 uses reduced induced schemes, finite-type Noetherianness, quasi-compact opens and generic constructible constancy, intersecting only finitely many cohomological opens. Step 4 uses the perfect-field geometric-reduced statement, dense smooth locus and finite irreducible components; its explicit component-exclusion opens are nonempty, disjoint and irreducible. Step 5 uses the minimal-closed-subset formulation of Noetherian induction, uniqueness of reduced induced structure and the chain definition of dimension, so termination, ordered peeling and the bound on stratum dimensions follow with their hypotheses. Step 6 uses the constant stalk, exact stalk, stalk-as-pullback, module inverse image and derived tensor/pullback statements with every A-module N, including infinite ones. Thus it establishes precisely the ring Tor condition needed later, without silently assuming a sheafwise Tor condition on a stratum.

In step 7 the cited inverse-image composition and finite-ring derived-local-constancy statements supply the local bounded finite-module complex E on each cover member; exact restrictions from step 1 give its lisse cohomology. Step 8 now uses only the new comparison statement, applied to the composite of the stratum immersion and the cover member, with its geometric point. It identifies that very E with a stalk of K. Transfer of the Tor interval along an isomorphism is elementary. Step 9 uses `lem-weil-bounded-finite-tor-perfect` with the Noetherian finite ring A, bounded finite E and the ring Tor bound just checked; it returns the model in exactly [a,b]. The cited projective definition supplies lifting along the finite-free surjection; the derived map-representative statement applies because Q is bounded above and projective termwise. Step 10 uses the explicit exactness assertion in the statement of `def-sfb-site-derived-constant-module-functor`, not an unproved inference from its name, and the cohomology isomorphism stated by `lem-weil-pbc-exact-functor-complex-cohomology`. They yield zero cohomology of the constant cone. Commutation with the two-term direct sums and signed differential of a cone is elementary. This is why no additional acyclicity node is justified.

For unchanged step 11 the recollement statement explicitly gives the bounded-below triangle and exact closed direct image; `lem-sf-exact-functor-derived-triangulated` supplies preservation of distinguished triangles, and module-linear composition identifies its terms. For step 12 I checked the closed-base-change, closed-proper, Noetherian-open and etale open/proper-interchange statements: the factorization uses the actual fibre product; the open is quasi-compact because X is Noetherian; all objects are bounded below; and both proper maps are closed immersions so their exact direct images compute their derived functors. The extension functor is the ordinary etale one. The case X empty gives an empty tower; a=b and a point stratum keep precisely the prescribed interval. All original hypotheses, including an arbitrary algebraically closed F and an arbitrary finite commutative A, are retained.

I rebuilt `proof_deps` from the step citations and regenerated verbatim quotes for every use. I checked all twelve step lengths; none exceeds 2000 characters. The two generic exactness statements added in step 10 are declared as tool uses in `split_report`, not installed as maintainer-owned `tool_uses`.

Validation: the first repaired server dry run passed at 7cf2c3c459. I then corrected the new helper blueprint `from.via` to include its non-blueprint parent item; the final dry run checks that precise deliverable.
