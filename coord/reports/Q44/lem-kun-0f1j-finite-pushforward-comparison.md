# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-0f1j-finite-pushforward-comparison.json`: statement, now split into eight steps; Mathlib searches find no exact match. No new nodes and no Mathlib leaves were created.
- `citations.json`: a verbatim statement quotation for every use in every step.
- This report. `prepare.py` is a sandbox-only preparation script; `searches.jsonl` is the search tool's log.

## Attachments

None. I searched the slopmaster2 project by the exact item id, 0F1J/0f1j, finite pushforward, and tensor/projection/base-change terminology. The finite exchange, exactness, and projection/base-change naturality declarations supply ingredients, not the full item. In particular Finite/BaseChange.lean:327 and :354 prove finite exchange, and Finite/Exact.lean:124 and :138 supply finite exactness and the derived identification. They do not state this tensor comparison. The archived master is not treated as a closed proof.

## WANTED

None.

## Corrections and limitations

The item was unsplit and the sandbox had no prior item copy or report at the start. I retained the inherited searches, citations and ancestry and added the searches actually run in this dispatch. I normalized the statement's inherited doubled TeX escapes; its mathematical content, hypotheses and conclusion are unchanged. The first draft's accidental double-quote notation for primes was removed before delivery. I replaced its vague naturality assertion with the explicit successive-adjunction calculation in Steps 5--7 and replaced its abelian-only derived composition citation with the existing module-valued ringed-topos composition node. I removed the unnecessary dependency on the untensored base-change isomorphism theorem: the item asserts an implication, and that follows functorially once the maps agree. Nothing remains unfinished at this stage.

## Source error

Stacks `etale-cohomology.tex`, Tag 0F1J (`lemma-punctual-base-change-upgrade`), the last displayed calculation, writes `R^q h_*(rho_i^{-1}e^{-1}F)` in the middle line. Its argument is on `Y_i`, whereas `h` has source `Y`: the correctly typed expression is `R^q h_*(rho_{i,*}rho_i^{-1}e^{-1}F)`. For example, for a two-point finite cover of a point, pushforward is the two-factor product, and dropping it discards the finite-cover factor (as well as producing the type error). Step 4 keeps `rho_*`; composition then gives `pi'_* Rh_{i,*}`. This is a correction of the intermediate proof formula, not a disputed item statement.

## Blueprint and duplicate searches

I read the chapter record `sec-smooth-purity`, unit record `sk-prop-sf-kunneth-ordinary`, the ancestor `lem-kun-0f1j`, and its current `main-20261015` blueprint text. The route is exactly its finite-pushforward calculation. `tools/blueprint_refs.py ancestor` gives `lem-kun-0f1j`; blueprint searches for finite projection, direct image composition, finite-pushforward and projection-formula were read alongside DAG-wide title/statement searches for exchange, finite exactness, composition, and counit compatibility. These found the existing ingredient nodes used here, not a second statement of the item. No new node therefore requires a Not duplicates pair. I did not edit any unit or maintainer-owned metadata.

## Mathlib searches

The tool log records LeanSearch, LeanFinder, Loogle and grep, with two semantic phrasings. I read the hits: the relevant-looking `SheafOfModules` declarations are ordinary sheaf pushforward/unit/component formulas; the ring-theoretic etale and tensor hits have different objects. The grep hits for stability of finite morphisms under base change do not give the derived tensor-comparison statement. Loogle's unknown-identifier response for `IsIso` is retained as a query diagnostic, not asserted to establish absence. The other semantic searches and grep also give no match. All appended search entries are the exact tool/query pairs and raw logged results. The older search records were inherited from the original node and retained.

## Review by Q44

I read Stacks Tag 0F1J's final diagram and two calculations, the actual finite exchange statement/proof at Tag 0959, the finite stalk and vanishing proposition at Tag 03QP, and the torsion-ring projection formula at Tag 0F0G. For geometry I checked Morphisms Tag 01WL (`lemma-base-change-finite`) and Tag 01WN (`lemma-finite-proper`). For composition I read `sites-cohomology.tex`, Tag 0D6E (`lemma-derived-pushforward-composition`) and its adjoint-uniqueness proof, and `categories.tex`, Tag 0DV0 (`lemma-compose-counits`). There are no new nodes whose source needs a separate review, and no SGA source is used.

I opened every cited node and compared its statement, not its proof, with the use. Step 1 uses `lem-weil-pbc-finite-morphism-permanence`(a) and `lem-weil-pbc-finite-proper` to establish the precise geometric hypotheses. `lemma-weil-pbc-finite-direct-image-exact` states exactness only for abelian sheaves; the step explicitly extends it using `def-weil-pbc-direct-image` (the same underlying functor) and the faithful exact forgetful functor of `lem-weil-pbc-module-sheaves-colimits-forgetful`(1). An exact faithful functor detects exactness since its kernel/cokernel images are zero only when their identity maps are zero. `lem-weil-pbc-exact-functor-derived-functor` then really does say every complex computes the derived functor. This repairs the original missing finite exactness justification.

Step 2 takes the two genuine finite exchange isomorphisms from `lemma-weil-pbc-finite-exchange`; `lem-weil-pbc-exchange-forget-coefficients` explicitly identifies the module exchange with the abelian exchange and detects its invertibility. `prop-weil-pbc-inverse-image-modules-exact`(1) supplies preservation of the constant coefficient ring, and `lem-weil-pbc-inverse-image-composition-module-linear` supplies the module-linear composition and unit normalization. No finite type or finite presentation of the schemes is introduced.

Step 3 specializes `lem-kun-0f0g` with E the unit and K=A; k is a torsion commutative ring and the map is proper by Step 1. `def-kun-projection-formula-map` states exactly its counit-defined adjunct, while `lem-kun-inverse-image-monoidal` provides the specified derived tensor identification. The coefficient unit is flat by its free rank-one construction, so removing it is immediate from the tensor definition. Step 4 uses the same facts for rho. `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` genuinely states composition for module derived categories with arbitrary ring sheaves, so it applies to constant k on these small etale sites; this avoids citing the abelian-only composition definition for a module theorem.

Step 5 checks the normalization used in the next calculation. `lem-weil-pbc-right-adjoint-preserves-kinjective` applies because the module inverse image is exact by `prop-weil-pbc-inverse-image-modules-exact`(3). Thus the composition theorem's stated K-injective normalization can use an identity second resolution. The module composition theorem's unit normalization and the explicit successive Hom bijection in `def-weil-pbc-composite-adjunction` give the common adjunction. This is the routine calculation from the cited statements, not an unmentioned comparison theorem.

Steps 6 and 7 are elementary expansions of those already cited adjunction and projection definitions. I checked the sources and targets of s and t: both start at rho^{-1}h^{-1}(P tensor A) and end at Q on Y_i. The transpose of the left route has first factor epsilon_rho composed with rho^{-1}E; the right route has first factor h_i^{-1}epsilon_pi'. `def-weil-pbc-underived-exchange` states precisely that these are equal, with the cartesian pullback identification. The other factor is rho^{-1}delta on both sides. The module adjunction clause of `prop-weil-pbc-inverse-image-modules-exact` guarantees the same counits, so this equality is module-linear. Injectivity of a Hom bijection proves the equality of maps on X'. Step 8 writes out the inverse using the functorial inverse of beta; it uses no base-change invertibility theorem. Each non-elementary step is under 2000 characters, and no smaller hidden lemma has been packaged as a new node.

Small cases: pi the identity gives the usual comparison with the tensor unit; an empty finite source makes P, both objects and both arrows zero; the zero sheaf F gives zero throughout; the disjoint union of two identity covers gives two copies with the same componentwise counit formula, and exposes the source's omitted rho_* factor. Ramified/nonflat finite maps are allowed, since none of the steps requires pi to be etale or flat. No assumption of a finite-type, Noetherian, quasi-compact or separated X is used. g's qcqs and ell's invertibility hypotheses remain exactly those of the item; this finite formal reduction does not need to use them. The generic off-unit exactness, coefficient, and composition nodes are declared in `split_report.tool_uses`; they implement the source's finite-pushforward route rather than replace it. B1--B9 are vacuous for new nodes; C1/C4 were checked against the verbatim quotations, D1/D2 do not occur because no clause has been moved to another node, and the E hypothesis/type checks are as above.
