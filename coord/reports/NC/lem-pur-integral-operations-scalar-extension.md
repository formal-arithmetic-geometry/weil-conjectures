# Stage-1 worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-operations-scalar-extension.json`: statement item, split into nine proof steps; no Mathlib match.
- `citations.json`: every citation of every step, with verbatim statement quotes.

## New nodes

None. No Mathlib leaves were created. All required foundational statements already exist; the item's steps carry the coefficient arguments rather than creating nodes for its clauses.

## Attachments

None. Searches of `WeilConjectures/` by the exact blueprint tag and by integral/scalar-extension notions found no declaration giving all clauses. The upstream master is only reference material; its sorry declarations were not treated as proofs. The source's module-category scalar extension declarations concern ordinary module objects, not this completed derived statement.

## WANTED

None. The blueprint files, Bhatt--Scholze paper, and Stacks sources used are present locally.

## Findings and corrections

The item's statement is retained, with an explicit reference to the already existing integral scalar-extension definition. The rationalization definition and rational scalar-composition lemma were removed from statement dependencies: the formulas quantify only over integral objects and integral extensions. Rational scalar composition alone cannot prove the final integral coherence clause.

The existing finite-coefficient package `lem-coef-finite-free-extension` cannot be cited here: its proof dependency graph returns to this item through the purity/derived-operations definitions (and many other nodes). Its internal-Hom clause also only covers finite-Tor constructible inputs, whereas this item assumes only bounded constructibility. I used neither that package nor any finite-Tor/perfectness hypothesis. Step 1 derives finite freeness by explicit residue-basis lifting using the existing finite-quotient and field-completeness statements.

The product-cone construction in the scalar-extension definition is not literally the identity when L=E. The identity clause is understood, as usual, after its canonical completion-unit identification on complete objects. Step 9 states that identification explicitly. No assertion about literal equality of chain representatives is made.

No statement dispute was found. The operations are comparisons in ambient complete derived categories; the proof does not assert that internal Hom of arbitrary bounded constructible inputs belongs to the bounded constructible subcategory. Only its derived completeness is required and proved.

The chapter and unit records were read. The unit `sk-def-sf-operations` has no proof steps; this item serves the integral/common-stage clause of `def-weil-derived-pullback-tensor-hom`. Chapter and unit files are untouched.

## Unfinished work

None in this one-level split. Existing dependencies retain their own DAG states; no new unsplit children are introduced. The second reader still reviews and delivers this accepted sandbox.

## Not duplicates

No new nodes. Whole-DAG/blueprint searches for scalar extension, finite free coefficients, completed tensor, valuation rings and derived internal Hom found the existing tools used below. No existing blueprint statement states all three integral comparisons together on this domain.

## Review by NC

I read the master blueprint source of the item, its parent definition and unit, the finite-free coefficient-extension blueprint proof as reference, and Bhatt--Scholze §§3.4–3.5 (especially Lemmas 3.4.9, 3.4.11 and Proposition 3.5.1 / Lemma 3.5.6). I checked the actual Stacks source labels and tag table, including sites-modules 093J/093M, algebraization 0998/099B/0A0E, sites-cohomology 06YS/06YY/0G7E/07A4/08J7/08J9/08JB/0941 and injectives 079P. The proof is marked agent-written because the sources provide the individual tools, not this assembled nine-step argument.

For step 1 I opened the coefficient datum, valued-DVR finite-quotient lemma and l-adic field-completeness lemma. They give precisely the DVR power decomposition, finite quotient B/v^e and completeness of E that the written residue-basis argument uses. Completeness of the coefficient sums in E, and convergence of the error in L, are separate: the latter only uses the norm bound |t|^n. Surjectivity and injectivity are both proved in the step, so finite freeness is not taken from an uncited theorem. The residue vector space is finite because its underlying set is finite; a maximal independent subset supplies a finite basis. The ramification index is positive because t is nonzero and has absolute value less than one in L.

For step 2 I opened the completed-coefficient definition and completed-constant-sheaf reduction statement, then read Stacks sites-modules 093J/093M. The latter statement supplies both flatness over the constant ring and the identification of the two-term free reduction complex. Its Noetherian hypothesis holds for the DVR. The fixed integral basis from step 1 persists at every t^n-level. Cofinality here is only ordinary sheaf limits, justified by the explicitly written compatible-family construction; this does not claim that inverse image commutes with infinite limits.

For step 3 I opened the generic ringed Koszul reflector, derived-completeness definition, strict-tower homotopy-limit theorem, and exact countable-product statement. The reflector gives local completeness and its universal property, not merely an existence of some noncanonical Roos vertex. The regular element condition is verified via step 2, so the Koszul tower really is the quotient tower used in the imported definition. Exact products hold for arbitrary coefficient sheaves on the pro-etale site. I wrote the finite-block coordinate elimination that proves cofinal reindexing for the specific arithmetic progression en: it is not an unsupported appeal to cofinality for arbitrary triangulated towers. All limits use strict complex models and induced maps.

For step 4 I opened derived change of rings, the precise integral scalar-extension definition, and its constructible preservation lemma. The first gives K-flat computation, the second specifies the strict quotient tower, and the third is used only for its explicitly stated D^b_c restriction. Finite free extension commutes with products and cones by the displayed finite-coordinate calculation; no infinite-dimensional flat tensor/product commutation is assumed. Step 3 legitimates the cofinal L-levels en, which must not be confused with the numerical E-levels n. For ell != p in the preservation-node notation, p is the fixed residue characteristic of the global coefficient setting; the item's argument and its three ambient comparisons need only the stated invertibility of ell on X,Y, and the preservation property is stipulated in the item rather than newly asserted for a broader scheme class.

For step 5 I opened K-flat resolution, the integral-operations definition, exact finite-constant inverse image, and the generic ringed-topos derived-tensor-pullback theorem. The resolution statement gives flat terms; the generic theorem also gives K-flat pullbacks. Exact finite inverse image applies to the actual finite discrete A/t^n coefficients. Ambient completed ring maps are allowed to be nonisomorphisms; no inverse-image/limit exchange is taken. The ordinary coefficient-pullback comparison is proved on tensor generators, and completion is applied only afterwards. Thus arbitrary f is allowed, without smoothness, properness, finite type or qcqs assumptions.

For step 6 I opened the same integral-operations and generic derived-tensor-pullback statements. Applying the latter to the identity topos with ring map R->S gives precisely ordinary tensor compatibility, before completing. The levelwise identification uses the same coefficient quotient on both factors; flat-term K-flat models compute these tensors. Completeness follows from the already cited reflector, with no assumption that resolutions are constructible termwise.

For step 7 I opened the generic ringed internal-Hom currying/restriction theorem, Koszul reflector and ideal-of-complete-elements theorem. The first applies to arbitrary unbounded objects and all slice sites, so it permits M without a perfectness hypothesis. Two currying formulas and tensor symmetry place the localized coefficient in the second Hom, whose vanishing is the reflector's completeness criterion for N. The ideal statement supplies all local multiples of t, so a single-generator check is sufficient. This establishes completeness, not constructibility, of Hom.

For step 8 I opened the actual derived-internal-Hom definition and K-injective resolution existence statement. Both allow all complexes on a small ringed site. The small sites are interpreted in the project's fixed universe. I wrote the acyclic-test proof that restriction of an S-K-injective complex is R-K-injective, using exact finite free scalar extension; I did not quote a change-of-rings result whose hypotheses may differ. The finite-sum Hom calculation is on complexes representing the second variable and is valid for arbitrary M. Its generator formula checks S-linearity and makes the temporary basis irrelevant. The generic definition supplies the well-definedness of the derived Hom represented this way.

For step 9 I checked the multiplication/evaluation formulas for the two routes through a tower of fields. They agree before localization and completion, and the strict coordinate maps commute with differentials and transitions. The completion reflector's unit supplies the identity comparison; an arbitrary isomorphism of Roos triangles would not suffice. The tensor and Hom comparisons are defined by canonical universal maps, so equality on local pure tensors proves the required coherence, rather than only abstract existence of isomorphisms.

Edge cases checked: L=E gives the unit identification and identity maps; unramified extension e=1 needs no discarded tower coordinates; ramified e>1 uses ideals v^{en}, not equal-index quotients; zero inputs give zero comparisons; torsion coefficients on a point are permitted; a nonperfect or unbounded first Hom argument is allowed by the finite-sum proof. No new statement needed small-case testing. Every actual statement/proof dependency was traversed to rule out a return path to the item. Generic off-unit tools are declared individually in split_report.tool_uses; none replaces a step of a different unit's proof.

I also checked delivery-errors B–E: no new or duplicate nodes, no Mathlib leaf with an unverified match, no false search record, no cited node's proof substituted for its statement, no unmentioned perfection or finiteness hypothesis, no integral inference from a rational-only lemma, and no content moved to children. All item citations have verbatim statement quotes in citations.json. Mathlib searches were made through msearch.py with two semantic phrasings, Loogle patterns and two grep directories; LeanSearch returned Internal Server Error and is recorded as unavailable. I read the underived SheafOfModules pullback candidate source; it does not state the completed derived comparisons.


## Second reading by NC

I independently opened the ancestor blueprint def-weil-derived-pullback-tensor-hom (integral/common-stage paragraph), the unit and chapter records, every cited node statement, and the Stacks .tex statements listed below. The item is an agent-written compatibility result making the ancestor's construction precise, not a theorem literally stated in Stacks. Its finite extensions, completed coefficient categories, arbitrary scheme morphism, invertibility condition, complete constructible inputs, three comparisons and integral coherence agree with that intent. No statement change or dispute is needed.

- Step 1: checked against the coefficient datum, finite-quotient and field-completeness statements and more-algebra Tag 09E4, label definition-extension-discrete-valuation-rings; PASS, the written spanning and independence arguments prove the fixed integral basis and the ramified ideals are v^{en}.
- Step 2: checked against the completed-coefficient definition and completed-constant-sheaf-reduction statement, sites-modules Tags 093J/093M, labels lemma-constant-exact/lemma-completion-flat; PASS, the two-term resolution supplies injectivity and quotient identification, and finite coordinates commute with sheaf limits.
- Step 3: checked against the actual noncanonical definition of derived completeness, strict-tower statement, exact-product statement and reflector statement, algebraization 099B/0A0E and sites-cohomology 0941; FIX, compare rotated Roos triangles to obtain an abstract isomorphism, infer local completeness, then invoke the reflector for the canonical unit. The finite-block elimination is valid also for e=1 and the initial discarded block.
- Step 4: checked against derived-change-of-rings and integral-scalar-extension statements and the prior tower calculation; FIX, remove the constructibility-preservation citation with its extra ell != p hypothesis, since preservation is stipulated by the item. Products/cones commute with finite free extension by the explicit coordinate argument.
- Step 5: checked against K-flat resolution, finite-constant inverse image, integral-operations and generic derived pullback statements, sites-cohomology 06YS/0G7E/06YY; PASS, quotient pullback is computed with flat terms and the ambient completed-ring maps need not be isomorphisms.
- Step 6: checked against integral-operations and derived-tensor-pullback statements, sites-cohomology 07A4, label lemma-pullback-tensor-product; PASS, use the identity topos ring map and the compatible finite quotient tensor identities before completion.
- Step 7: checked against internal-Hom currying/restriction and complete-elements ideal statements, sites-cohomology 08J9/08JB and algebraization 0998, and Bhatt--Scholze Lemma 3.4.11; PASS, localization currying kills Hom into complete N on every slice, without perfectness of M.
- Step 8: checked against the derived-Hom definition and K-injective existence statement, injectives 079P, sites-modules 03EO and sites-cohomology 08FI; FIX, explicitly cite lem-pur-kinjective-restrict-localized before the sectionwise derived adjunction. Read the actual 08FI label lemma-restrict-K-injective-to-open (the existing node's source incorrectly calls it lemma-restriction-K-injective; its statement is correct). Finite sums and the evaluation formula prove the S-linear comparison for arbitrary M.
- Step 9: checked against the reflector's canonical unit and the preceding tensor/evaluation maps; PASS, pure tensor multiplication agrees for both routes through E subset L subset L', and the completion-unit identification supplies the identity case. The calculation is elementary once the preceding comparisons are fixed.
- New nodes: none; B1--B7 and duplicate/Mathlib-leaf checks introduce no further work.

Small cases: zero inputs and the empty scheme give zero objects throughout; L=E gives the canonical completion-unit comparison; e=1 leaves no interior tower coordinates; e>1 uses v^{en}, not v^n; n=1 gives B/tB with its finite residue basis; all towers start at n>=1, so no n=0 assumption enters. Hom's first variable need not be perfect, and no assertion that Hom stays bounded constructible is used. The finite residue quotient is a vector space over A/tA, not over B/vB. I traversed all repaired statement/proof dependencies and found no return path to the item.

Independent searches were run through msearch.py and retained verbatim in searches.jsonl: Loogle with SheafOfModules/pullbackIso, grep for derived Hom/completion coefficient-base-change terminology, and LeanFinder for finite free algebra extension commuting with derived sheaf Hom and adic completion. The Loogle declarations were read at PullbackContinuous.lean:106 and PullbackFree.lean:142; they concern underived sheaf pullback. The other hits concern underived free modules or sheafification, and no exact completed-derived match was found. Exact-id and scalar-extension/Hom searches of the read-only upstream source did not supply a finished declaration of this item. No upstream sorry declaration was counted as proved.

Changes: expanded step 3 to justify the canonical unit from the weaker imported Roos-triangle definition; removed the unnecessary extra-hypothesis constructibility citation from step 4 and proof_deps; added the existing slice K-injectivity citation in step 8 with the correct Stacks label and corrected the location of 03EO to sites-modules.tex; regenerated citations.json with full verbatim statements for every repaired citation; recorded my independent searches. The first worker's report and Review by NC are retained. No new nodes, Lean writes, compilers or builds.
