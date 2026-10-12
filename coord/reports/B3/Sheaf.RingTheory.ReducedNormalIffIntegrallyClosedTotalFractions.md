## What changed

Replaced the single sorry in `reduced_normal_iff_integrallyClosed_totalFractions` by a
compiling proof of both equivalences, with its original signature unchanged. Normality
implies integral closedness using `integral_totalFraction_mem_range_of_normal`. A new,
strictly weaker domain-decomposition theorem supplies domain factors. The main module
proves their integral closedness using `integralClosure_finite_pi`, Mathlib localization
of products, and transport across ring equivalences. It proves the converse using
`Pi.isNormalRing_of_finite` and prime-localization ring equivalences.

Two proved private helpers implement coordinatewise nonzerodivisors and inheritance of
integral closedness by finite product factors. The algebra structures supplied by
`integralClosure_finite_pi` are reconciled using `toAlgebra_algebraMap`.

Added proof imports `Mathlib.RingTheory.Localization.Pi` and
`Sheaf.RingTheory.IntegrallyClosedReducedFiniteDomainDecomposition`. Updated the original
node's proof and proof dependencies to match this argument.

## Proved and sorry left

Closed the original hole in `reduced_normal_iff_integrallyClosed_totalFractions`
(node `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`).
No sorry remains in the item's module.

Added one hole: `exists_finite_domain_factors_of_integrallyClosed_totalFractions`
(node `lem-weil-pbc-integrally-closed-reduced-finite-domain-decomposition`), in
`Sheaf.RingTheory.IntegrallyClosedReducedFiniteDomainDecomposition`. This is a
decomposition, not a complete sorry-free proof: one hole closed and one added.
The new theorem gives only domain factors; integral closedness of those factors and both
converse directions are proved in the original module. Existing dependency holes in
`integral_totalFraction_mem_range_of_normal`, `integralClosure_finite_pi`, and
`Pi.isNormalRing_of_finite` are used, unchanged.

Local compilation of both modules succeeds. The new statement covers the zero ring by
n = 0, domains by n = 1, and finite products by their coordinate domains. It asserts no
Noetherian hypothesis and no nontriviality hypothesis on R. The two private helpers allow
empty index sets. The new theorem follows the field-decomposition and idempotent parts
of Stacks Tag 030C; its docstring contains the complete natural-language argument.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`
(node `lem-weil-pbc-localization-prime-residue-field-iso`) from the item's module.
Its use for total-fraction decomposition remains recorded under the new domain-factor
node, so this is a relocated dependency, not a claim of global pruning.

The original node no longer directly uses
`lem-weil-pbc-reduced-zerodivisors-union-minimal-primes`,
`lem-weil-pbc-minimal-prime-reduced-localization-field`,
`lem-weil-pbc-product-of-localizations-at-maximal`,
`lem-weil-pbc-prime-avoidance`, or
`lem-weil-pbc-zero-locus-eq-iff-radical-eq`.
These remain needed by the new domain-decomposition node. No module is claimed globally
unreachable. All remaining proof imports are used. Statement imports remain necessary.

## Where the brief, the DAG or earlier work was wrong

The plan's idempotent-decomposition step has no existing Lean declaration stating its
conclusion. The new node isolates precisely that part, without moving the full normality
criterion into a renamed theorem. The finite-product integral-closure statement's explicit
ring-homomorphism algebra structures require propositional transport before applying it
to canonical fraction-ring algebras; the private helper handles this.

LeanSearch returned Internal Server Error and was recorded as unavailable. LeanFinder,
Loogle and source grep found no full theorem or domain-decomposition theorem. Blueprint
searches for `finite product of domains` and `030C` returned zero matches. Stacks Tag
030C was read at https://stacks.math.columbia.edu/tag/030C because the local literature
checkout lacks algebra.tex. The unit's realized statements and route are unchanged.

## New nodes

`lem-weil-pbc-integrally-closed-reduced-finite-domain-decomposition` states the domain-factor
portion of Tag 030C. Its new module is
`lean/Sheaf/RingTheory/IntegrallyClosedReducedFiniteDomainDecomposition.lean`.
It carries the total-fraction decomposition and idempotent lifting argument and deliberately
leaves the integral closedness of factors for the original module's proved argument.
No definition or existing statement changed; no change record is needed.


## Second reading by B3

1. Compared the delivered original module with the repository using diff. Its public
   imports, theorem name, universes, parameters, hypotheses, and conclusion are unchanged
   byte for byte. Only proof imports, two private proved helpers, and the theorem body
   changed. The new module contains one theorem, no definition. No change record is needed.
   Verdict: no existing statement or data changed.
2. Compiled both delivered modules in import order with lcompile.py --all; both succeeded
   without warnings. Scratch copies with #print axioms checked the main theorem, both
   private helpers, and the split theorem. The cancellation helper uses only propext,
   Classical.choice and Quot.sound; the other declarations additionally use sorryAx from
   the explicitly reported open statements. There are no forbidden declarations or hollow
   definitions. The existential domain factors are eliminated inside a proof of a
   proposition, never used to define arbitrary data. Verdict: valid kernel-checked
   reduction, conditional on the named open dependencies.
3. Read Stacks Algebra Tag 030C (lemma-characterize-reduced-ring-normal), including its
   second and third proof paragraphs, at https://stacks.math.columbia.edu/tag/030C. The new
   theorem is precisely the domain-factor portion: reducedness and finite minimal primes
   give the field decomposition of total fractions, integral closedness lifts the coordinate
   idempotents, and their image rings inject into the corresponding fields. In the zero
   ring there are no minimal primes and the empty product works; an integrally closed
   domain has one factor; a finite product of integrally closed domains has its coordinate
   factors. Reduced rings with intersecting components are excluded by the integral
   closedness hypothesis, not by an added domain or Noetherian assumption. The factors'
   integral closedness is genuinely proved separately in the original module. The new
   statement is strictly weaker than the item and omits both converse implications.
   Its complete proof docstring and matching new node are present. Independent searches
   used LeanFinder for orthogonal idempotent domain decomposition, Loogle for
   nonZeroDivisors/Submonoid.pi and IsIntegrallyClosed/Function.Surjective, and source rg
   through Sheaf, upstream ring theory and Mathlib. LeanFinder found
   CompleteOrthogonalIdempotents.ringEquivOfComm and bijective_pi, which implement only
   the last idempotent decomposition step, not the total-fraction decomposition or lifting
   needed to close the new hole. No existing theorem closes that hole in a few lines.
   Verdict: true, necessary, strictly smaller sourced split; not a renamed full criterion.
4. Read the proof from the main theorem downward. Normal-to-closed uses exactly the
   elementwise range assertion of integral_totalFraction_mem_range_of_normal. For the
   factor argument, coordinate cancellation establishes the product nonzerodivisors
   even for an empty index set; Mathlib Localization.Pi supplies the product localization;
   integralClosure_finite_pi's injective-map clause gives precisely the needed factor
   integral closedness after the algebra structures are reconciled. For product-to-normal,
   the factors are domains before applying Mathlib's integrally closed localization lemma;
   Pi.isNormalRing_of_finite and Localization.localRingEquiv then transport both domain
   and integral closedness back to R. Each proof import is used, and public imports are
   required by the statement. Compared the old proof_deps with the new list: all six
   removed direct dependencies are named in No longer needed, with their relocation to
   the new node made explicit. Read dag/units/sk-thm-p1.json: neither item is a realized
   unit statement or step, and all realized entries and the chapter/unit route remain.
   Verdict: correct top-down reduction and honest pruning report; no global pruning claimed.
5. Compared both node records with their Lean modules and the existing dependency
   declarations. The original node's four proof dependencies are exactly the four Sheaf
   statements used by the proof. The new node's first step uses the existing zerodivisor,
   minimal-prime-field, prime-avoidance, localization-correspondence, nilradical and
   product-localization statements; its second step is the sourced idempotent argument.
   Its statement matches Fin n domain factors without asserting integral closedness.
   Source, proof_origin, blueprint ancestry, searches, created, chapter, unit and lean
   records are present. Existing-node changes are confined to proof, proof_deps and
   proof_origin. Verdict: DAG and Lean agree.

Changes by the second reader: added this independent review and recorded additional
searches in the sandbox search log. No Lean proof, statement, import or node needed repair.
One original hole closed, one domain-factor hole added; this remains a decomposition with
net zero holes closed, not a sorry-free proof.
