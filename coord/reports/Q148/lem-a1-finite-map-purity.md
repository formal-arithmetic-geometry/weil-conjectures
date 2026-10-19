# Worker report

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-finite-map-purity.json: statement item, split; statement unchanged; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-a1-finite-etale-weil-fibre-comparison.json: one new statement-only, unsplit comparison lemma; no Mathlib match, four search kinds and a second semantic phrasing recorded.
- citations.json: verbatim statement excerpts for all five step/node citations.

The split follows the current main-20261015 proof of lem-a1-finite-map-purity. It first compares a pushforward stalk with the finite fibre over the residue field, then uses the existing lem-a1-finite-weil-sections-decomposition, and finally proves the eigenvalue and norm implications in the item. The new lemma has no weight assumption or conclusion. The unit sk-thm-dl-a1-upper and chapter sec-deligne-laumon-a1 were read and are untouched; the item is not their key statement.

## Attachments

No finished declaration states the item in the available slopmaster2 checkout. Searches by the blueprint tag, lowerStar_of_isFinite, punctual-purity predicate, finite stalk and Frobenius concepts found no such declaration. The audit's module WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage is missing in both available source checkouts. Its recorded state is rests_on_sorry, which also disqualifies the recorded theorem as an attachment. No new claim of closed Lean is made.

AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine belongs to existing lem-sf-adic-affine-direct-image-finiteness: I read LowerStar.lean:411-415 and matched its algebraically closed characteristic-not-ell base, affine source and target, locally finite type morphism, constructible input and bounded constructible output with that node. It is sorry_here; it is not needed by this finite-fibre proof.

The audit's other entries already attached to prop-functor-package or lem-zl-morphism-open-closed-reduction remain as imported. The two unattached entries nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion and isZero_higherLowerStar_of_isFinite, and the unattached sum_trace_compactlySupportedCohomology, cannot be read at the recorded paths: LowerShriekFunctoriality.lean, QuasiFiniteVanishing.lean and GrothendieckLefschetz.lean are missing. Whole-WeilConjectures name searches in both checkouts found none of those names. I have not fabricated their statements or manufactured nodes from an obsolete audit. Their full audit remains untouched for the maintainer. This proof uses neither compact-support functoriality for open immersions nor a global trace formula.

## WANTED

No missing mathematical literature for this split. The audit needs refresh against the currently available source checkout; the missing Lean modules are reference/audit discrepancies, not a request for a different proof route.

## What was wrong and what changed

The imported statement is true and remains verbatim. Its stmt_deps named only general scheme conventions; the purity predicate, Weil sheaf and rational direct-image notions are now named too. The imported one-paragraph proof cited an ordinary abelian-etale stalk formula for a rational Weil object and silently assumed Frobenius equivariance and the correctly normalized return operator. I read that formula's statement and Stacks 03QP: neither states those rational/Weil assertions. The missing comparison is therefore one statement-only lemma. I also found the existing finite Weil-sections decomposition and reused it, rather than making another cycle decomposition node. The eigenvalue relation now follows by projecting a nonzero eigenvector, without a semisimplicity assumption. The finite-field cardinality and positive e-th-root argument are explicit elementary steps.

The proof_origin is agent: the main blueprint is agent-written, and the additional equivariant comparison is an agent refinement. Stacks 03QP is cited precisely as the finite-level input; Deligne II supplies the coefficient/Weil/local-Frobenius definitions. I do not attribute the new comparison verbatim to Stacks. No SGA source is used.

## What remains

The new comparison lemma is intentionally unsplit, with no proof sketch in its statement and no proof dependencies. Its future split can use finite-etale local splitting and finite-level Stacks 03QP, or properly coherent coefficient-stage finite base change, but must prove the equivariance at the rational stage as stated. All calculations needed after that comparison and the existing finite-sections node are present in the item. No Lean was written or compiled.

## Review by Q148

I read the main-20261015 statement file and separate proof file for the item, the older master statement/proof, the unit and chapter records, Stacks etale-cohomology.tex at proposition-finite-higher-direct-image-zero (Tag 03QP), and Deligne II printed pages 150-154. Deligne (1.1.3) gives rationalization and common coefficient fields, (1.1.7)-(1.1.10) distinguish geometric Frobenius, local Frobenius and Weil actions, (1.1.8) identifies finite-extension local Frobenius with a power, and (1.2.5)(i)/(1.2.6) explicitly include preservation under finite direct image, with real iota-weights. The new lemma makes precise the missing relative rational comparison; its source openly distinguishes finite-level source text from agent formulation. The item's etale hypothesis is retained, although Deligne's stability is more general.

Step 1 uses three opened statements. The new comparison ensures the pushforward is a constructible Weil sheaf and identifies its local Frobenius with global Frobenius on its finite fibre over L=kappa(y); it additionally identifies that fibre's local operators with the original local F_x. Existing lem-a1-finite-weil-sections-decomposition expressly gives the direct sum, finite-dimensionality, cyclic stalk permutation and e-th-power return identity for H_c^0 of any finite scheme over a finite field. It can be instantiated with L as the base finite field and k as its chosen algebraic closure; its residue degrees then are exactly [kappa(x):kappa(y)]. Def-weil-punctual-weights fixes the coefficient category and purity predicate. All three excerpts in citations.json include the assertions used. Ordinary lemma-weil-pbc-finite-stalk-formula is not claimed to supply rational comparison or equivariance.

Step 2 uses exactly the finite-sections node's block preservation and component return identity. For T v=lambda v, each block projection commutes with T, so some nonzero block is an eigenvector. Taking T^e and a nonzero component gives F_x u=lambda^e u. These are two direct applications of linearity to a vector, not a spectral mapping theorem being used without citation. Jordan blocks cause no difficulty; no diagonalizability, irreducibility or lissity is assumed.

Step 3 uses exactly the definition of punctual purity at the closed point x, with alpha=lambda^e. The field count q_x=q_y^e follows by coordinates in a basis of kappa(x) over kappa(y); the norm and real-power equality use q_y>0 and e>=1. The map iota is a field isomorphism, so its value on a power is the same power. Both quantities are nonnegative and positive-base real powers are positive, so the e-th-root inference applies for all real w, including negative and zero weights. The final universally quantified predicate is precisely the definition cited.

For the new statement I checked the finite-field, characteristic-not-ell, finite-type and finite-etale hypotheses against the objects needed by the item; no separatedness or lisse assumption was introduced. A closed point of the finite fibre has the same residue field as its image x, so local iteration counts agree: e*d_y=[kappa(x):k_0]. Thus it is F_y, not the single global q-Frobenius step, which permutes e relative lifts. This normalization is explicitly part of the new comparison, not asserted as an elementary transport. The coefficient stage used for stalks, cohomology and operators is one common finite extension of Q_l before extending to Qbar_l.

I tested empty X and fibres outside the image (both sides zero and purity vacuous), identity maps (e=1), disjoint finite etale components (direct sums), and Spec F_(q^2) -> Spec F_q with a rank-one return alpha: the induced operator has matrix [[0,alpha],[1,0]], so lambda^2=alpha and the norm has the required weight. A degree-d closed y replaces q by q^d and retains e as relative degree. The identity map with a nontrivial invertible Jordan block shows the proof does not sneak in semisimplicity. These tests also apply when the source sheaf has zero stalks or is constructible but not lisse.

For B1-B9 I checked that the only new node has a self-contained statement, named definition dependencies, empty proof/proof_deps, null proof_origin and mathlib_match, status unsplit, correct same-chapter/unit metadata, exact blueprint ancestry and all real logged search queries. The arithmetic steps are not new nodes. Whole-DAG keyword searches, source-tag searches and whole-blueprint searches via blueprint_refs.py found the finite-sections node but no existing relative rational Weil-fibre comparison. The Mathlib hits include topological stalkPushforward (a map, not a finite-etale rational equivariant isomorphism), Zariski structure-sheaf pushforwards, scheme residue maps, constructible images and fibre finiteness; none is an exact match or one-line specialization. LeanSearch and LeanFinder gave actual results; no unavailable service was recorded as absence.

For C1/C4 I read every cited statement and separated the unproved comparison from the elementary calculation. For D1/D2 the new statement contains no purity predicate or bound: the item itself still derives the eigenvalue relation and weight equality. For E I checked the field/degree normalizations, the correct fibre X_0 times_(Y_0) Spec kappa(y), and the nonzero-component argument. No non-elementary proof step exceeds 2000 characters. The only substantive correction during self-review was to reuse the already existing finite-sections cycle decomposition and narrow the new child to relative fibre comparison. I checked that the new child has no dependency path back to the item. No off-unit proof tool is required, because finite-sections and the new child share this item's unit and the other citation is a definition.

## Not duplicates

lem-a1-finite-etale-weil-fibre-comparison vs g1-finite-pushforward-coefficient-control: the existing statement concerns finitepushforwardcoefficientcontrol, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs g1-finite-pushforward-cohomology-comparison: the existing statement concerns finitepushforwardcohomologycomparison, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs g1-finite-pushforward-pullback-comparison: the existing statement concerns finitepushforwardpullbackcomparison, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-a1-finite-map-purity: the item derives a punctual weight equality; the new comparison has no weight hypothesis or conclusion.

lem-a1-finite-etale-weil-fibre-comparison vs lem-a1-finite-weil-sections-decomposition: the existing node starts with H_c^0 of a finite scheme and gives its cycle decomposition; the new node identifies a relative direct-image stalk with that H_c^0 and matches local operators before the existing result can be applied.

lem-a1-finite-etale-weil-fibre-comparison vs lem-asd-supported-kummer-scalar-source: the existing statement concerns derived scalar extension of a closed supported constant sheaf, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-sbc-closed-coefficient-source-transition-iso: the existing statement concerns for a closed immersion i:z→t and a sheaf g on z, the canonical source transition with coefficient i_*g is an isomorphism in every degree q., with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-sbc-closed-coefficient-target-transition-iso: the existing statement concerns for a cartesian square y→t over x→s, a closed immersion i:z→t, and the corresponding cartesian square yz→z, the canonical target transition is an isomorphism with coefficient i_*g., with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-trf-finite-scheme-derived-germs: the existing node gives finite-coefficient derived germ maps for a finite geometric scheme and k-endomorphisms; the new node compares a relative rational Weil pushforward stalk and Frobenius over a residue field.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-curve-assertions-dense-open: the existing statement concerns the eight curve assertions and restriction to a dense open, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-curve-assertions-finite-pushforward: the existing statement concerns the eight curve assertions pass to finite direct images, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-finite-pushforward-cohomology: the existing statement concerns finite direct image does not change etale cohomology (edge map), with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-finite-pushforward-unit-edge-compatibility: the existing node proves compatibility of ordinary abelian cohomological edge maps with units and a second morphism; it has no rational Weil local-operator comparison.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-finite-split-neighbourhoods-cofinal: the existing statement concerns cofiltered split neighbourhoods compute the base stalk, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-finite-split-pieces-cofinal: the existing statement concerns split pieces compute each fibre stalk, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-finite-split-sections-product: the existing node gives products of sections on split neighbourhoods for any product-bearing value category; it does not identify rational Weil Frobenius or the common-stage finite-fibre cohomology.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-finite-stalk-formula-restriction: the existing node gives ordinary abelian-etale restriction of germs; the new node is a rational Weil-stalk-to-cohomology comparison with relative/local Frobenius.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-finite-surjective-unit-mono: the existing statement concerns the unit along a finite surjective morphism is a monomorphism, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-sepclosed-finite-extension-unique-embedding: the existing node concerns finite extensions of separably closed fields; the new node compares rational sheaf stalks and finite-fibre cohomology.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-sets-finite-pushforward-stalk: the existing statement concerns stalk of a finite direct image of an etale sheaf of sets, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite: the existing statement concerns finite geometric fibre of a finite morphism, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective: the existing statement concerns restriction map bijectivity assuming finite fibre, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: the existing statement concerns stalk of a direct image of sets as sections over the strict henselization, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs lem-zl-finite-pushforward: the existing node states an upper-weight stability result for complexes and does not supply the rational relative-fibre/local-Frobenius comparison used here.

lem-a1-finite-etale-weil-fibre-comparison vs lemma-weil-pbc-finite-stalk-formula: the existing node is the finite direct-image formula for ordinary abelian-etale sheaves, with no rational coefficient or Frobenius compatibility.

lem-a1-finite-etale-weil-fibre-comparison vs new-sbc-finite-etale-adic-pushforward-coordinates: the existing node is a quasi-coherent structure-sheaf coordinate comparison under ring-quotient transitions, not rational Weil cohomology.

lem-a1-finite-etale-weil-fibre-comparison vs sk-lem-curve-finite-support: the existing node concerns classical finite-support curve sheaves and ordinary cohomology; the new node has rational/common-stage Weil operators and arbitrary finite-type targets.

lem-a1-finite-etale-weil-fibre-comparison vs sk-lem-geo-finite-boundary: the existing statement concerns detection by a proper direct image, with its ordinary/finite-coefficient hypotheses; it does not identify the rational Weil stalk with residue-field fibre cohomology and match both local Frobenius operators.

lem-a1-finite-etale-weil-fibre-comparison vs sk-lem-pbc-finite: the existing node gives ordinary abelian-etale exactness and constant-ring derived exchange; the new node concerns rational/common-stage Weil sheaves and identifies two normalized Frobenius operators.

