# Stage-1 direct delivery: lem-sf-constructible-exceptional-coefficient-construction

## Files written

- dag/nodes/sec-six-functors/lem-sf-constructible-exceptional-coefficient-construction.json — statement, split into 22 argument steps using existing nodes; Mathlib searches found no matching construction.
- citations.json — every step/node pair, quoting its cited statement verbatim.
- report.md — this report. No new nodes or Mathlib leaves.

## Attachments

None. The exact `WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_construction` in `lean/Sheaf/Paper/ConstructibleExceptionalCoefficientConstruction.lean` ends with `sorry`. Searching `lean/WeilConjectures/` for the blueprint tag, declaration/record name and exceptional-constructible terminology found related finite functors, not a proof of the full normalized family. The record definition and all four dependent record fields were read, as was the imported Data module.

## WANTED

None. The current blueprint, Zheng PDF and Stacks sources used here are available locally.

## Statement and imported-proof repair

STATEMENT-DISPUTED: the imported statement was only a Lean theorem signature with the enclosing section omitted. In particular `l`, its prime instance, `Ω`, the field/algebra/algebraic-closure instances, and the meaning of `CoefficientConstruction` were unbound in that text. Reading the actual Lean section supplies exactly this missing context. The delivered statement restores it and spells out the precise record fields. The theorem itself and its conclusion have not been weakened: it still constructs the four dependent records over the same finite-type, relatively separated morphism; there is no absolute separatedness hypothesis.

The inherited one-step proof was an assertion that data were constructed elsewhere, with empty uses and a large unrelated union of proof dependencies. Replaced it with the construction itself. It would be circular to cite the larger assembly node `lem-sf-constructible-exceptional-adjunction-coefficients`, since this construction is now a premise of that assembly; the new proof cites its lower existing inputs directly. No Lean was written or compiled.

## Not duplicates

No new node was created. Searches across the whole DAG and `tools/blueprint_refs.py search` for coefficient construction, exceptional adjunction and exceptional terminology were read. The existing assembly statement has more coherence conclusions and depends on this item; it is not an acyclic black box. Existing finite-scalar mate and finite-free compact-composition nodes that require absolutely separated X,Y were inspected but are not used. The general system-realization theorem and integral shift-realization theorem have the needed hypotheses and were reused.

## Review by N0

I read the current main-20261015 exceptional inverse-image paragraph, the six-functors chapter and compatibility unit records, and the exact Lean construction record (ring, fields, common, refinements). I read Zheng's proof of Proposition 2.23 (the Brown branch), statements and proofs of 2.29 and 3.16, and Constructions 5.14–5.16, Lemma 5.22 with its derivation from 5.13/(5.16.2), and Proposition 5.24. This proof is an agent synthesis of these sources and the cited existing statements, and is marked as such. No SGA document or SGA trace route is used. Smooth-purity preservation is an already stated prerequisite through the blueprint lecture-notes route, not rederived from a forbidden source.

I opened every cited node's statement and checked what the corresponding step takes from it; citations.json preserves those statements for independent review. The construction uses only already existing inputs, so there are no new-node source claims to review.

1. Finite compact supports: finite-type-over-Noetherian and dimension finiteness apply to the middle scheme of each compactification. Open extension preserves the interval, and direct-image ctf gives the enlarged interval for the proper part. The two derived-functor nodes give actual triangulated structures.

2. Finite right adjoint: the ordinary etale adjoint is transported using the class-restricted Hom theorem, not an ambient pro-etale adjoint. Constructible origin supplies the left-input hypothesis; the preservation corollary states bounds for exactly the specified composite. Natural Hom bijections give triangles.

3. Finite shifts/exactness: the finite-ctf node supplies the triangulated categories; unique adjoint shifts supply both unit and counit compatibility, satisfying every hypothesis of the right-adjoint exactness node. The additivity argument is stated explicitly.

4. Finite scalars: the flat-model node includes a bounded constructible etale model on Noetherian schemes. The step proves flatness and constructibility after coefficient change on that model, then uses derived change of rings for maps and exactness. Tor comparison and constructible origin say exactly how to return to the pro-etale category. No quotient is assumed flat.

5. Finite left comparison: etale compact-scalar coherence specifies the proper/open map and proves it invertible without flatness. Derived pushforward composition applies to the coefficient identity-topos morphisms, and the scalar-adjunction node specifies the unit map. This fixes the ambient normalization.

6. Finite right comparison: the cited scalar adjunction and etale exceptional adjunction justify each term of the displayed Hom chain. Yoneda is the actual Hom-evaluation lemma, not only a full-faithfulness slogan. Constant-tensor states invertibility for arbitrary constant coefficient complexes. Restriction conservativity is proved from its unchanged underlying cohomology.

7. Site and shift transport: constructible origin and Tor comparison have both directions needed here. The compact-support comparison identifies the selected left functor. The direct-image comparison states the canonical mate and its counit equation, and open comparison identifies extension by zero. Tensor/pullback and projection-mate nodes supply the named tensor/shift comparisons; the adjoint-shift and whiskering nodes supply the remaining shift equations.

8. Strict etale systems: the system-adjoint node explicitly states evaluation of the right adjoint, its units/counits and transitions, uniform lower bounds and preservation of normalization. This is the required stronger statement; evaluation of the left adjoint alone would not suffice. The finite-type schemes meet its hypotheses without absolute separatedness.

9. Strict site comparison: the comparison node states an actual system adjunction with evaluations, normalization and bounded-below counit. Joint conservativity is explicitly in the left-extension node, and finite comparison gives the unit. Pushforward composition is for arbitrary small ringed sites, including diagram sites. The system Hom chain uses actual maps before evaluation.

10. Reduction/limit: evaluation-calculus states the exact reduction unit and total-limit counit. The completed-scalar theorem at E=L identifies this unit with completeness. DVR effectivity proves this specified counit invertible on normalized towers without an extra constructibility assumption; finiteness is imposed separately through the two category definitions.

11. Integral adjunction: coefficient-system normalization and finite uniform bounds apply to both outputs. The compact-support lemma supplies the canonical reductions and Tor bounds of the prescribed left functor. The integral-ctf triangulation node is used, rather than only triangulation of all integral constructibles. Total limit exactness and the adjoint shift result give exact operation records.

12. Integral left normalizations: the system-realization theorem covers the single proper/open word on finite-type schemes with common normalized bounds, all verified in earlier steps. It compares actual generator maps. Choosing the realization through the published tower functor yields the record equation, not an arbitrary isomorphism. The integral shift-realization theorem supplies the precise Roos-cone shift compatibility.

13. Integral reduction: evaluation-calculus and the system-adjoint theorem give simultaneous adjunction equations and reduction maps. The system-realization theorem identifies their left proper/open map with the ambient one, and shift-realization handles its named shifts. I checked that no equality is deduced merely from equal finite evaluations.

14. Ramified subsequences: system-adjoint explicitly allows B_n=R_L/varpi_E^n and states agreement with the en subsequence. The left-extension node gives the missing levels and their actual transition maps. Its evaluation counit is invertible on normalized systems, so conservativity proves the equivalence on these domains.

15. Completed integral scalars: finite-free completed-scalar comparison gives exactly chi, in the direction required by integralScalar_normalized. Constructibility and the separate adic Tor-bound node prove the restricted functor has the desired domain. Ringed-system proper/open maps and the system realization identify the left mate; the shift-realization theorem is cited separately.

16. Allowed composites and identities: successive-derived-scalar normalization states the explicit balanced map and compatibility with scalar units; its specializations give the record scalar associators. The ringed coefficient projection cocycle holds for actual system maps and arbitrary structural ring maps. Open tensor normalization supplies the open factor; mate pasting and whiskering provide the rest. The text writes the counit substitution argument.

17. Rational operations: residue-Tor proves every integral representative belongs to the finite-Tor domain. The definition is raw localization with the same objects, and linear localization states exactness. Localizing inverse linear Hom maps proves the adjunction without any idempotent completion.

18. Rational comparisons: the raw object/morphism formulas show that the specified q maps are exactly localizations of the integral maps. Scalar-extension exactness supplies endpoint structures. The counit equations are localized equations; naturality on fractions is explained, not assumed.

19. Common stages: the common-stage definition specifies represented morphisms, equality after larger fields, and triangles over a finite field. Left transition identities from tensor/mate normalization give the right identities by injectivity of transposes. Thus the Hom colimit and maps are well defined. Common q is literally the identity on represented objects, as the record requires.

20. Refinement left maps: the finite compactification theorem supplies invertible comparisons. The proper/open definition specifies their open-unit normalization. The system-realization theorem states that these actual maps intertwine with integral generator maps before limit, and shift-realization states their shift compatibility. Its hypotheses allow the nonseparated bases in the item.

21. Refinement right maps: natural-bijection transposition and unique-right-adjoint state the exact counit normalization. The two explicit transpose calculations prove the unit and inverse identities. Adjoint shifts, raw localization and common stages preserve precisely these maps, giving both field-stage normalization fields.

22. Assembly and edge cases: all four records use the same operation/scalar choices. Empty X gives zero functors on X; empty Y forces empty X, so no maximum or Krull dimension of an empty scheme is used. Positive levels, identity morphisms, nonflat quotients, and ramified en levels were checked. No step exceeds 2000 characters after the shift additions; there is no long unreviewed hidden lemma.

The off-unit citations are generic tools for the already fixed construction route. They are declared in split_report.tool_uses for the maintainer to judge; the maintainer-owned tool_uses field was preserved. No chapter or unit record was changed.

## Unfinished work

None within this one-level stage-1 split. Lower prerequisite proofs remain their existing DAG obligations. No claim of a completed Lean proof is made.
