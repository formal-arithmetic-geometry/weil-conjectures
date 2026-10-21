# Q41: lem-sf-semilinear-scalar-derived-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-sf-semilinear-scalar-derived-comparison.json`: statement, split into six proof steps; not a Mathlib leaf. The statement is unchanged. No new nodes; no new Mathlib leaves.
- `citations.json`: seventeen step/node entries with verbatim statements. Full statements are quoted where a step needs several clauses, so the evaluation, unit/counit and intrinsic-alpha assertions remain visible together.
- `report.md`: this report. `prepare.py` is sandbox-only preparation material, not a node or repository change. `searches.jsonl` is the search command's unmodified log.

## Attachments

None. Searched the whole project `lean/WeilConjectures/` for the exact item and blueprint tag, semilinearity, scalar comparisons and restriction. Read `SixFunctors/BaseChange/RestrictScalars.lean` and `SixFunctors/ProEtale/FiniteCoefficient/Derived/RestrictScalarsLowerStar.lean`. The former concerns ordinary fixed-coefficient etale comparisons; the latter supplies bounded-below single-ring pro-etale direct-image comparisons. Neither states the arbitrary semilinear-system, unbounded derived, open-mate and intrinsic-alpha assertion. No sorry declaration was counted as a finished proof.

## WANTED

None required for this split. The ancestor and unit records refer to main-20261017 paths absent from this read clone; I read their current DAG records and the available main-20261015 `sk-thm-sf-package/fix-prop-coherence.md` and `.proof.md`. The latter contains the exact sentence about coefficient comparisons of adjunction units and counits that this item makes precise. This is an agent-written assembly, not a theorem claimed verbatim from Stacks.

## What was wrong or incomplete

The item was statement-only, with five earlier Mathlib search records inherited from its creator. Those records were preserved. Seven searches actually run for this delivery were appended from the command's log, including a second semantic phrasing. The hits were read: ordinary sheaf restriction and pullback/pushforward adjunctions, exact-functor derived localization, and derived-unit/counit factorization. They do not state the complete system comparison theorem. Mathlib does supply individual tools already represented by existing DAG nodes.

There is no statement dispute and no route change. The source line naming 03D7 is a foundation for ordinary ringed-topos adjunctions, not a quotation of the derived-system assertion. The proof therefore explicitly uses existing stronger comparison/evaluation nodes and is marked agent-written. In particular the proof does not infer invertibility of a mate merely from invertibility of its original square, does not assume scalar restriction preserves K-injective systems, and does not infer equality of derived morphisms from level evaluations.

## What could not be finished

Nothing within this one-level stage-1 split. No Lean was written or compiled. Existing construction/comparison nodes remain obligations in the DAG; this delivery proves the assembly from their stated conclusions and creates no substitute for them.

## Not duplicates

No new node was created. Searched the whole imported blueprint with `blueprint_refs.py search` for scalar restriction, restriction of scalars and invertible mates, and searched DAG text for scalar derived comparisons, constant towers and semilinear restriction. Ordinary comparisons, single-level ring change and simultaneous derived sections already have nodes and are cited directly. The blueprint coefficient-change nodes for condensed-module objects have different categories and some impose flatness; they are not identified with this arbitrary ring-system statement. The nearest blueprint ancestor is `fix-prop-coherence`, as confirmed by `blueprint_refs.py ancestor`; the item's existing provenance and `same_as: []` are retained.

## Review by Q41

I read delivery-errors B through E in both the current and inherited sections and checked the six steps against the statements actually cited. Sources opened were Stacks `sites-modules.tex`, Tag 03D7, label `lemma-adjoint-pullback-pushforward-modules`, including its proof; `sites-cohomology.tex`, Tags 0D6D (`lemma-derived-pullback-composition`), 0D6E (`lemma-derived-pushforward-composition`) and 07A6 (`lemma-adjoint`), including their proofs; and `categories.tex`, Tag 04VG (`lemma-properties-left-localization`). I also read Mathlib's `Localization/Predicate.lean` for the natural-transformation lifting and uniqueness that 04VG itself does not state. I read the available blueprint ancestor proof and current chapter/unit records. No prohibited SGA source is used. There are no new-node sources to audit.

Step 1 uses the ordinary comparison's exact sectionwise restriction, the simultaneous-section theorem's exact inverse image, and the localization node's unique lifting of transformations and inverse transformations. Exactness ensures the functors invert quasi-isomorphisms after the derived quotient. The evaluated restriction is identified on complexes, not by claiming evaluation is faithful. Its pullback comparison is the localization of the actual ordinary comparison.

Step 2 uses the mate definition for the displayed composite, and the simultaneous-section statement for evaluated geometric adjunctions, units, counits and transposes. It applies that statement twice, once to C_n and once to the constant sequence B. The tower statement specifies the same constant-B geometric adjunction. I wrote out the evaluated unit--inverse-comparison--counit word, which prevents replacing the specified mate by an unspecified isomorphism.

Step 3 uses the ring-sheaf-change statement itself, including its exact adjunct equation and invertibility. Its assumptions require invertible inverse-image identifications of both ring sheaves, not flatness of B to C_n. The constant-ring identification supplied by the tower statement works with B and separately with C_n; compatibility follows on constant sections from the given homomorphism. Substituting the geometric counit into the cited adjunct equation and using its identity adjunct identifies the normalized ring-change comparison with step 2's word. This works for every n without finite coefficients or boundedness.

Step 4 uses precisely joint detection of isomorphisms in the simultaneous-section theorem. Its constant ring specialization gives the ordinary strict B tower category, since all scalar-transition restrictions are identities. Every component of d is invertible by step 3, so d is invertible. This is detection of isomorphisms, which the cited statement asserts, and not detection of equality, which it expressly avoids.

Step 5 uses ordinary open-unit normalization from the ordinary comparison, exact open adjunctions from simultaneous sections, and localization of transformations and their equations. I checked the direction: the left mate runs from J^T rho_U to rho_X J, hence is a^{-1}. The proof writes its unit--b--counit formula and identifies it by the ordinary open Hom bijection before localizing. This does not assert that arbitrary mates preserve invertibility.

Step 6 uses the ordinary statement's explicit preservation of beta, the clopen projector and their full intrinsic-alpha composite; the varying-ring-arrow statement that this exact ordinary transformation is localized; the strict-tower statement's intrinsic-alpha formula; and localization's preservation of composition and equality. I checked the displayed equation has source rho_V P_p J_i and target J_k^T G_r rho_W. The correct vertices are U,V,W,Z as in the item. The hypotheses are proper vertical maps and quasi-compact open horizontal maps; no cartesian hypothesis is introduced. The equation precedes proper mating and so does not rely on the parent theorem this item is intended to support.

For small cases I checked B=C_n with identity transition maps (all comparisons become identities), the zero ring and zero complex, identity f (the mate reduces by the adjunction triangle), identity and empty open immersions, and the clopen projector when s is identity (cartesian case) or has empty image (zero map). None requires coefficient flatness; in particular B=Z and C_n=Z/2^n passes the coefficient hypotheses without any flatness claim. Noncartesian squares still use the same clopen construction already stated by the cited nodes. Arbitrary unbounded complexes and noncartesian systems are allowed throughout; no normalized-system right adjoint is invoked.

The largest proof step has 1176 characters; none exceeds 2000 or hides an additional comparison lemma. All non-elementary input facts are existing cited nodes, not new versions of clauses of this item. Every citation quote was checked as a literal substring of the cited node's statement. The only declared off-unit tools are simultaneous-system evaluation, constant-tower normalization and single-level ring change; they supply generic comparisons rather than replacing the compatibility unit's route. I retained the item's source, provenance and all other maintainer fields.
