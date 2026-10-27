## Files written

- `dag/nodes/sec-trace-formula/lem-trf-facet-lattice-supported-coordinate-cover.json`: statement, split; Mathlib searches find no exact theorem or one-line specialization for the whole item. The statement is unchanged. Six proof steps reuse existing nodes; no new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every dependency cited by every step.
- `report.md`: this report. The search command maintains `searches.jsonl`.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, the id, facet, orthant, lattice support, supported series and coefficient embedding. No declaration there states the item. General power-series and quotient constructions only cover parts; they do not justify ATTACH.

## Wanted sources

WANTED: K. Kato, *Toric singularities* (1994), the sharp saturated monoid/facet and completed toric local algebra underlying ILO VI 1.6, for lem-trf-facet-lattice-supported-coordinate-cover. The existing DAG sources already record this request. I did not download a source or attribute a theorem to unread Kato. The proof is explicitly by agent, assembled from existing statements. No SGA source is used.

## Findings and changes

The original item was statement-only and had no proof or proof dependencies. Its mathematical statement passes the checks below; no STATEMENT-DISPUTED correction was needed. Its normal-domain hypothesis and the congruence on the Cohen parameter are retained even though this particular splitting argument does not need them. Those hypotheses remain relevant to other lemmas about the same model.

The whole-DAG keyword search found `lem-trf-sharp-cone-primitive-facet-preparation` and `lem-trf-completed-monoid-support-projection`, which already state the two substantial inputs. In particular the weaker orthant embedding lemma would give some lattice embedding, whereas this item needs exactly the primitive facet vector: I used the preparation lemma instead. No duplicate auxiliary nodes were made. The completion theorem was applied in r+n coordinates with subgroup M x Z^n, not merely M; this explicitly accounts for the t variables and avoids an unsupported iterated-completion identification. The quotient argument is written out using linearity, without assuming the projection is multiplicative.

Read the newest blueprint at `literature/blueprint/latest` (COMMITS main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345), including the trace-formula chapter, sk-i-curve-zero unit and lem-trf-local-term-locality proof. The unit now follows contracting correspondences. This item is an existing historical nearby-duality/alteration auxiliary branch recorded in its unchanged ancestry; it does not alter or claim to realize the current unit itself. Whole-blueprint searches for facet, monoid, lattice, completion, supported and lattice supported found no equivalent blueprint statement. The nearest ancestor remains lem-trf-local-term-locality and same_as remains empty. No chapter/unit file was changed.

Fresh required searches were run through msearch.py: leanfinder twice (facet/orthant and completed-monoid/coefficient formulations), leansearch, loogle, and grep twice. Their exact query texts and hits are recorded in the item and searches.jsonl, alongside the preserved inherited search records. All services answered. The grep facet hits concern simplicial complexes, read at Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean:176. Read Ideal.algebraMap_quotient_injective at Mathlib/RingTheory/Ideal/Quotient/Operations.lean:756 and HahnSeries.toMvPowerSeries at Mathlib/RingTheory/HahnSeries/PowerSeries.lean:153: the former assumes the contracted ideal as its quotient ideal, and the latter only converts Hahn series; neither supplies the full item. No Mathlib leaf is warranted.

## Not duplicates

No new nodes. The existing facet preparation, lattice-intersection, orthant-embedding, completion-coefficient-embedding, completed-support-projection and lattice-support-retraction nodes were read instead of recreating their statements.

## Review by Q145

I read ILO Expose VI 1.4 and 1.6(i)--(ii), printed pp. 69--70 (PDF pages 75--76). These give the log-regular context and exactly the equal-characteristic and Cohen-ring model presentations in the item. They do not assert the supported-coordinate-cover theorem, so both the item and its proof identify the auxiliary algebra as agent-written. There are no new nodes needing separate source validation. I read sections B through E of delivery-errors.md, including its repeated historical copy, and checked the actual proof against the specific failure cases.

Step 1 uses the complete statement of `lem-trf-sharp-cone-primitive-facet-preparation`: finite facets, free lattice embedding, pointed cone, lattice intersection, primitive normals and half-space description are all expressly there, under precisely fs+sharp hypotheses. `def-trf-sharp-monoid-facet-forms` expressly identifies the codimension-one facet forms with these normals. This comparison uses no hidden assertion of normality of the completed ring and no proof-internal witnesses from the cited node.

Step 2 uses those stated half-space and pointedness assertions: a vector with every valuation zero and its negative both satisfy the inequalities, hence are zero. Nonnegative facet values similarly characterize sigma intersect G. This is a short elementary argument, and it proves the kernel and image clauses for the actual facet vector.

Step 3 uses the group-completion presentation in `def-trf-fs-log-blowup`. Finite monoid generators generate G by differences. A primitive normal is surjective and hence not zero; if it vanished on every chosen generator it would vanish on G. The sum of all generators therefore has positive value at every facet. This is an elementary sum of nonnegative integers, with no separate positivity lemma hidden in the step.

Step 4 invokes `lem-trf-completed-monoid-support-projection`, whose statement gives the continuous injective extension, its exact supported image, the coefficient projection, linearity and the retraction identity. I checked each hypothesis: Q' is (M x Z^n) intersect N^(r+n); it is finitely generated because it is isomorphic to P x N^n; L is complete local with finitely generated maximal ideal. For a field the maximal ideal is zero; for a Cohen ring the definition node explicitly gives maximal ideal (p) and completeness. The monomial isomorphism and the equality of completion ideals are spelled out before passing to compatible quotient sequences; this supplies the required B rather than a differently completed ring. No appeal to completion commuting with another operation is left implicit.

Step 5 takes only the stated B-linearity and retraction identity from the same node. For b=Theta*a the equality b=theta*rho(a) proves the contracted ideal; conversely theta multiples map into Theta multiples. A difference Theta*h maps to theta*rho(h), proving well-definedness on cosets. The displayed scalar formula proves R-linearity and the identity on R. This does not require rho to preserve products of arbitrary elements, nor that theta or Theta be a nonzerodivisor. It is a direct quotient calculation and is elementary.

Step 6 uses the precise coefficient projection in the same statement, and the preparation lemma's explicit zero-group case. I checked P={0}, r=0, n=0 separately: the support is all of N^n and rho is the identity; if n is also zero, B=A=L (L is complete), and the Cohen quotient is L/(theta) on both sides. There is no positive-vector requirement for P={0}. For P=N, nu is the identity; for P=N^2 the facet map is the coordinate map. For a singular example P={(a,b) in N^2: a+b even}, with G the parity sublattice, projection deletes odd-parity monomials; multiplying by a supported series preserves parity cosets, and the same quotient calculation works for theta=p-X_1 X_2. These tests guard against accidentally using multiplicativity of the projection. Normality is never inferred from a definition or from these examples.

All proof dependencies are exactly the union of uses and all citations are verbatim from node statements. Every non-elementary fact has an existing cited node; every elementary step has its actual few-line argument. No new node is an elementary fact, duplicate, clause restatement, or missed Mathlib leaf because no new nodes are introduced. Every step is under 2000 characters; step 4 is an application with its hypotheses explicitly verified, and contains no separate comparison theorem disguised as a long step. Nothing relies on a source with omitted details or on unproved project Lean. Only the sandbox was written; no Lean, compiler, Lake, repository git, or local validation scripts were run.

## Unfinished work

None in the stage-1 mathematical split. Server dry-run and delivery results are recorded below when available.
