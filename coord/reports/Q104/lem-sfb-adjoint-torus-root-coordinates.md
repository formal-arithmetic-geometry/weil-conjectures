# Q104: lem-sfb-adjoint-torus-root-coordinates

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-adjoint-torus-root-coordinates.json`: retained the imported statement and added a four-step proof, with the existing diagonalizable-character quotient theorem and two new arbitrary-base structural inputs.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-self-centralizer-arbitrary-base.json`: new statement-only node; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-adjoint-action-kernel-is-centre.json`: new statement-only node; no Mathlib match.
- `citations.json`: eight verbatim statement quotations covering every cited node in every proof step.
- `report.md`: this report.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, its blueprint tag, adjoint-torus terminology, root-character terminology, and centre/centralizer declarations. No sorry-free declaration states the item. The nearby Lean and DAG declarations are either definitions, field-only centralizer results, or Noetherian relative results and do not state this arbitrary-base item exactly.

## Literature wanted

WANTED: `literature/conrad-reductive-group-schemes.pdf`, Brian Conrad, *Reductive Group Schemes*, Theorem 3.3.4, Corollary 3.3.6(1), Proposition 3.3.8, Example 5.1.7, and the proof of Corollary 6.1.15. I read the cited pages online at the source URL recorded in the nodes; the project has no local copy.

## Corrections and blueprint comparison

The imported item had no proof and carried an inherited `blueprint.from.node = null`; `python3 tools/blueprint_refs.py ancestor lem-sfb-adjoint-torus-root-coordinates` returns `None`, so I retained that ancestor result and replaced the nonspecific inherited place with the exact Conrad supporting-input place. The statement itself is unchanged. The prior imported `created` provenance is retained as history. Whole-blueprint searches for “split torus centralizer”, “adjoint torus root lattice”, and “root lattice quotient center” returned no equivalent blueprint node.

The two new nodes are not relabellings of the item. `lem-sfb-split-torus-self-centralizer-arbitrary-base` isolates the centralizer equality needed to put a central section inside the torus. `lem-sfb-adjoint-action-kernel-is-centre` isolates Conrad’s centre-as-adjoint-kernel input. The existing `lem-sfb-relative-reductive-centre-weight-kernel` has the same general theme but assumes a nonzero Noetherian base and includes a different relative weight-kernel construction; the new statements allow every commutative base ring. The existing `lem-sfb-reductive-torus-self-centralizer` is field-only, and `lem-sfb-reductive-centre-root-quotient` is algebraically-closed-field-only. These differences are recorded here rather than silently treating them as duplicates.

## Not duplicates

- `lem-sfb-split-torus-self-centralizer-arbitrary-base` vs `lem-sfb-relative-reductive-centre-weight-kernel`: the new statement is the arbitrary-base self-centralizer theorem; the existing statement assumes a nonzero Noetherian base and proves a larger centre/weight-kernel theorem.
- `lem-sfb-split-torus-self-centralizer-arbitrary-base` vs `lem-sfb-reductive-torus-self-centralizer`: the new statement is for split reductive groups over arbitrary commutative rings; the existing one is for maximal tori over fields.
- `lem-sfb-adjoint-action-kernel-is-centre` vs `lem-sfb-relative-reductive-centre-weight-kernel`: the new statement identifies the full adjoint-action kernel over arbitrary bases; the existing statement is Noetherian and formulated through relative tangent weights.
- `lem-sfb-adjoint-action-kernel-is-centre` vs `lem-sfb-reductive-centre-root-quotient`: the new statement is arbitrary-base and functorial under base change; the existing statement is algebraically closed field only.

## Review by Q104

I read the current item, the chapter record `dag/chapters/sec-six-functors-basics.json`, and the unit record `dag/units/sk-thm-sf-ctf-stability.json`. The unit metadata is inherited and does not supply a separate root-data route; the item’s own source place is Conrad’s root-lattice/adjoint-torus input used in the isomorphism theorem. I also read the full statements of `def-sfb-pinned-split-root-realization`, `def-sfb-ring-diagonalizable-group`, `lem-sfb-relative-diagonalizable-character-duality`, and the two new nodes.

For step 1, Conrad Theorem 3.3.4 and Corollary 3.3.6(1) give the scheme-theoretic self-centrality of a maximal torus over an arbitrary nonempty base, while Proposition 3.3.8 identifies the centre with the adjoint-action kernel. The two new node statements say exactly the parts used: a central section lies in `T`, and inside `T` centrality is equivalent to trivial restricted conjugation on the Lie module. Their base-change clauses justify applying the argument to every `A`-algebra `B`; no reducedness or connectedness is smuggled in.

For step 2, I checked the pinned-realization definition itself. It gives the direct sum of `Lie(T)` and the free rank-one root lines and defines the full character weight equation, not merely a differential character. The torus summand is fixed by commutativity, and a scalar acts identically on a free rank-one line exactly when its scalar is one. This proves the common-kernel calculation over nonreduced coefficient rings and also handles an empty root set.

For step 3, I checked `lem-sfb-relative-diagonalizable-character-duality`: its statement explicitly says that the quotient of `D_A(M)` by `D_A(M/L)` is `D_A(L)`, identifies the corresponding common character kernel, and gives arbitrary-base-change compatibility. Applying it to `L=Q=\mathbf Z\Phi`, together with steps 1–2, gives `Z(G)=D_A(M/Q)` and `T/Z(G)=D_A(Q)`. The finite root set and the subgroup `Q` are already introduced by the item statement.

For step 4, I checked the conjugation and weight clauses in `def-sfb-pinned-split-root-realization`, the quotient/fppf-local clause in `lem-sfb-relative-diagonalizable-character-duality`, and the centre/base-change clause in the adjoint-kernel node. Centrality makes conjugation constant on `Z(G)`-cosets, so it descends through the fppf quotient. The same defining weight equation gives multiplication by the character value on each root line, fixes `T_B`, and preserves labels. The construction is compatible with further base change by the cited quotient and kernel statements.

I checked the edge cases `Q=0`, empty `\Phi`, rank-zero `M`, disconnected `A`, and nonreduced test algebras. In the empty-root case the quotient is the trivial torus and the action is trivial; in rank zero all groups and lattices reduce to the stated identity cases. No step assumes that `A` is a domain, reduced, connected, Noetherian, or a field. The Mathlib searches were run for the item and for both new nodes with LeanFinder, Loogle, grep, and LeanSearch; all returned only generic root-pairing, Lie-algebra, or group-centralizer facts, so both new nodes are correctly marked unsplit with no Mathlib match. `srvcheck.py ... check_dag` passed.

## Unfinished work

None in this one-level stage-1 split. No Lean source was written and no compiler, Lake, or build command was run.
