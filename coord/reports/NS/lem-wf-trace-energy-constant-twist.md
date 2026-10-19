# Stage 1 report: lem-wf-trace-energy-constant-twist

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-wf-trace-energy-constant-twist.json`: statement, split into four explicit elementary steps using existing nodes; no whole-item Mathlib match.
- `citations.json`: verbatim statement excerpts for all seven dependency citations (two in step 1, four in step 2, one in step 4).
- `report.md`: this report. `searches.jsonl` is the search command's log; `write_split.py` is sandbox-only preparation material.

Zero new nodes; zero new Mathlib leaves. The item statement and its original search records and provenance are retained. Added the tensor-product definition to `stmt_deps`, since the statement itself uses tensor. The chapter and unit records are unchanged: this support lemma is not their key node.

## Attachments

None for this item. Read `AlgebraicGeometry.WeilSheaf.traceEnergy_constantTwist` at `WeilConjectures/DeligneLaumon/AffineLine/TraceEnergy.lean:422–426`: its proof is `sorry`. Searches of WeilConjectures by item tag and trace/twist names gave no other whole-item declaration. The closed `nonempty_equiv_stalkAt_constantTwist` and `nonempty_equiv_stalk_constantTwist` in `StalkConstantTwist.lean:130–150` concern the pointwise operator only, not the whole energy identity; they were read as construction cross-checks and are not claimed as attachments.

## WANTED

None. The source for this support identity is the available current blueprint; its proof is accordingly marked agent-origin.

## Findings and corrections

The item was statement-only and is mathematically correct as written. Its source is current-blueprint `lem-wf-l2-purity-rigidity.proof.md`, Step 1. That paragraph speaks first of a closed point of degree m and then of the whole energy at level m. A rational point at level m need not have closed-point degree m. The split spells out the m-fold Weil recurrence directly at each rational point, avoiding this imprecise shortcut without changing the statement, normalization, or proof route.

The existing Lean candidate covers an identity written as division by q^(mw) and allows all natural m, using a finitely supported sum convention with junk value on infinite point sets. The item restricts to finite type and m>=1 and writes multiplication by q^(-mw); these are consistent on its domain, but the candidate remains sorried. No Lean or build commands were run.

I searched the whole DAG and blueprint for constant twist, twist, and trace energy and inspected the relevant existing definitions. `lem-wf-conjugate-tensor-traces` does not duplicate this result: it needs a lisse sheaf on a smooth connected affine curve and concerns conjugation and an L-function. `lem-wf-constant-twist-weight` concerns purity rather than trace energy. Neither is used. No nontrivial lemma was moved into a new node, and scalar trace scaling is explicitly obtained from the matrix diagonal rather than introducing an unnecessary Mathlib leaf.

Fresh search commands used LeanFinder, Loogle, LeanSearch, and Mathlib grep, with a second semantic phrasing and a second grep. Their hits were read. LinearMap.trace_tensorProduct/trace_tensorProduct' and Matrix.trace_smul express the ordinary linear-algebra fragment; finite-field trace and Gauss-sum results do not state the sheaf identity. All new search records are copied from the command's actual queries and returned names; original item records are preserved as inherited records, not represented as searches newly performed here.

## Unfinished work

None within the assigned one-level split. There are no new unsplit nodes.

## Review by NS

I read the chapter and energy unit, the current blueprint's Step 1 in the rigidity proof, the current constant-twist and tensor-product definitions, and every statement cited by the four proof steps. I also read the source implementation of constantTwist (Tensor.lean:80–89), its rational-point stalk equivalence, the energy definition (TraceEnergy.lean:85–93), and finite_fieldPoints (PointCount.lean:211–216). These confirm the geometric Frobenius convention and that the energy sums range over rational points rather than only closed points of exact degree m. No SGA route is involved.

Step 1 uses precisely the rank-one scalar character in `def-wf-constant-weil-twist` and the displayed tensor Weil map in `def-wf-tensor-product`. I checked its tensor-unit identification explicitly on v tensor c and its inverse on v; it requires no comparison between two different coefficient categories or a fundamental representation of a nonlisse sheaf. The geometric line is the coefficient unit, so the tensor-unit computation gives the same underlying sheaf with Weil map b theta. This is a unit calculation, not a claim that an arbitrary constructible sheaf is a fundamental-group representation. In particular the argument does not require geometric connectedness. The completed tensor unit and its rationalization use that same unit, rather than an ordinary discrete Qlbar-sheaf replacement.

Step 2 uses the iterated Weil-map recurrence and the actual rational-point return operator of `def-weil-local-frobenius-trace`. I checked the induction at m=1 and m+1. The scalar is b^(m+1) because pullback is linear over the coefficient field; the Frobenius acts on the geometric base, not by a field automorphism on coefficients. The formula Lf_E^*(u tensor c)=Lf^*(u) tensor c in `def-weil-derived-pullback-tensor-hom` supplies exactly this linearity. `def-weil-finite-coefficient-point` gives the linear fiber functor, rationalized and taken at a common finite stage, so applying it preserves the scalar. This avoids asserting a tensor-stalk comparison not supplied by a cited statement. Finally `def-weil-endomorphism-trace` defines trace as the diagonal sum, which is all the matrix computation takes from it. The stalk is finite dimensional since this is a constructible heart sheaf. Enlarging the coefficient stage to contain b is legitimate since b is algebraic over Ql; the definitions cited in this step explicitly use common finite stages at Qlbar. No finite-stage category is silently identified with another coefficient model.

Step 3 uses no additional theorem: multiplicativity of complex absolute value and the definition of positive real powers prove the displayed identities. I checked the sign and the factor two: 2m(-w/2)=-mw. Here q>=2 by the finite-field datum, so log q exists and real powers have the displayed exponential expression. No purity, semisimplicity, or positivity of w is assumed.

Step 4 takes only clause (1) of `lem-weil-point-counts-finite`, whose hypotheses are a finite-type scheme over the finite base field and a finite extension. Both hypotheses hold here, and the node is already Lean-closed. It gives exactly the finiteness needed to distribute the scalar over a finite sum. It supplies no unstated estimate or cohomological theorem.

For small cases I checked the zero sheaf and empty scheme (both energies zero), b=1 and w=0 (identity), X_0=Spec(k_0) with a rank-one Frobenius scalar a (energies |iota(a)|^(2m) and |iota(ab)|^(2m)), m=1, a rational point whose closed degree properly divides m (the recurrence still contributes b^m), a rank-two Jordan block (diagonal trace calculation unchanged), negative w, and nonconnected X_0. The tensor-unit and scalar calculations require neither lissity of F nor diagonalizability. Every step is less than 2000 characters, and each displayed intermediate claim is explicitly proved in its step. No step hides a separate non-elementary comparison lemma. I checked delivery-errors B through E: self-contained item, ordinary TeX, no new statement-only nodes to audit, no false attachment, exact citation scope, no relabeling, no missing hypotheses, and no change of route. Every citation excerpt in citations.json was checked as a literal substring of the opened node's statement.

The first dry run required a longer excerpt for the coefficient-linearity citation; I replaced that excerpt with the full introductory sentence and displayed morphism formulas from the same statement. The mathematical step is unchanged.
