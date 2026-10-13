## What changed

Replaced the sole sorry in Sheaf.RingTheory.PopescuLiftPartialChart, namely
Algebra.PopescuLiftPresentation.partial_chart_fibre_dimension, with a complete Lean
reduction to one algebra calculation. Existing signatures and definitions are unchanged.
Added the proof-only import Sheaf.RingTheory.PopescuPartialChartPolynomial, plus the explicit
Mathlib differential tensor-base-change import. The existing
partial_chart_flat proof is unchanged.

The main proof pulls pi and a_k conditions to the finite chart, constructs the residue
field's compatible quotient-base algebra, checks that the fibre prime avoids a_k,
uses the polynomial model, proves smoothness by base change and composition, and
constructs a differential basis of rank n. It transports the basis through the model,
passes to a prime above the fibre point, and applies the already proved smooth-dimension
theorem and its existing Algebra.dimAt_openEmbedding helper, accessed with
proof-only `import all Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension`. The model's equivalence is selected
only inside this proposition proof; no definition chooses data from an unproved existence.

Read Stacks Tag 07CP online, especially the partial D_k presentation and its displayed
polynomial description modulo pi. The local TeX is absent, as the existing node records.
LeanFinder and Loogle found only general differential and localization lemmas.
LeanSearch returned Internal Server Error. Direct Mathlib and project searches found no
partial-chart model: PopescuZeroBaseChartPolynomial is for the full lifting algebra and
requires a coefficient map; it cannot directly supply the partial model.

## Proved and sorry left

Closed the original hole
Algebra.PopescuLiftPresentation.partial_chart_fibre_dimension
(node lem-weil-pbc-popescu-lift-partial-chart-dimension). No sorry remains in the item.

Added one hole: Algebra.popescu_partial_chart_polynomial
(node lem-weil-pbc-popescu-partial-chart-polynomial), in its own module
Sheaf.RingTheory.PopescuPartialChartPolynomial. Its whole proof is exactly `by sorry`.
The remaining theorem asserts an algebra isomorphism after scalar extension killing pi
and localization, without any dimension, smoothness or flatness conclusion. It is the
algebra-elimination step of Tag 07CP, strictly a part of the original argument, not a
renaming of the fibre-dimension assertion. This delivery is a decomposition: one original
hole closed, one new hole added, net zero holes. All rank, smoothness and dimension glue
above that calculation is proved in Lean.

Local compilation of both modules passed. The main module compiled in approximately
23 seconds, below the single-file limit.

## No longer needed

Removed the duplicate private helper dimensionAt_openEmbedding. No existing
import, module or proof-dependency node is pruned. The second reader removed
the first worker's redundant added proof import Mathlib.LinearAlgebra.TensorProduct.Basis;
its declarations are already available through the retained imports. This second reading
also removed Mathlib.RingTheory.Etale.Kaehler after a successful compile without it.
All three original
proof imports are used. The full-chart polynomial-model modules are not imported:
this argument needs only the partial chart, so it adds no dependence on coefficient
comparison between other charts. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery: removed the duplicate private theorem
Algebra.PopescuLiftPresentation.dimensionAt_openEmbedding and used the existing
Algebra.dimAt_openEmbedding directly. The earlier claim that the private theorem
could not be imported was wrong: `import all` exposes it for this proof. The existing
dependency module and all public signatures stay unchanged. Updated the dimension
node's final proof step to name the existing helper.

No statement correction was needed. The original plan's algebra calculation was marked
elementary but requires a quotient/base-change/localization isomorphism with generator
checks; this is now a separately named node. The rest of the original plan has been
made into Lean. The original fibre point and target statement are unchanged.

The new statement was checked on empty E_k (no free auxiliary variables), all auxiliary
variables in E_k (no eliminated variables), m=0, n=0 with Prepared.card_le, and a zero
coefficient algebra. Empty E_k leaves the coefficient algebra with no free auxiliary variables. Zero
coefficient algebras give zero polynomial/localized algebras; no prime is chosen there. The statement assumes no Noetherianity, flatness,
annihilator equality or unprovided coefficient map.

## New nodes

lem-weil-pbc-popescu-partial-chart-polynomial states the partial chart's polynomial
model for any compatible scalar extension killing pi. Its source and proof describe
both substitution maps, their relation checks and their inverse identities. It inherits
sec-proper-base-change and sk-thm-p1, and its blueprint ancestor is the original node's
ancestor with the original node added to the via chain. The existing dimension node's
proof, proof_deps and proof_origin now follow the compiled proof. No interface changes
or change records are required.

## Earlier second reading (a previous round; superseded)

1. Compared the complete item module with the repository version and checked the
   declaration table. Every existing signature, visibility and definition is unchanged;
   only proof text, its explanatory docstring and proof-only imports were added.
   There are no forced adaptations or interface change records. Verdict: pass.
2. Compiled both delivered modules in import order using lcompile.py. The item has
   no sorry; the only delivered sorry is the whole named theorem
   Algebra.popescu_partial_chart_polynomial. Scratch copies with #print axioms show
   only propext, Classical.choice, Quot.sound and the expected sorryAx in the
   dimension and flatness conclusions. Scanned for forbidden declarations and for
   data holes: none. The model and bases are eliminated only within a proposition
   proof; no public data definition selects an arbitrary unproved witness. Verdict: pass.
3. Read the polynomial-model signature, its full docstring and node against the
   displayed partial-chart calculation in https://stacks.math.columbia.edu/tag/07CP.
   The ideal equality follows from Prepared.relation after killing pi and inverting
   a_k; the complement variables are uniquely eliminated. Empty E_k, full E_k,
   m=0, n=0 and zero coefficient rings cause no exception. The statement is a
   strictly smaller algebra step, with no dimension or flatness conclusion.
   Independent Loogle, LeanFinder and grep searches found generic polynomial
   equivalences and presentation tools, not an exact theorem. Also read
   PopescuZeroBaseSingleChartPolynomial: it quotients by ALL original u_l, whereas
   this partial chart imposes only u_j on E_k. Applying it would first require a
   separate localized quotient comparison, as well as renumbering and tensor glue;
   it is not a direct substitute or a few-minute closure of this hole. The full-chart
   theorem additionally uses other charts' relations. Verdict: pass as decomposition.
4. Checked the reduction from the actual fibre prime through principal localization,
   smooth base change, differential bases and the smooth-over-field dimension theorem.
   The private open-embedding helper proves the neighbourhood comparison directly;
   the identical helper in SmoothAtPrimeDifferentialsDimension is private and cannot
   be imported. Every old proof dependency remains used, and every added import
   supplies proof declarations unavailable through the other imports' public closure
   after removing the redundant TensorProduct.Basis import.
   Inspected dag/units/sk-thm-p1.json realized: no realized statement or step is
   bypassed or changed. No old imports or nodes are pruned. Verdict: pass.
5. Checked both node records against the Lean signatures and proof. The existing
   dimension node records the polynomial model and each differential/dimension step;
   proof_deps equals the union of step uses. The new node has source, complete proof,
   three searches, creation and blueprint ancestry, chapter/unit and verbatim Lean
   statement. Its proof_deps likewise matches its steps. Verdict: pass.

Removed the redundant proof-only import Mathlib.LinearAlgebra.TensorProduct.Basis
(already publicly provided by EquationCountFibreDimensionFlat), and recompiled.
Corrected the report's edge-case wording (empty E_k does not imply that the coefficient
algebra is zero), documented the nearby single-chart theorem and why it does not
directly close the remaining hole, and recorded this review. The Lean proof and
statements required no repair. One upper hole is closed and one
strictly smaller hole is added: decomposition, net zero holes, no module pruning.


## Second reading by D4

1. Compared the item module with the repository using diff and the declaration-table
   checker: every existing signature and definition is byte-for-byte unchanged.
   The only changes are the dimension proof, its explanation, and proof-only imports.
   There are no interface changes or forced adaptations. Verdict: pass.
2. Compiled both modules in import order with lcompile.py. Scratch copies printing
   axioms show propext, Classical.choice, Quot.sound and expected sorryAx for the model,
   dimension and flatness; finiteChartEquiv has no sorryAx. The only delivered sorry
   is the entire named theorem Algebra.popescu_partial_chart_polynomial. No forbidden
   declarations or definition holes occur. The unproved model is eliminated inside
   a proposition proof; no data definition chooses its witness. Verdict: pass.
3. Read Prepared.relation, the reduced quotient and actual chart equations against
   Stacks Tag 07CP, specifically its displayed partial D_k calculation:
   https://stacks.math.columbia.edu/tag/07CP. Killing pi removes the constant terms;
   the prepared relation identifies the selected and full f ideals after inverting
   a_k. Each complementary z_l then has a unique linear expression. This proves
   the model's natural-language argument without using smoothness or dimension.
   Checked empty/full E_k, m=0, n=0 (card_le forces E_k empty), zero B, and a_k=0
   (both localizations are zero). Independent LeanFinder, Loogle and grep searches
   found general localization presentations and polynomial equivalences, no exact
   model. Read PopescuZeroBaseSingleChartPolynomial (all u_l imposed),
   PopescuSpecialChartPolynomial (full lifting quotient with a coefficient map),
   and the unrelated coefficient-elimination helper for Tag 07FE: none applies
   directly. Closing the model would require substantial quotient/tensor/localization
   construction. It is strictly an algebra step of the item, not a restatement.
   Verdict: pass as decomposition, one hole closed and one added, net zero.
4. Read the complete dimension proof: the residue-field quotient map is constructed,
   the fibre prime avoids t, the differential bases transport through the polynomial
   model and formal etaleness, and card_le gives rank n. Read the existing proved
   private Algebra.dimAt_openEmbedding; import all supplies it without copying it.
   All old proof dependencies remain used and no realized node in sk-thm-p1.json
   is bypassed. Tested each added Mathlib import by deleting it in a scratch copy:
   Etale.Kaehler is redundant, while Kaehler.TensorProduct is necessary for
   tensorKaehlerEquiv. Verdict: pass after removing the redundant import.
5. Both node Lean statements occur verbatim in their modules. Checked new-node
   source, proof, three searches, creation, blueprint ancestry, chapter, unit and
   Lean record. In both nodes proof_deps is exactly the union of step uses. The
   dimension node's steps follow the compiled proof and name the existing helper.
   No old dependency is dropped. Verdict: pass.

Changed only the redundant proof import Mathlib.RingTheory.Etale.Kaehler and this
report. The earlier review's claim that the private helper cannot be imported is
superseded: import all successfully exposes it. No Lean statement changed; one
original hole is closed, one smaller hole remains, and no module is pruned.
