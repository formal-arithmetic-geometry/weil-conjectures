## Files written

- `dag/nodes/sec-trace-formula/lem-trf-filtered-ring-log-pushout.json`: statement, split; eight proof steps, no new nodes. Reuses two existing Mathlib leaves. The item's complete fixed-monoid quotient comparison has no Mathlib match in the searches run.
- `citations.json`: four verbatim statement quotations, one for each proof-step citation.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, logification, units with filtered colimits, and unit pushouts found no declaration stating this item. Nearby etale-unit stalk results and the private `exists_unit_stage` in `PointedSmoothFamilyStage.lean` do not state the fixed-monoid quotient comparison.

## WANTED

None. The algebraic argument is explicitly agent-written, using the local Stacks filtered-colimit description and existing DAG Mathlib leaves.

## Findings and changes

The item was unsplit and the sandbox had no previous node, report or search log. There is no released repair note for it. I copied the live item, retained its statement, source, blueprint ancestry, created record and inherited searches, and appended the actual searches from this run. There is no statement dispute and no change to any hypothesis or conclusion.

The essential inputs already exist as `lem-pc-filtered-colimit-commrings-elementwise` and `lem-weil-pbc-filtered-colimit-sets-elementwise`, both Mathlib leaves. Their statements were read in full. In particular I did not substitute the directed-poset-only `lemma-nagata-filtered-colimit-finite-data` for a filtered-category statement. Nor did I cite a definition for an elementwise theorem. The Mathlib declarations behind the leaves were read in `CategoryTheory/Limits/ConcreteCategory/Basic.lean` (representatives and eventual equality), `CategoryTheory/Limits/Types/Filtered.lean` (including the same-stage criterion), and `Algebra/Category/Ring/FilteredColimits.lean` (forgetful preservation). The Loogle result about nonunits assumes local homomorphisms and is not applicable; its module is absent from the pinned source. The semantic searches returned ring and monoid colimit constructions, not the item's comparison. The second phrasing explicitly searched for the quotient relation.

The split proves unit lifting by choosing a representative of an inverse and making the single equation xy=1 true at a later stage. It then constructs the monoid structure on the set colimit and the inverse on R times the units of A. Checking the defining quotient relations directly eliminates the need for an unsupported finite-congruence-chain assertion. No new lemma is a restatement of a clause of the item. All elementary claims are short consequences of the explicit definitions and the two cited leaf statements; in particular the finite common refinement is written out using the equalization axiom.

The chapter and unit records and the three-level rule in SETUP were read. This auxiliary algebraic statement serves the associated-log stalk and chart-spreading input already identified by its blueprint ancestry; it does not replace the geometric unit route. I read the current main-20261015 proof of `lem-trf-local-term-locality`, which uses contracting correspondences and normal-cone specialization. It does not itself state this algebraic auxiliary. Blueprint searches for filtered colimits, pushouts, fixed monoids and eventual equality found no blueprint node equivalent to the item. The existing two leaf nodes supply its generic inputs. No SGA source is used.

## Not duplicates

No new nodes. The two existing general filtered-colimit leaves are cited directly. The related directed finite-data node is not duplicated or cited under stronger hypotheses than its statement supplies.

## Review by Q124

I read `literature/stacks-project/categories.tex`, Tag 04AX (`section-directed-colimits`), from Definition 002V through the explicit eventual-equality formula and the finite-limit lemma 002W. The proof origin is agent, because the fixed-monoid quotient calculation is my argument rather than a theorem claimed to be printed there. There are no new nodes requiring separate sources. I checked delivery-errors B through E, both copies, against the written item and its source.

Step 1 uses exactly the three filtered-category axioms stated in the item. A finite common target is obtained by induction, and each required commutation is imposed by postcomposing with an equalizer of parallel arrows. This addresses non-poset indices explicitly.

Step 2 cites the ring leaf's clause (1) for the inverse representative and clause (2) for equality of the product with 1. Both are literally in its statement. All objects are commutative unital rings and the diagram is small and filtered, as that leaf requires. The two arrows produced for the product and 1 need not coincide: any unital map takes 1 to 1. The composite starting at the prescribed i therefore already suffices. Commutativity makes the single product equation a two-sided inverse. This proves all the unit assertions without finite generation of R.

Step 3 uses the same ring leaf's clause (2), this time for the underlying values of two units. Equality of units from equality of their values follows from uniqueness of a two-sided inverse, not an additional colimit theorem. The citation quote includes the exact clause applied.

Step 4 uses only the defined generating relations and compatibility of beta. Images of generators lie in the next quotient relation, so the induced map exists; identity and composition hold on representatives. The same check gives the maps to Q.

Step 5 uses clauses (1) and (2) of the set leaf, which explicitly state representatives and eventual equality for every small filtered category. Its hypotheses match the diagram constructed in Step 4. The finite witness diagram is synchronized by Step 1. Multiplication, its independence, and the monoid laws are then checked in a single stage. This is a direct argument rather than an uncited preservation-of-algebraic-structures theorem.

Step 6 uses the already proved unit lifting and unit equality to define H, and writes the product and unit checks on a common-stage representative. Step 7 uses the prescribed-starting-stage unit assertion, so e becomes invertible after an arrow out of the actual stage representing a. Its displayed equality is precisely the defining relation at that later stage. The kernel congruence argument explains why checking generators proves independence of all quotient relations.

Step 8 uses clause (1) of the set leaf for exhaustiveness of the representatives in C, and the definition of a quotient for exhaustiveness in P_i and Q. Both composites are explicitly evaluated on those representatives. It also evaluates the two structure maps, proving the final compatibility clause.

The small cases checked were: a singleton identity-indexed diagram, where the comparison is the identity; the zero ring, where the unit group is trivial and E=R collapses Q to the trivial monoid; a diagram eventually mapping to the zero ring, where 1=0 is witnessed at a stage; and an idempotent noncancellative R, for which the congruence-kernel proof uses no cancellation. Parallel index arrows are handled by Step 1 rather than silently treated as equal. Empty I is excluded explicitly in the statement. No proof step exceeds 2000 characters (the maximum is 1003); no hidden standard theorem was left inside a long step. The statement dependencies remain the two notions actually named in the statement. The union of all uses is exactly the two proof dependencies, and citations.json quotes each cited statement verbatim.

## Unfinished work

None in this one-level split. No Lean was written or compiled. Required server dry run and delivery results are recorded below when obtained.
