## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_root_splitting`
with a complete Lean assembly from two geometric intermediate theorems. The existing signature,
visibility, public imports, and docstring are unchanged. The exponent and number of split factors
are both `Nat.card G`; positivity and invertibility are proved directly.

Added proof imports of `RegularDivisorStrictHenselRootSection`,
`PuncturedRootSectionEtaleDescent`, the already proved category-theoretic extensive lemma,
and the algebraic closure construction. Three private, fully proved helpers establish etale ascent of the regular divisor, trivialize a torsor
from a section and compare its ambient pullback with its pullback over U. The comparison uses
monicity only after pulling i back along φ, obtained from beta; it does not assume i monic.
Coproduct reindexing, both pullback comparisons, and the fold-map equation are proved explicitly.
The regular base and divisor quotient are obtained using etale ascent, with the quotient
identified as an etale tensor-product base change; flatness preserves the nonzerodivisor.

The new statements and target assembly are checked with lcompile.py. The original geometric
plan is preserved, with the strict-hensel calculation and the descent separated. This is a
partial delivery, not an axiom-free proof of the entire geometric theorem.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_root_splitting`
(node `lem-sbc-regular-divisor-galois-root-splitting`). Its module contains no remaining sorry.
All three private helpers, `regular_divisor_properties_of_etale`, `split_of_section`, and
`split_over_ambient_of_section`, are completely proved. The regularity helper was also
compiled independently before integration: it uses the already proved etale-localization
lemma, flatness, and the quotient/tensor-product equivalence.

Added two holes, each a public theorem whose proof is exactly `by sorry`:

- `AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_section`
  (`lem-sbc-regular-divisor-strict-hensel-root-section`), in
  `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection`.
- `AlgebraicGeometry.Scheme.punctured_root_section_etale_descent`
  (`lem-sbc-punctured-root-section-etale-descent`), in
  `Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent`.

This closes one upper hole by decomposition into two strictly separate parts of its argument,
so the delivery-local count is 1 closed minus 2 added, net -1. The maintainer computes
the import-closure ledger separately; this is not claimed as positive ledger progress.
The first theorem supplies a section on one fixed limit ring, without any finite-stage chart
or coproduct splitting. The second is a general descent statement with that section as an
explicit hypothesis; it needs neither a group, ramification, regularity, nor a nonzerodivisor assumption. The torsor argument
combining these inputs into the final splitting is actual Lean proof.

## No longer needed

Removed redundant newly added proof imports `Mathlib.RingTheory.Flat.Basic` and
`Mathlib.RingTheory.TensorProduct.Quotient`: both are already available through
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`. Also removed
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, already publicly available
through the existing EtaleTorsor -> Etale -> Smooth -> Smooth.Field imports.
Every original import is needed by the unchanged statement. The original node had no
proof dependencies to prune. The proof uses neither cyclic intermediate-cover classification
nor root-model normality; these were not dependencies of this item, and are not claimed as
pruned modules of this delivery.

## Where the brief, the DAG or earlier work was wrong

The item's three proof steps had empty `uses` lists and no proof dependencies: no existing
stated declarations implement the strict-hensel root-section or its descent. These are now
two named, sourced statements rather than a hole hiding the whole argument.

The source pages read were [09EB](https://stacks.math.columbia.edu/tag/09EB),
[0BRM](https://stacks.math.columbia.edu/tag/0BRM),
[0EYE](https://stacks.math.columbia.edu/tag/0EYE),
[0EYG](https://stacks.math.columbia.edu/tag/0EYG),
[0BSK](https://stacks.math.columbia.edu/tag/0BSK), and
[05N9](https://stacks.math.columbia.edu/tag/05N9). The local literature checkout is absent on this machine. Blueprint search
found no statement already giving either intermediate theorem. The ancestor helper could not
follow the parent's `created.item` because it is a module name; the new nodes preserve the
explicit ancestor `sbc-thm-spreading-finite-etale-galois` already recorded in the parent.

Edge cases checked: off-divisor points use an existing strict-hensel torsor section, pulled
to the root algebra, and do not require that root algebra to be local. A group is nonempty,
so its cardinal is positive. A unit divisor equation gives the zero quotient, whose regularity
is allowed. Empty base spectra have no point y to treat. Descent permits n=0 and empty
punctures; it assumes existence of the corresponding limit section and asserts no ramification
result in that case. No existential witness supplies data to a public definition.

## New nodes

`lem-sbc-regular-divisor-strict-hensel-root-section`: the tame ramification, Abhyankar and purity
portion of the original proof, stopping at one section over the fixed strict-hensel root ring.
Its docstring explains the stabilizer argument and handles points off the divisor separately.

`lem-sbc-punctured-root-section-etale-descent`: the finite-presentation descent portion,
for any finite etale cover and any root exponent, with the limit section as a hypothesis.
It asserts only pointedness and the descended section. Regularity and nonzerodivisor
properties are proved separately in the original module; the descent theorem assumes
no regularity of R or R/(f), and allows arbitrary f.

No change record is needed: no existing interface or target statement changes, and no other
existing module is adapted.

## Second reading by P4

1. Compared the existing module with the repository using diff and the delivery
   declaration parser. PASS: the existing declaration signature, visibility,
   public imports, and docstring are unchanged; only proof imports, three proved
   private helpers and the theorem body were added. No definition, existing
   statement, target or other existing module changes.
2. Compiled all three modules locally in import order with lcompile.py. PASS:
   no errors or non-sorry warnings; the item has no sorry, and the only new
   holes are the two public named theorems listed above. No forbidden declaration
   or hollow definition is introduced. A scratch-copy #print axioms check after
   import removal confirms that all three private helpers use only propext,
   Classical.choice and Quot.sound. The target and both split theorems additionally
   use sorryAx, as expected from the open statements. The canonical ring is the actual
   coordinate-ring colimit; the structural map is characterized by its cone
   composites, and full faithfulness recovers its uniquely determined ring map.
3. Read both split statements, their complete proof docstrings and their nodes
   against [0EYG](https://stacks.math.columbia.edu/tag/0EYG),
   [0BRM](https://stacks.math.columbia.edu/tag/0BRM),
   [0BSK](https://stacks.math.columbia.edu/tag/0BSK), and
   [05N9](https://stacks.math.columbia.edu/tag/05N9). PASS: the fixed-limit
   ramification calculation and general finite-presentation descent are separate,
   strictly smaller parts, not restatements of the target. Checked trivial groups,
   unit divisor equations, empty spectra and punctures, and n=0 in descent. In the
   on-divisor case the root ring is local because its closed fibre has only the
   root T=0, and regular because T is regular and its quotient is the regular
   divisor ring. In the off-divisor case pull an existing section over H back
   to the root algebra, with no locality claim for that algebra. The descent
   argument first factors the given map through the finite etale base change
   over D(f); beta supplies the necessary compatibility without assuming i monic.
   Repeated Mathlib searches with different phrases through msearch.py and rg
   in both library roots. The relevant generic Mathlib lemma is
   RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit; its algebra-map
   factorization does not alone provide the pointed root-puncture diagram and
   geometric identifications in the new descent statement. No exact duplicate
   was found, and neither hole admits a short closure from these search results.
4. Read the proof from the target through regularity ascent, torsor reindexing,
   section trivialization and both pullback comparisons. PASS: these steps are
   actual checked proofs, including the fold-map equation. Removed the three
   redundant newly added proof imports listed in No longer needed. The original
   proof_deps was empty, so there are no old dependency nodes to prune. The unit
   sk-prop-input-spreading and its realized record are unchanged; its pre-existing
   empty realized lists are not repaired by this delivery. The divisor/tame-root
   part of the unit route is retained.
5. Compared every new node's lean.statement byte for byte with its Lean signature,
   and checked proof_deps equals the union of the proof steps' uses for all three
   nodes. PASS: source, creation, search and blueprint ancestry fields are present;
   the existing node changes only proof, proof_deps and proof_origin. No change
   record is needed because no existing interface changes.

Second-reading changes: removed the redundant proof imports
Mathlib.RingTheory.Flat.Basic, Mathlib.RingTheory.TensorProduct.Quotient, and
Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure,
and documented the independent checks and the available generic descent lemma.
The hole accounting remains one existing hole closed by decomposition and two
new holes added (delivery-local net -1), not an axiom-free proof of the geometry.
