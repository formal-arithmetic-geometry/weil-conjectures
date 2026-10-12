## What changed

Proved `AlgebraicGeometry.IsCurve.prime_biproduct_primary_iff` in
`Sheaf.AlgebraicGeometry.Curve.PrimeBiproductPrimary`, with its signature unchanged.
Added the proof-only import
`Sheaf.AlgebraicGeometry.Curve.PrimeAnnihilatedPrimaryCases`, using its already-proved
`AlgebraicGeometry.Scheme.prime_annihilated_primary_cases`.

The proof establishes the cohomology vanishing equivalence in every degree by mapping
biproduct injections, projections, and the identity decomposition through the additive
coefficient-forgetting and cohomology functors. It then splits the characteristic prime
into the case equal to the annihilating prime and the case different from it. In the
second case the existing prime-case theorem makes the relevant primary sheaf zero.
Updated the item's DAG proof, dependencies, and proof origin to match this argument.
The unit's realized statement and steps are unchanged.

## Proved and sorry left

Proved `AlgebraicGeometry.IsCurve.prime_biproduct_primary_iff`
(node `lem-pbc-f1-prime-biproduct-primary`): the module's one original sorry is removed.
No new statements and no sorries remain in the delivery.
The proof-only dependency `AlgebraicGeometry.Scheme.prime_annihilated_primary_cases`
is already proved in the repository.

## No longer needed

Removed the direct proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`; it remains a transitive
dependency through `PrimeAnnihilatedPrimaryCases`. No module is claimed globally pruned.
The direct DAG dependency on `lemma-weil-pbc-geometric-stalk-conservative` is replaced
by `lem-pbc-a3-prime-annihilated-primary-cases`; geometric stalk conservativity is still
needed transitively inside that already-proved lemma, so its module is not globally
pruned. The original plan's explicit `Abelian.Ext.addEquivBiproduct` construction is
unnecessary: mapping the biproduct identities proves the required vanishing equivalence.
No derived-global-sections comparison, new primary-torsion transport lemma, or separate
empty-biproduct lemma is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong or changed. The stated DAG plan did not name the
existing prime-annihilated primary-case lemma; it is now used rather than repeating its
stalk and Bezout argument. The proof covers the empty index type by the empty identity
sum, zero sheaves, and characteristics different from r by zero-object cohomology.

First-worker validation (2026-10-12) reported an unused-`f` warning. The current
delivery tool rejects warnings; the second reader repaired this as recorded below.


## Second reading by P2

1. **Public contract: pass.** Compared the only delivered module against the repository
   with `diff`, and checked the existing theorem signature byte for byte. The signature,
   definitions, public import, and existing docstrings are unchanged; there is no change
   record because no mathematical interface changed.
2. **Proof and axioms: pass.** Compiled the module through `lcompile.py` without errors
   or warnings after the repair below. A scratch copy with `#print axioms` confirms that
   both `prime_biproduct_primary_iff` and its prime-case dependency use exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivery contains no
   `sorry`, axiom, unsafe declaration, opaque declaration, extern, or implemented_by.
3. **Split statements: pass, none.** No new declaration, node, or split-off statement.
   Read the existing prime-case lemma: exponent one gives r-primary torsion; Bezout
   kills stalks primary for a distinct prime; conservativity gives the zero sheaf.
   Checked the empty index type, singleton index, zero sheaves, empty scheme, r equal
   to the characteristic prime, a different characteristic prime, and characteristic
   zero. All are handled without an added hypothesis.
4. **Route and pruning: pass.** Read C3's actual definition and the additive cohomology
   infrastructure. Independent `rg` searches in both library roots and `msearch.py`
   grep for zero biproducts and mapped biproducts found no existing theorem directly
   replacing this C3 argument. The elementary mapped-identity argument is appropriate;
   using generic preservation machinery would require more transport. Both remaining
   imports are needed and their visibility is correct. The sole removed old dependency,
   `lemma-weil-pbc-geometric-stalk-conservative`, is listed above and remains needed
   transitively. Read `dag/units/sk-thm-p1.json`: its realized statement and steps remain
   unchanged; this item is below that route and bypasses no unit step. The old docstring's
   Ext product equivalence describes an equivalent justification, while the actual
   implementation and DAG use mapped identities.
5. **DAG agreement: pass.** Read the original and delivered node. The three steps match
   the degreewise zero-object equivalence, existing primary cases, and characteristic
   split in Lean. `proof_deps` is exactly the union of step uses; `proof_origin` describes
   the realized route. Only the permitted proof metadata fields changed. No new-node
   field checks are necessary.

Changed only the declaration's linter setting: retained the unused base morphism `f`
verbatim and added a documented, declaration-scoped `linter.unusedVariables false`.
This removes the warning rejected by the current delivery tool without inventing a
use of `f`, changing the theorem, or changing the proof argument. Corrected the stale
first-worker validation paragraph above. Final dry run and delivery use `deliver3.py`.
