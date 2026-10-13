## What changed

Repaired the returned proof of
`AlgebraicGeometry.Scheme.Modules.sectionRing_coefficient_arithmetic_of_numerator`
in `Sheaf.AlgebraicGeometry.SectionRingCoefficientArithmetic`, preserving its exact
signature and docstring.

Removed the duplicate private theorems `eqToHom_app_heq`, `ring_power_of`, and
`veroneseIso_power`, and the private `veroneseIso` definition and `power_generator`
helper. The generator argument now proceeds directly inside the arithmetic proof:
the degree-zero unit is a generator by `unitSectionsEquiv`; the successor step uses
the already proved `IsFreeGenerator.tmulSection` and `IsFreeGenerator.app_hom`, with
`restrict_mul` identifying the restricted homogeneous multiplication. This proves
the property actually needed without recreating the tensor-power comparison lemmas.
The existing fraction arithmetic and scalar cancellation arguments are retained.

Removed the now-unused proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`. Only the original
two public imports remain. No other modules or interfaces change. The original
DAG proof already specifies this direct generator induction, so its route and
proof dependencies remain accurate and no node edits are necessary.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.sectionRing_coefficient_arithmetic_of_numerator`
(node `lem-sc-section-ring-coefficient-data-arithmetic`).
No holes remain; zero holes were added or split off. The remaining private helper
`restrict_mul` is proved. The repaired module compiles without warnings.
The delivery axiom probe passes, and an explicit run of
`tools/import_prune_check.py` exits successfully, including the duplicate-statement
guard that returned the earlier delivery. The required dry run reports OK; nothing
is pushed. The second reading remains for the independent reader.

## No longer needed

Removed the proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` from the returned
version. The arithmetic proof no longer needs tensor-power-section comparison
calculations, their auxiliary isomorphism, or their duplicate private lemmas.
The module is not claimed globally prunable, since other library modules use it.
Both original public imports and both original proof-dependency nodes remain
needed: `def-sc-invertible-section-ring` and `def-sc-local-free-generator`.
No DAG nodes or library modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly identified the three duplicate private theorem
statements in the earlier delivery. The earlier second reading incorrectly
accepted their local reproduction because the existing declarations are private.
Private visibility does prevent importing those particular declarations, but it
does not justify duplicating their statements. The repair removes all three,
using the public tensor-product generator interface instead. It also removes the
associated definition and generator helper. The old second reading has been
removed because it predates this repair; the independent reader must check the
repaired version.

No mathematical or public-interface errors were found. The unused positive-degree
hypothesis stays unchanged. The direct generator induction includes exponent zero
and works on the empty open; no global cancellation assumption is introduced.

## Second reading by R1

1. PASS: compared the complete delivered module with the repository using diff,
   and checked the existing theorem signature and docstring byte for byte.
   Neither changed; the public imports, universe, namespace and visibility also
   remain unchanged. There are no changed definitions or other delivered modules.
2. PASS: independently compiled the delivered module with lcompile.py (no errors
   or warnings). A fresh scratch copy of this exact repaired source prints only
   propext, Classical.choice and Quot.sound for both the main theorem and the
   private restrict_mul helper. No sorry or forbidden declaration mechanism is
   present. The exponent-zero generator proof uses the unit equivalence; the
   successor uses tensor-product generators transported along tensorPowAddIso.
   Addition and multiplication use common denominators and injectivity of scalar
   multiplication by the resulting local generator, including empty opens and
   zero numerators. No arbitrary witness is used to define data.
3. PASS: no statements are split off and no holes are added. Read the remaining
   private helper: it is the homogeneous multiplication formula followed by
   naturality and tmulSection_map. Searches in both library roots for restriction,
   multiplication and coefficient arithmetic found no existing replacement for
   this section-ring-specific formula. An independent Loogle search for
   HomogeneousLocalization.Away.mk confirmed the existing fraction constructor,
   surjectivity and value lemmas that this proof already uses.
4. PASS: the proof follows the shortest direct route through the existing tensor
   generator interface and Mathlib fraction arithmetic. Both public imports are
   needed by the signature. Both original proof_deps remain used; hence no old
   dependency node is missing from No longer needed. The removed ClearDenominators
   import belonged to the earlier returned proof, not the repository baseline.
   No module is globally pruned. Checked sk-thm-curveestimate.json realized:
   this item is not a realized unit statement or step and bypasses none.
5. PASS: read lem-sc-section-ring-coefficient-data-arithmetic and both dependency
   records. Its existing proof describes precisely the implemented generator
   induction, fraction arithmetic and local scalar cancellation; proof_deps and
   document proof_origin agree. No new node or node-field repair is needed.

Second reading changed only this report and refreshed the scratch axiom-check
copy, which had still contained the rejected duplicate helpers. The delivered
Lean proof needed no changes. Independently verified one original hole closed,
zero holes added, zero split off; this is a proof, not a decomposition.
