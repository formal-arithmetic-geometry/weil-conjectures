## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFormalApproximation`
with a complete Lean proof from two strictly finite-order geometric statements. The existing
public theorem has exactly its original signature and visibility. Its docstring and DAG proof
now describe the actual Cauchy-sequence argument.

The proof chooses a representative at each finite order, proves compatibility by subtracting
residual germs and reflecting ideal membership, applies Mathlib variable-ideal adic completeness,
and proves uniqueness using separatedness. Representatives determine the same quotient class
by the reflection lemma; choices occur only inside the proof, and no definition or exported
object is chosen from an unproved existence theorem.

The proved private helper `powerSeries_variables_pow_germs` establishes the forward direction
without depth, locality, or Noetherian assumptions. It uses `ΓSpecIso_inv_naturality`, the
restriction square on `appTop`, `germ_stalkMap_apply`, and ideal comap/power monotonicity. It has
no sorry. A scoped elaboration-transparency option accommodates the equivalent presentations
of sections on the preimage of the top open; the proof still passes the kernel normally.

Added proof-only imports of `Mathlib.RingTheory.AdicCompletion.Completeness` and the two new
finite-order modules. The two new modules retain the Hartogs proof dependency used by their
source arguments. All three delivered modules compiled through launcher `lcompile.py`.

Source read: [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9), specifically
the first displayed calculation before taking its inverse limit. The checkout does not contain
the fetched literature tree, so the source was read from the Stacks website. Searches ran through
`msearch.py`; LeanSearch returned HTTP 500 and is recorded as unavailable. Loogle returned no
mixed power-series/stalk-map result. LeanFinder returned adic-completion/extensionality lemmas
for the limit argument, and unrelated Weierstrass/evaluation results for the finite-order
geometry. Repository, DAG, imported-blueprint, and Mathlib searches found no existing declaration
of either new finite-order statement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.existsUnique_powerSeries_punctured_formal_approximation`
(node `lem-sbc-power-series-punctured-formal-approximation`). Its body contains no sorry.

Added two holes, each a public theorem whose entire proof is `:= by sorry` in a separate module:

- `AlgebraicGeometry.Scheme.exists_powerSeries_punctured_finite_order_approximation`, node
  `lem-sbc-power-series-punctured-finite-order-approximation`, module
  `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFiniteOrderApproximation`.
- `AlgebraicGeometry.Scheme.powerSeries_mem_variables_pow_of_punctured_germs`, node
  `lem-sbc-power-series-punctured-ideal-detection`, module
  `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedIdealDetection`.

This is a decomposition: one upper hole closed and two finite-order holes added, not a
sorry-free proof of the mathematical theorem or a net reduction of holes. The first statement
allows its representative to depend on n and asserts neither compatibility nor uniqueness.
The second statement only reflects ideal membership for one global series at one finite order;
it contains no existence or simultaneous approximation claim. The compatibility, passage to the
limit, forward germ membership, and uniqueness are all proved in the assigned module.

Edge cases checked in the source arguments: n=0 uses unit ideals; n=1 is the constant-term
comparison; zero sections and zero series work; no domain or reducedness assumption is used.
For positive n the quotient is finite free even when A has nilpotents. The hypotheses and
positive number of variables are retained. Every new theorem has its source, complete proof
in words, and blueprint id in its docstring. No definition, axiom, or target signature changed.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction` from the assigned module.
It is still needed by both new finite-order statements and remains imported in their modules;
it is not globally pruned.

The assigned node directly uses only the two new nodes and
`lem-weil-pbc-power-series-variables-complete`. Its previous direct dependencies
`lem-sbc-depth-two-hartogs-restriction`, `lem-weil-pbc-spec-map-stalk-localization`, and
`lem-weil-pbc-affine-open-stalk-localization` are transferred to the finite-order arguments.
They are not claimed to be globally unnecessary. No whole module or mathematical dependency
is pruned. The coefficient-by-coefficient limit construction is unnecessary: Mathlib's
`IsPrecomplete.prec` and `IsHausdorff.eq_iff_smodEq` already supply that part.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan was mathematically valid, but the Hartogs declaration alone does not
expose the finite-free thickening comparison in the exact section-and-stalk interface needed
here. That comparison is substantial glue rather than an application of the general Hartogs
signature. It is now isolated into the two finite-order statements, both strictly smaller than
the original simultaneous existence-and-uniqueness assertion.

The original plan's stalk-coordinate argument is unnecessary for the forward implication:
canonical morphism naturality proves it directly. The converse still needs the finite-order
quotient comparison and its stalk identification. No statement was disputed, weakened,
strengthened, or adapted. The unit route through the 0EY9 power-series comparison is retained;
its realized statement and step arrays are empty, and none were edited.

## New nodes

`lem-sbc-power-series-punctured-finite-order-approximation` isolates the surjectivity at one
fixed quotient order in the first displayed calculation of Tag 0EY9. Its proof uses the
finite-monomial basis, Hartogs on the punctured spectrum, and the canonical localization
identification of thickening stalks. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/PowerSeriesPuncturedFiniteOrderApproximation.lean`.

`lem-sbc-power-series-punctured-ideal-detection` isolates the injectivity at one fixed quotient
order in the same calculation. Stalkwise vanishing on the thickening and the finite-free
Hartogs comparison force the quotient class to vanish. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/PowerSeriesPuncturedIdealDetection.lean`.

Both inherit the item's chapter, unit, and blueprint ancestor. Actual logged searches are
recorded, including service unavailability. No change record is needed: existing statements,
definitions, and public imports are unchanged, and there are no forced adaptations.

## Second reading by G1

1. Compared every delivered module with the repository. The sole existing public declaration's
   signature is byte-for-byte unchanged. Its public imports are unchanged; only proof imports,
   its proof docstring, and its proof body differ. The two other modules are new. No definition,
   target, or other existing declaration changed. Verdict: pass.
2. Compiled all three modules in import order with launcher lcompile.py: no errors or warnings.
   There are exactly two sorry occurrences, each the entire proof of a reported public theorem;
   none in the main theorem or private helper, and no forbidden declaration or option. A scratch
   copy's #print axioms shows propext, Classical.choice and Quot.sound for the private helper;
   the main theorem and both finite-order theorems additionally show sorryAx, as expected.
   The scratch copy was removed. Verdict: pass as a decomposition, conditional on two open lemmas.
3. Read both new statements and their complete docstring arguments against
   https://stacks.math.columbia.edu/tag/0EY9. At positive n, B/I^n is finite free over A and the
   thickening is supported on Spec(A); its open part is supported on U. Hartogs therefore
   computes its sections canonically, giving the asserted lifting and detection statements.
   The zero-order unit ideal, zero section/series, first-order constant coefficients, and rings
   with nilpotents cause no exceptions. These are separate fixed-order surjectivity and
   injectivity assertions, not renamed copies of simultaneous unique approximation. Additional
   launcher searches used the descriptions “sections of a finite free infinitesimal neighborhood
   over punctured spectrum extend by depth two Hartogs” (LeanFinder),
   “MvPowerSeries, RingHom.ker” (Loogle), and punctured/quotient/thickening/sections keywords
   (grep); repository searches also inspected the adjacent power-series modules and upstream
   algebraic geometry files. No duplicate was found. The global-sections theorem already imports
   this item, so using it here would be circular. Neither geometric hole has a short closure
   using the available declarations. Verdict: pass.
4. Checked compatibility, limit approximation, forward ideal mapping, and separatedness from
   the top downward. Mathlib supplies completeness and separatedness directly; the geometric
   finite-order steps still require the two new statements. Proof imports are private, and the
   Hartogs imports in the new modules retain the source route. “No longer needed” lists all three
   removed old direct DAG dependencies and explains their transfer to the new nodes; no whole
   module is claimed pruned. The unit sk-prop-input-spreading has empty realized statement/step
   arrays, which are unchanged, and the source route is preserved. Verdict: pass.
5. Checked all three JSON records against the Lean statements and argument. Only proof,
   proof_deps and proof_origin changed in the existing node. The new records have matching
   verbatim Lean signatures, sources, proof steps, dependency unions, search records, creation
   records, blueprint ancestry, chapter and unit. Verdict: pass.

Second reading changed only this report: added the independent audit and explicit axiom results.
No mathematical, Lean, import, or DAG repairs were necessary. The hole accounting remains one
original hole closed and two strictly smaller holes added (net minus one hole closed).
