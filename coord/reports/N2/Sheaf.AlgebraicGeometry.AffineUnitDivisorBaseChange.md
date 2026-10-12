## What changed

The original declaration `AlgebraicGeometry.affine_unit_divisor_base_change` keeps its
signature and visibility byte for byte. Its proof constructs the geometric instance
witnesses, obtains germ-compatible rational maps, a unique-fibre boundary equivalence,
and the forward order comparison from `AffineUnitDivisorBaseChangeCore`, explicitly
pulls back a unit to prove forward range inclusion, applies
`AffineBoundaryUnitDivisorDescent` for reverse inclusion, and uses set antisymmetry.
The proof docstring now describes this actual reduction.

The two new modules state strictly separate geometric steps. Their public imports are
only the curve divisor and compactification interfaces needed in their signatures.
Their planned proof ingredients are plain imports: LocalDvrBaseChange in the core;
DivisorClassCurve, PicZeroTorsionBaseChange, SerreDuality, and DivisorSequence in descent.
The existing item's DivisorModule public import remains. The proof-only LocalDvrBaseChange
public import was removed from the item and moved into the core as a plain import.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.affine_unit_divisor_base_change`, by a decomposition, not a completed
independent proof. One hole closed, two holes added: net holes closed minus added is -1.
The remaining holes are exactly:

- `AlgebraicGeometry.affine_unit_divisor_base_change_core`, node
  `lem-sc-affine-unit-divisor-base-change-core`.
- `AlgebraicGeometry.affine_boundary_unit_divisor_descent`, node
  `lem-sc-affine-boundary-unit-divisor-descent`.

Both are public named theorems with exactly `:= by sorry`, in new modules, with sources
and complete natural-language proofs. The first does not assert reverse inclusion;
the second does not construct the geometric setup or assert forward order comparison.
Neither merely renames the original statement. There are no new definitions and no
arbitrary existence witness used to define data. The chosen maps and equivalence are
used only in the proof of the original existential proposition; additionally, germ
compatibility and the unique-fibre property determine them canonically.

## No longer needed

Removed direct imports from the item:

- `Sheaf.AlgebraicGeometry.LocalDvrBaseChange` (proof-only, now plain in the core).
- `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility`.
- `Sheaf.AlgebraicGeometry.DivisorClassCurve` (now plain in descent).
- `Sheaf.AlgebraicGeometry.GenusInvariant`.
- `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality` (now plain in descent).
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` (reached through the natural
  degree-zero Picard/Jacobian comparison used in descent).
- `WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence` (now plain in descent).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.

Every old direct proof dependency is absent from the new combination proof:
`lem-sc-pic-affine-base-change-compatibility`, `lem-sc-compactification`,
`def-sc-field-extension`, `lem-sc-local-dvr-base-change`, `def-sc-divisor`,
`lem-sc-divisor-class-curve`, `lem-sc-deg-principal-zero`,
`thm-sc-jacobian-representability`, `lem-sc-genus-invariant`, and
`lem-sc-divisor-sequence-general`. Compactification, field-extension, and divisor notions
remain statement prerequisites. Local DVR comparison, divisor classes, principal degree,
and divisor exactness remain in the split steps. Jacobian representability remains in
the dependency chain of `lem-sc-piczero-torsion-base-change`. Separate genus comparison
and PicAffineBaseChangeCompatibility are unnecessary for these steps; the natural
comparison uses the points of one Jacobian. Topological invariance is unused throughout.

These are direct-import and proof-plan prunings; no assertion is made that any module
becomes unreachable from every target. The unit's affine argument still uses the boundary
identification, valuation comparison, Jacobian injectivity, and divisor exact sequence.
`dag/units/sk-prop-ext-invariance.json` has empty realized entries; this delivery changes
none of its statement, steps, or realization entries and does not bypass a unit step.

## Where the brief, the DAG or earlier work was wrong

The first worker repaired an earlier near-restatement into a genuine two-step reduction.
However, the new nodes still copied obsolete claims that
PicAffineBaseChangeCompatibility supplied the unique-fibre boundary bijection and
Jacobian injectivity. Its current signature requires a chosen boundary point and supplies
neither fact. The second reader repaired these plans: LocalDvrBaseChange supplies the
unique fibres and order comparison; the cartesian open square identifies the boundary;
PicZeroTorsionBaseChange supplies the exact degree-zero pullback injectivity at n=1.
BoundaryPointClassBaseChange does not constrain its equivalence to the projection, so it
cannot identify an arbitrary supplied e with its own equivalence. The descent proof in
words instead uses flat pullback of the actual rational point ideals specified by he.

## New nodes

`lem-sc-affine-unit-divisor-base-change-core`, in
`Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore`: canonical restriction maps,
unique-fibre boundary geometry, and the forward unit-order comparison.

`lem-sc-affine-boundary-unit-divisor-descent`, in
`Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent`: reverse inclusion for supplied
germ-compatible maps and the boundary equivalence constrained by its fibres. Its route
uses the existing degree-zero Picard injectivity statement.

There are no existing statement or definition changes and no forced adaptations. The
public-import change is recorded in
`coord/changes/affine_unit_divisor_base_change_imports.md`, with all 111 transitive
downstream modules listed. The sole direct importer, UnitsQuotientBaseChange, compiled
unchanged against the revised sandbox interface. Removing a proof-only public import changes an import interface, so the
delivery requires independent CODEX review rather than claiming to be proof-only AUTO.

## Earlier second reading (a previous round; superseded)

1. Compared the item with the repository using diff and extracted its entire theorem
   signature: byte-for-byte identical, including hypotheses, existential instance
   witnesses, all germ clauses, the unique-fibre clause, the forward comparison, and the
   range equality. No existing data definition or declaration visibility changed.
   Verdict: pass. The sole public-import pruning removes a proof ingredient; the
   downstream UnitsQuotientBaseChange uses the theorem, not a LocalDvr declaration, and
   its original source compiled unchanged against the revised overlay. No transitive
   downstream module mentions either removed proof declaration.
2. Compiled all three delivered modules locally in import order with lcompile.py:
   no errors or warnings. Checked all source text: exactly two named theorem sorries,
   no forbidden axiom/unsafe/opaque/implemented_by/extern, no hollow definition.
   Scratch #print axioms checks for all three declarations show only propext,
   Classical.choice, Quot.sound, and sorryAx. Verdict: valid compiling decomposition,
   with the two geometric holes and the imported open statements still unresolved.
3. Read both new statements, their proofs in words, and their matching nodes. Checked
   empty boundary (unique empty equivalence, zero range), singleton boundary (degree
   zero forces zero), identity extension, and genus zero. The supplied maps are fixed
   by germs on the nonempty open; he fixes the actual fibres, so no arbitrary permutation
   or noncanonical map invalidates descent. Independently searched with different
   LeanFinder/Loogle/grep queries and read the upstream germ construction, the local DVR
   theorem, BoundaryPointClassBaseChange, BoundaryDivisorKernelPowers, divisor-class
   comparison, and PicZeroTorsionBaseChange. No duplicate of either full new step found.
   Verdict: true, strictly narrower steps; neither is a repackaging of the whole item.
   Closing either would require substantial geometric formalization, not a short lemma
   application. Used the existing Picard injectivity ingredient in the descent plan.
4. Read the original top-level proof downward and checked its explicit pulled-back unit
   witness and both subset directions. Removed proof-only public import leakage and
   narrowed the new public imports to signature needs; retained plain planned proof
   imports for the open steps. Listed every old direct proof dependency and every
   removed direct import above. Read the unit's statement, three steps, and realized
   entries: the affine boundary/Jacobian/divisor-sequence route is retained.
   Verdict: pass; decomposition with net -1, not a claim of completed proof progress.
5. Checked the original node's proof/dependency union against the actual Lean combination,
   and both new nodes' id, kind, source, searches, created, blueprint, chapter, unit,
   status, and verbatim Lean statement records. Repaired obsolete proof plans and
   synchronized their proof_deps unions. Verdict: pass; existing statement and
   stmt_deps unchanged, new nodes match their Lean signatures exactly.

Changed in second reading: corrected all three proof docstrings, made the core use the
local-DVR geometric plan, made descent use the existing Picard injectivity plan,
fixed new proof-dependency records, removed the item's proof-only LocalDvr public import,
narrowed new public imports, added plain imports of planned proof ingredients, recorded
independent searches, completed pruning and net-hole reporting, and added the required
public-import change record after the first dry run requested it. No proof tactic,
existing signature, or split-off statement was changed.

6. Searched the complete DAG for duplicate blueprint records and found no conflicting
   whole-blueprint record for either split node. Corrected both blueprint objects after
   review: each now points from `thm-sc-constant-invariance` with the prescribed place,
   lists `lem-sc-affine-unit-divisor-base-change` and
   `lem-sc-units-quotient-base-change` in `via`, and includes `"same_as": []`.
   The obsolete `from.node = "lem-sc-affine-unit-divisor-base-change"` and empty `via`
   objects were removed from both node files.


## Second reading by N2

This is an independent reading of the present sandbox, after the earlier review round.

1. **Interfaces: pass.** Read the diff against the repository and compared the complete
   text from `theorem affine_unit_divisor_base_change` through its `:= by`: byte-identical.
   The existential instances, both germ conditions, unique-fibre condition, forward
   divisor equality, and range equality are all preserved. There are no new definitions
   or forced adaptations. The removed public LocalDvrBaseChange import is explicitly
   covered by the existing import change record; the other removed imports were plain.
   Recompiled the unchanged direct importer UnitsQuotientBaseChange against the sandbox
   overlay successfully, with no errors or warnings.
2. **Lean proof: pass as a decomposition.** Independently compiled the three delivered
   modules in import order using lcompile.py, with no errors or warnings. Scratch copies
   with #print axioms for all three theorems show only propext, Classical.choice,
   Quot.sound, and sorryAx. Text inspection finds exactly the two reported named theorem
   holes and no forbidden declaration or hollow definition. The original proof builds
   geometric instances using baseChange_curve and regularity, then combines the two
   lemmas. Its forward subset witness is the actual appTop pullback of the input unit;
   hord has exactly the orientation required for Set.range membership.
3. **Split statements: pass.** Read both signatures and full proof docstrings against
   local_dvr_base_change, picZero_torsion_base_change (injectivity at n=1), the
   divisor-class/Picard comparison, finsum_ord_eq_zero, and the zero-order unit criterion.
   The core omits descent; descent assumes the supplied maps and unique-fibre boundary
   identification and proves only reverse inclusion. Neither restates the entire item.
   Germ compatibility fixes the maps because the open curve is nonempty and stalk maps
   of open immersions are isomorphisms. The fibre clause fixes the point correspondence,
   excluding arbitrary boundary permutations. Flat pullback of rational point ideals
   has multiplicity one; this is the point-class comparison used by descent.
   Checked identity extension, empty boundary (zero Finsupp), one boundary point
   (degree-zero divisor is zero), and genus zero (principal degree-zero divisors).
   Ran fresh LeanFinder, Loogle, and grep searches with different queries, recorded in
   both new nodes. Read BoundaryPointClassBaseChange: it does not constrain its e to the
   projection and cannot replace the required comparison for the supplied e. Read
   BoundaryDivisorKernelPowers and its explicit germ construction; it only handles the
   kernel and supplies no full duplicate. Neither hole closes by a short existing lemma
   application; no unjustified claim of completing those geometric formalizations.
4. **Route and pruning: pass.** Read from the original theorem down through its actual
   two subset proofs. Public imports of new modules provide signature notions only;
   plain imports retain the named proof ingredients for open lemmas. The report lists
   every removed direct import and all ten original proof dependencies now replaced.
   Read sk-prop-ext-invariance's full unit record: its affine paragraph identifies the
   rational boundary, compares valuations, uses Jacobian point injectivity, and recovers
   units through divisors. Those steps remain in the new route. Its realized entries are
   empty and untouched. The literature file named by the source is not present on this
   machine; the unit record contains the affine source paragraph used for this check.
   No claim is made that a removed direct import is globally unreachable.
5. **DAG: pass.** Independently checked proof_deps equals the union of step uses in all
   three nodes. The original node names BaseChangeCurve and the two split steps used by
   the Lean proof. Both new node lean.statement fields match their full signatures
   byte for byte. Checked source, status, created, chapter, unit, proof_origin, searches,
   and blueprint ancestry through thm-sc-constant-invariance and the parent affine
   argument. The existing node's mathematical statement and stmt_deps are unchanged.

Changed in this reading: added independent search evidence to both new node records and
this current review section. No Lean proof, existing signature, definition, split statement,
import, or mathematical proof plan needed a further repair. The hole accounting remains
one original hole closed by decomposition, two new holes added, net -1.
