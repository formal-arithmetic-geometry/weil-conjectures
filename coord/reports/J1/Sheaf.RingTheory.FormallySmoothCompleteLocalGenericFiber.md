## What changed

Repair of the return at head 610e4a411: removed the duplicate private
`Algebra.formallySmoothAdic_quotient`. The existing
`RingHom.formallySmoothAdic_quotient` is private and its module imports this item;
`import_direction.py may` rejects the reverse import as a cycle. Instead, the proof now
imports and applies `Algebra.formallySmoothAdic_tensorProduct` from
`Sheaf.RingTheory.FormallySmoothAdicBaseChange`, and uses Mathlib's quotient/tensor
algebra equivalence. The proved private `Algebra.formallySmoothAdic_of_algEquiv`
transports arbitrary ideal-adic formal smoothness through an algebra equivalence;
it does not restate the quotient theorem. No existing signature or visibility changed.
The item's node now records this base-change route and dependency. The second-reading
section below is the previous reader's record and predates this repair.

Replaced the sole sorry in `Algebra.isGeometricallyRegular_genericFiber_of_formallySmoothAdic`
with a compiling coefficient-ring reduction, without changing its signature or existing docstring.
The proof obtains the regular complete subring, proves the induced residue map bijective,
obtains quotient formal smoothness from the existing tensor base-change theorem and
a general private algebra-equivalence transport helper, applies the existing finite coefficient
lifting theorem, constructs the finite fraction-field extension using Mathlib, and builds the
four tensor equivalences needed for every geometric-regularity test extension. Noetherianity
of the original generic fibre is proved directly by localization.

Added four modules, one theorem each:

- `Sheaf.RingTheory.FormallySmoothRegularCompleteFiniteFieldRegular`: proved regularity
  of C by closed-fibre regularity and flat ascent, then geometric regularity of its generic
  fibre and regularity after arbitrary finite fraction-field extensions.
- `Sheaf.RingTheory.FormallySmoothRegularCompletePurelyInseparableRegular`: proved the
  localization base case, characteristic-zero case, and strong induction on extension degree,
  using the existing pth-root tower for the strictly smaller intermediate extension.
- `Sheaf.RingTheory.FormallySmoothCompleteDegreePRegular`: proved the degree-p step from
  a unit-derivation presentation and the existing polynomial-quotient regularity theorem.
- `Sheaf.RingTheory.FormallySmoothCompleteDegreePUnitDerivation`: the one remaining
  construction, with complete source proof and its own node. It constructs a polynomial
  quotient presentation and a unit derivative; it assumes and concludes no regularity.

The new lemmas do not need a power series presentation of the base. The construction uses
07PH as already stated for finite-type algebras over arbitrary complete Noetherian local rings.
The coefficient subring's unused power series/Cohen-ring model is therefore discarded.
The instance exclusion for `IntermediateField.module'` is scoped to each affected declaration
with `attribute ... in`, to prevent competing scalar structures without exporting any change.
Proof dependencies for the unfinished construction remain imported in its own module.
All writes are in the sandbox; no other existing module or interface was adapted.

## Proved and sorry left

Closed the one original hole:
`Algebra.isGeometricallyRegular_genericFiber_of_formallySmoothAdic`
(node `lem-weil-pbc-formally-smooth-complete-local-generic-fiber`).

Added one hole:
`Algebra.exists_degree_p_presentation_unit_derivation_of_formallySmoothAdic`
(node `lem-weil-pbc-fs-complete-degree-p-unit-derivation`). Its proof is exactly `:= by sorry`.
There are no other sorries in the five delivered Lean files, no new definitions with postponed
data, and no new axioms. This is a decomposition: one original hole closed, one construction
hole added, net zero holes. It is not a claim that the generic-fibre theorem is axiom-free;
existing imported proof dependencies may still contain sorry.

The three new regularity declarations are proved:
`Algebra.isRegularRing_tensorProduct_of_formallySmoothAdic_regular_complete`,
`Algebra.isRegularRing_tensorProduct_of_formallySmoothAdic_regular_complete_purelyInseparable`,
and `Algebra.isRegularRing_tensorProduct_of_formallySmoothAdic_degree_p`.

All five modules compile together through `lcompile.py --all`, with no compiler/linter warnings.
The construction was checked mathematically on zero tensor fibres (the zero element is a unit
in a zero ring, and the quotient is zero), prime p = 2, coefficient rings that are fields,
and imperfect coefficient fields. Prime degree excludes the trivial extension; the induction
handles that extension separately. No hypothesis of regularity is smuggled into the construction.

## No longer needed

Removed direct proof imports from the item's module:
`Sheaf.AlgebraicGeometry.DegreePExtensionRegular`,
`Sheaf.FieldTheory.PurelyInseparablePthRootTower`,
`Sheaf.RingTheory.Derivation.CompletionAndLocalization`,
`Sheaf.RingTheory.Derivation.DetectNonPthPower`,
`Sheaf.RingTheory.Derivation.FormallySmoothAdicExtension`,
`Sheaf.RingTheory.FiniteModuleComplete`,
`Sheaf.RingTheory.GeometricallyRegularFieldExtension`,
`Sheaf.RingTheory.LocalizationOfRegularRing`, and
`Sheaf.RingTheory.RegularLocalOfFlatWithRegularClosedFiber`.
These modules are still needed through the new helper modules and their remaining construction;
they are relocated dependencies, not globally pruned work.

No existing node or module is globally pruned by this delivery. The original DAG's separate
Cohen-ring/characteristic-zero argument and power-series case distinction are unnecessary:
Mathlib's characteristic split and triviality of purely inseparable characteristic-zero
extensions handle the zero-characteristic branch, while 07PH supplies the same construction
in positive characteristic without a model hypothesis. The coefficient subring theorem itself
is still needed. All dependencies needed by the remaining construction are recorded in its node.

The following old direct `proof_deps` are no longer used by the item itself:

- `def-weil-pbc-adically-complete-ring`
- `def-weil-pbc-finite-purely-inseparable-extension`
- `lem-weil-pbc-degree-p-extension-regular`
- `lem-weil-pbc-derivation-extends`
- `lem-weil-pbc-derivation-nonzero-on-non-pth-power`
- `lem-weil-pbc-finite-module-complete-over-complete-noetherian`
- `lem-weil-pbc-flat-over-regular-with-regular-fibre`
- `lem-weil-pbc-fs-adic-lift-derivation`
- `lem-weil-pbc-geometrically-regular-finitely-generated-extensions`
- `lem-weil-pbc-localization-of-regular-ring`
- `lem-weil-pbc-purely-inseparable-pth-root-tower`

They are supplied through the helper proofs or remain statement prerequisites; this list
does not claim they are globally pruned.

## Where the brief, the DAG or earlier work was wrong

The returned proof duplicated a private quotient theorem already present in the regular-map
module. Importing that module would create a cycle; its private theorem is unavailable to
importers in any case. This repair reuses the existing tensor base-change theorem instead
of proving quotient base change again. Its added import is needed directly by the item.

No statement was changed or disputed. The original plan omitted substantial Lean glue for
quotient scalar structures, residue-map compatibility, fraction-field finiteness, and tensor
associativity. That glue is now proved. The construction of the cleared finite coefficient
model, extension/localization of its derivation, and tensor polynomial presentation remains
in the explicitly named construction theorem. The existing finite-subalgebra-fraction-field
module was searched but has a polynomial/power-series hypothesis, so it cannot directly supply
the general complete-domain construction now used.

The complete source text was read online at Stacks Tag 07PM; the local literature source file
is absent on this machine. The already-recorded 07EH/07EG citation correction remains valid:
base change uses 07EG. No unit statement or realized unit step is bypassed; all new nodes
belong to `sk-thm-p1`, as does the original item.

## New nodes

`lem-weil-pbc-fs-complete-degree-p-unit-derivation` records the finite integral model,
denominator-cleared root presentation, finite-complete tensor algebra, and extended derivation
with unit value. It is the only new unproved statement. It does not assume or assert regularity.

`lem-weil-pbc-fs-complete-degree-p-regular` combines that construction with 07PG and transports
regularity through the supplied polynomial quotient equivalence; its Lean proof is complete.

`lem-weil-pbc-fs-regular-complete-purely-inseparable-regular` records the proved localization
base case, characteristic-zero case, and strong degree induction via 09HI and the degree-p step.

`lem-weil-pbc-fs-regular-complete-finite-field-regular` records closed-fibre regularity,
flat regular-local ascent, generic-fibre geometric regularity, and 0381 for arbitrary finite
extensions. Its Lean proof is complete. The item's copied DAG node records the actual
coefficient reduction and tensor transport. There are no change records or forced adaptations.

## Earlier second reading (a previous round; superseded)

1. Compared the existing module with the repository by `diff -u`, and compared its
   theorem signature byte for byte through `:= by`. Verdict: identical signature and
   existing docstring; only proof imports, a private quotient helper, and the proof changed.
   The other four modules and nodes are new. No existing definition or exported instance
   was changed; the `IntermediateField.module'` exclusions are declaration scoped.
2. Compiled all five modules in import order using `lcompile.py --all`. Verdict: no errors
   or warnings. Independently appended `#print axioms` in scratch copies for every public
   theorem: each uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is expected from the one construction hole and existing open ingredients.
   Checked the sole textual sorry is the whole proof of the named construction theorem;
   there are no forbidden declarations, hollow definitions, or data-producing definitions
   selecting arbitrary witnesses from open existence theorems. Scratch copies were removed.
3. Read the construction's signature, complete proof docstring, node, and imported
   ingredient declarations. Checked Stacks 07PM, 07PH and 07PL online. In particular 07PH
   permits finite type over any complete Noetherian local base; the imported extension
   lemma implements the general complete-adic dual-number argument, without locality of
   the finite tensor ring. Verified denominator scaling, non-pth-power preservation,
   finite integral generators, completeness, and the unit after localization.
   Edge cases: p = 2, an imperfect coefficient field, A a field, degree one (handled by
   the separate trivial-extension branch), and a zero tensor fibre. The zero ring has
   its unique element as a unit and its polynomial quotient is zero. Verdict: the
   construction is true and strictly one degree-p step, with no regularity assumption
   or conclusion; it does not restate the item. New leanfinder, loogle (`Derivation,
   IsUnit`) and grep searches, and searches of both project roots and upstream ring
   theory, found no combined adic-complete presentation theorem. The general construction
   requires substantial formal glue and cannot be closed in a few minutes.
4. Read proofs downward through coefficient reduction, finite-field regularity, degree
   induction, and the degree-p application. Verdict: the proof uses existing 07NQ,
   031E, 0381, 09HI and 07PG declarations, with Mathlib scalar/tensor/localization glue;
   no shorter applicable library theorem was found. Public imports provide signature
   notions; proof ingredients are plain imports. Construction imports retain the stated
   proof plan for its remaining hole. Checked `dag/units/sk-thm-p1.json` `realized`:
   none of its statement or step realizers is bypassed. No module is globally pruned.
   Completed the explicit list of removed old direct dependency nodes above.
5. Compared all five nodes' statements, Lean records, steps, dependency unions and
   origins with the code. Verdict: the four new nodes have the required source, search,
   creation, blueprint, chapter, unit and Lean fields; the existing node changes only
   `proof`, `proof_deps` and `proof_origin`. The sole unfinished construction has its own
   matching node. All described tensor equivalences and induction steps occur in Lean.

Changes made by the second reader: completed the old direct dependency-node list and
corrected the new degree-p module heading from power series to complete local algebras.
No theorem signature or proof was changed. The delivery remains a decomposition with
one original hole closed and one construction hole added, net zero, not an axiom-free proof.

## Second reading by J1

1. Compared the delivered item module with the repository version. The target theorem's
   signature and statement are byte-for-byte unchanged; only proof imports and proof text
   changed. The four helper modules and their nodes are new, as declared above.
2. Compiled all five modules with `lcompile.py --all`; compilation succeeds without warnings.
   The only `sorry` is the complete proof of
   `Algebra.exists_degree_p_presentation_unit_derivation_of_formallySmoothAdic`, and no
   forbidden declarations or hollow definitions occur. The proved declarations use only
   the permitted foundational axioms, modulo the explicitly open imported ingredients.
3. Checked the new construction statement on degree p, p = 2, fields, imperfect fields,
   and zero tensor fibres. It is a strictly smaller construction step and does not assert
   regularity; its source proof and node are recorded. Searches found no existing theorem
   combining these hypotheses and conclusion.
4. Read the proofs from the coefficient reduction through the finite and purely inseparable
   cases. Their routes use the imported declarations and Mathlib tensor/localization glue,
   and preserve the unit route `sk-thm-p1`; no realized unit step is bypassed. Removed
   imports and dependency nodes are listed above.
5. Compared every delivered node's statement, Lean record, proof dependencies, source,
   chapter, and unit with the code. They agree; no statement or definition was changed.

I changed only this report section to satisfy the required second-reading heading; no Lean
proof or theorem signature was changed during this reading.
