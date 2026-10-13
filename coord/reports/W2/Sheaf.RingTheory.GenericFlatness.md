## What changed

Completed and checked the existing sandbox proof of
`RingHom.exists_nonzero_flat_localizationAway` in
`lean/Sheaf/RingTheory/GenericFlatness.lean`, without changing its signature or visibility.
Three fully proved private helpers construct a finitely presented torsion-kernel cover,
lift finite ideal generators through localization, and descend generic flatness through
a Noetherian approximation. The final proof identifies its flat localization with every
localization model in the conclusion using an explicitly proved bijective ring map.

Proof-only imports use the proved source-library modules
`WeilConjectures.Mathlib.RingTheory.FinitePresentation` and
`WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`, plus Mathlib torsion-freeness. Polynomial localization and ideal results are available
through the retained source-library imports. The node proof now records
these steps and the use of flatness rather than freeness. Its three original definition
proof dependencies remain used. There are no new public interfaces or definitions.

## Proved and sorry left

Closed the sole original hole:
`RingHom.exists_nonzero_flat_localizationAway`
(node `lem-sbc-finite-type-algebra-generic-flatness`).
No holes remain in the module and no holes were added or split off.
This is a proof, not a decomposition. A single-file axiom check reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for the theorem. The three private
helpers are fully proved. The Lean file compiles cleanly.

## No longer needed

No original module import or DAG dependency was pruned. Removed redundant explicit
imports `Mathlib.RingTheory.Localization.BaseChange` and
`Mathlib.RingTheory.Localization.FractionRing` from the earlier sandbox draft;
the required declarations remain available through the retained imports.
Second reading also removed redundant proof imports
`Mathlib.RingTheory.MvPolynomial.Localization` and
`Mathlib.RingTheory.Localization.Ideal`; both are available transitively.
No Sheaf proof-dependency modules are needed beyond the existing Mathlib definition
leaves. All three original proof dependencies remain used, and the unit route is kept.

## Where the brief, the DAG or earlier work was wrong

The previous attempt ended without a report or dry run despite leaving a complete,
compiling proof in the sandbox. It is now checked and packaged.
The prose plan asks for freeness, but its kernel argument only requires torsion-freeness,
which follows from flatness over a domain. The existing proved generic-flatness theorem
therefore suffices. No mathematical statement or target was changed.


## Second reading by W2

1. **Interface: PASS.** Compared the entire delivered module with the repository
   using `diff -u`. The sole existing theorem's signature, universe, namespace,
   visibility and docstring are byte for byte unchanged. Both original public
   imports remain. Added imports are proof-only, and the three added helpers are
   private, proved theorems. There are no new definitions or interface changes,
   so no change record is required.
2. **Proof and axioms: PASS.** Independently compiled the module with lcompile.py.
   A fresh scratch copy of the current proof printed axioms for the public theorem
   and all three private helpers: each uses only propext, Classical.choice and
   Quot.sound. No sorry, axiom, unsafe, opaque, implemented_by, extern or hollow
   definition occurs. The quotient and localization are explicit constructions;
   all existential witnesses used in the proof come from proved theorems.
3. **Split statements and edge cases: PASS.** There are no split-off statements
   or added holes. Read all three private helper proofs. The finite ideal-lifting
   argument works for the zero ideal and an empty generating set; the polynomial
   presentation allows zero variables. Neither the cover nor the final proof
   assumes that the target is nonzero or that the initial map is injective.
   For the zero target, the localized cover is flat and its torsion kernel vanishes
   by the same argument, so the conclusion includes that case. R remains an
   arbitrary domain; only its descended finitely generated integer subalgebra is
   assumed Noetherian. The nonzero element stays nonzero by subalgebra inclusion.
4. **Route, search and imports: PASS after pruning.** Searched again with
   leanfinder for localization over a non-Noetherian domain, loogle for
   `Ideal.map, Ideal.FG`, and grep for subideal, torsion-cover and generic-flatness
   results; also searched lean/Sheaf and the source ring-theory modules. No exact
   shorter theorem was found. The proved source declarations
   Algebra.FinitePresentation.exists_fg_subalgebra_isPushout and
   Module.exists_flat_localizedModule_powers are used directly. Removing the
   torsion-freeness import fails to synthesize Module.IsTorsionFree; it is needed.
   Removed Mathlib.RingTheory.MvPolynomial.Localization and
   Mathlib.RingTheory.Localization.Ideal, then compiled with both removed.
   Their declarations are available transitively. No original imports or original
   proof_deps were removed. Read dag/units/sk-prop-normal-form.json: its existing
   realized slots are empty, and this delivery changes none of them or the unit's
   slicing route; this is a proof of its existing lower algebraic dependency.
5. **DAG: PASS.** Compared the node with the repository. Only proof and
   proof_origin change. The three proof steps accurately describe the finite
   relation cover, Noetherian approximation and flat base change, then the
   bijective localization map. The kernel dies because a flat module over R is
   torsion-free, with no freeness hypothesis used. proof_deps is exactly the union
   of the three steps' uses and retains the original three definition leaves.
   The recorded Lean signature matches the unchanged theorem. No new node files
   or new public statements are delivered.

Second reading changed only two redundant proof imports and this report. No proof
repair was necessary. Closed: RingHom.exists_nonzero_flat_localizationAway (one
original hole). Added holes: none. Split off: none. Original dependency modules
pruned: none. The unchanged theorem docstring gives a valid freeness route; the
node and report correctly record the weaker flatness route actually formalized.
