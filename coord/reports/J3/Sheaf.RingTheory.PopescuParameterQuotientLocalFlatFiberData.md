## What changed

The unchanged theorem `Algebra.parameter_quotient_local_flat_fiber_data` now has a
complete Lean proof from the regular-local parameter lemmas, a proved generic
localized quotient-flatness lemma, a proved separable ind-smooth transport lemma,
and one new residue-identification statement. Private proved helpers identify the
polynomial origin and apply `RingHom.flat_of_regular_parameters` to `List.ofFn`.
All added imports used only by proofs are non-public. No existing signature,
definition, visibility, target, or other group's module was changed.

`Sheaf.RingTheory.FlatLocalizedQuotient` proves
`RingHom.flat_localized_quotient_of_flat_localRingHom` directly from Mathlib:
compose flat localization, quotient tensor base change, quotient/localization
identification, and `Module.flat_iff_of_isLocalization`.

`Sheaf.FieldTheory.SeparableIndSmoothTransport` proves
`Algebra.ind_smooth_of_separable_ringEquivs`: an explicit diagram of lifted smooth
subalgebras, its colimit in types, its ring/algebra universal property, smoothness
under the base isomorphism, and transport along the target equivalence.
The local private colimit-reflection helper follows the already proved helper in
`Sheaf.RingTheory.FilteredColimitSmoothProduct`, generalized only by instantiating
its existing universe-polymorphic signature. That module is not imported.

`Sheaf.RingTheory.PopescuParameterQuotientResidueEquivs` states only the compatible
residue ring identifications. It omits regularity, dimension, Noetherianity and
separability, and asserts neither flatness nor ind-smoothness. This is strictly the
geometric identification step, rather than either clause of the item's conclusion.
Existential equivalences are eliminated inside a theorem proof, never used to
choose data for a definition. All original and new modules compile together.

## Proved and sorry left

Closed the item's one original hole:
`Algebra.parameter_quotient_local_flat_fiber_data`.
Added one hole:
`Algebra.parameter_quotient_residue_ringEquivs`
(node `lem-weil-pbc-popescu-parameter-quotient-residue-equivs`).
There are no other sorries in the four delivered modules.
This is a decomposition with net zero holes, with flatness and the entire
categorical transport argument proved; it is not a claim of sorry-free closure.
The two new proved public declarations are
`RingHom.flat_localized_quotient_of_flat_localRingHom` and
`Algebra.ind_smooth_of_separable_ringEquivs`.

The remaining geometric lemma was checked in dimension zero (P=k and Λ_q a
field), for c=1, arbitrary positive c, and arbitrary field characteristic.
The existence of q₀ excludes a unit powered ideal. Generation alone identifies
the closed fiber, so regularity and separability are legitimately absent from
that lemma. Arbitrary transcendental separable extensions remain allowed in the
ind-smooth transport lemma; no finite-degree hypothesis was added.

## No longer needed

Removed the direct proof import `Sheaf.FieldTheory.SeparableSmoothColimit` from
the item. It remains needed through `Sheaf.FieldTheory.SeparableIndSmoothTransport`
(node `lem-kun-separable-smooth-colimit`), so it is not globally pruned.
Also removed the redundant direct proof import
`Mathlib.RingTheory.Flat.Stability` from the item; it is already public through
`Mathlib.RingTheory.RingHom.Flat`. Removed redundant proof imports
`Mathlib.RingTheory.Localization.Ideal` and `Mathlib.RingTheory.Flat.Stability`
from the new flatness module: its public imports already supply them.
No original proof-dependency node is claimed globally unnecessary: the three quotient/base-change dependencies now
occur below `lem-weil-pbc-flat-localized-quotient`, and the separable colimit node
occurs below `lem-weil-pbc-separable-ind-smooth-transport`.
The old item's separate commuting-square construction between two localized
quotients is unnecessary: flatness is descended to P/J first, then transferred
to its localization by Mathlib's localization-flatness equivalence.
The old dependency `lem-weil-pbc-filtered-colimit-algebras-elementwise` is no
longer used: its underlying forgetful colimit reasoning is proved in the
transport module. The old dependencies
`lem-weil-pbc-localization-at-prime-of-quotient`,
`lem-weil-pbc-tensor-quotient-base-change`, and
`lem-weil-pbc-flat-module-quotient-flat` are now used through the new flatness
node (all three are Mathlib leaves);
`lem-kun-separable-smooth-colimit` is used through the new transport node.
These are all five old dependencies absent from the item's new direct list.
Whether those nodes remain globally reached is the maintainer's closure check.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The planned quotient square was a
longer route than necessary, and the ring-colimit theorem alone does not supply
the required algebra-colimit or universe transport: those are now explicit Lean.
The local checkout lacks the untracked Stacks source file. The final paragraph
of Stacks Tag 07FE was read at https://stacks.math.columbia.edu/tag/07FE.
LeanSearch returned Internal Server Error; it is recorded as unavailable, not
as a failed mathematical match. The unit's realized statement and steps are
unaffected; this item is below the unit level.

## New nodes

`lem-weil-pbc-flat-localized-quotient` records the proved generic descent of local
flatness to localized quotients, in `Sheaf.RingTheory.FlatLocalizedQuotient`.

`lem-weil-pbc-separable-ind-smooth-transport` records the proved categorical and
universe transport from compatible field identifications, in
`Sheaf.FieldTheory.SeparableIndSmoothTransport`.

`lem-weil-pbc-popescu-parameter-quotient-residue-equivs` records the one remaining
geometric identification step, in
`Sheaf.RingTheory.PopescuParameterQuotientResidueEquivs`. Its docstring gives the
full proof using prime contraction, the origin quotient, localization of
quotients, maximal-ideal generation, and compatibility on constants/inverses.
No change record is required because no existing interface was changed.


## Second reading by J3

1. Interfaces: compared the item's complete diff against the repository version.
   The existing theorem signature is byte for byte identical, as verified using
   the declaration parser; no existing declaration was removed, no definition
   or visibility changed, and there are no forced adaptations. The other three
   modules are new. Verdict: pass.
2. Proofs: compiled all four modules in import order with `lcompile.py --all`.
   Scanned their full sources for forbidden declarations and data holes. The
   sole direct sorry is `Algebra.parameter_quotient_residue_ringEquivs` and has
   its own module, node, source and full proof docstring. Explicit `#print axioms`
   checks gave just `propext`, `Classical.choice`, `Quot.sound` for the generic
   flatness lemma, and those plus `sorryAx` for the item, residue lemma and
   transport lemma, because their import closures still contain open statements.
   The private colimit construction uses a proved universal property; its
   choice of an index establishes the scalar law and does not choose an
   arbitrary object from an unproved existence theorem. Verdict: pass, a
   decomposition with one hole closed and one added, net zero.
3. Split statement: read the residue lemma and its full geometric argument.
   Contraction forces the polynomial-origin prime, and the parameter-generation
   equality identifies the extended maximal ideal with the target maximal ideal.
   Quotient/localization and the third isomorphism theorem then give exactly
   the stated compatible residue equivalences. Checked d=0, d=1, c=1, larger
   powers, arbitrary characteristics and non-Noetherian target rings. Neither
   regularity nor separability is required for this identification. This lemma
   asserts neither flatness nor ind-smoothness and is strictly a part of the
   original proof. Independent LeanFinder, Loogle and grep searches used
   maximal-ideal and closed-fiber language, and `rg` covered both library roots.
   `IsLocalization.AtPrime.equivQuotMaximalIdeal` handles a component but not the
   parameter-generated fiber and compatibility together; no existing complete
   result was found. Closing this hole requires substantial explicit quotient
   and scalar-map constructions, rather than a short application. Source checked:
   [Stacks 07FE](https://stacks.math.columbia.edu/tag/07FE) and
   [Stacks 07BV](https://stacks.math.columbia.edu/tag/07BV). Verdict: pass.
4. Route and pruning: read the regular-local, flatness and separable-colimit
   dependencies and the new proofs from the item downward. The generic flatness
   proof uses Mathlib base change and localization directly. The explicit
   algebra-colimit proof avoids invoking any stronger Popescu result or cycle.
   Removed redundant proof imports and recompiled the entire delivered set.
   The No longer needed section now enumerates every old direct dependency
   omitted from the new list. Inspected `dag/units/sk-thm-p1.json`: none of the
   changed nodes realizes its statement or steps; its realized route is kept.
   No module is claimed globally pruned. Verdict: pass.
5. Nodes: matched all four recorded Lean signatures against their modules;
   checked that each `proof_deps` equals the union of its steps' `uses`, that the
   steps describe the actual declarations/Mathlib leaves used, and that all
   three new nodes have source, searches, creation, blueprint, chapter, unit
   and Lean records. The item changes only stage-3-owned node fields.
   Verdict: pass.

Second-reading changes: removed the item's redundant `Flat.Stability` import,
removed the new flatness module's redundant `Localization.Ideal` and
`Flat.Stability` imports, and made the dependency-pruning report explicit.
No mathematical statement or proof argument needed repair.
