## What changed

Proved the body of AlgebraicGeometry.Scheme.exists_smooth_closed_point_local_section
without changing its signature or public imports. Added the proof-only imports
SmoothClosedPointFiniteFlatLift and WeilConjectures.AlgebraicGeometry.Morphisms.Slicing. The new finite flat lift
is strictly the residue-extension step: it asserts no slice, section, or singleton fibre.
The original theorem constructs B as the actual stalk of the etale slice, constructs s
by composition, and extracts the actual ring map from that constructed spectrum map.
Existential witnesses are eliminated inside a proof; no data definition is chosen from
an unproved existence theorem.

The source proof of Stacks Tags 0EYB, 07NE and 057G was read on the Stacks website.
The unit sk-prop-input-spreading has empty realized lists; its completion route is retained.
All sandbox modules compile in import order. Existing closed source declarations for
slicing and flat canonical stalk maps receive precise new DAG attachments.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.exists_smooth_closed_point_local_section
(lem-sbc-smooth-closed-point-local-section).

Added one hole:
AlgebraicGeometry.Scheme.exists_smooth_closed_point_finite_flat_lift
(lem-sbc-smooth-closed-point-finite-flat-lift).
Its proof is exactly `:= by sorry` and its docstring gives the source and complete argument.
This is a decomposition, with zero net holes removed, not a completed proof of the
residue extension. The etale-slice, stalk-localization, flat/local composite,
singleton-fibre argument, base equation, and prescribed closed-point equality are proved.
No other sorries are left in the delivered files.

## No longer needed

No original import or dependency module was removed; none can be claimed globally pruned.
The exploratory direct import of
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite was removed: the proof
uses Mathlib discreteness directly, and the etale quasi-finiteness instance is already
available from Slicing's imports. No need to use its coheight theorem, the full
Smooth.exists_etaleCover_factorization theorem (sbc-lem-slicing), or the relative
connected-component theorem (lem-sbc-smooth-section-component-geometrically-irreducible).
Slicing still loads those modules transitively; this delivery does not claim to prune them.

The second reading removed the redundant direct proof import
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat: it is already publicly
imported by Slicing through the source Smooth module. Its flatness instance is
still used, so lem-sbc-canonical-stalk-spectrum-flat remains a proof dependency.
No original dependency was pruned (the original proof_deps list was empty).

## Where the brief, the DAG or earlier work was wrong

The item's proof_deps was empty despite a non-elementary construction. It now names
the residue lift and the two existing source declarations actually used. The broad
flat-local prescribed-residue-field extension in Sheaf.RingTheory.FlatLocalExtensionGivenResidueField
cannot supply this step: it gives neither finiteness nor Noetherianity. The etale slice
in the source library was already proved, so leaving a new slice hole was unnecessary.
No statement change or forced adaptation was necessary.

Edge cases checked: a nonempty chosen fibre point is the only nonemptiness required;
no perfectness or separability of its original residue extension is assumed. A field
base and a zero-dimensional smooth fibre are included. A local noetherian stalk of
the slice exists because the slice is locally of finite type over A'. The singleton
fibre uses quasi-finiteness of the localized etale map and finiteness of A' over A,
not an unjustified claim that an arbitrary flat local map has singleton fibre.

## New nodes

lem-sbc-smooth-closed-point-finite-flat-lift: the one new holed module,
Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointFiniteFlatLift, performs only the
finite flat residue-field lift and produces a separable point for the existing slice.

lem-sbc-smooth-separable-point-etale-slice: attaches the existing proved
AlgebraicGeometry.Smooth.exists_etale_comp_of_etale_residueFieldMap in Slicing;
no new Lean declaration or hole. Its signature was read and used unchanged.

lem-sbc-canonical-stalk-spectrum-flat: attaches the existing proved instance
AlgebraicGeometry.Scheme.flat_fromSpecStalk; no new Lean declaration or hole.
It is a tool from the local spectrum localization argument. The narrower result
already exists in the source library, so it is not reproved via the much broader
canonical-local-spectrum-and-module-pullback statement of the other unit.

Searches for each new attachment used LeanSearch (unavailable: internal server error),
LeanFinder, and Mathlib/source grep; the node records preserve these results. The
DAG and blueprint searches found no exact duplicate of the finite flat lift or the
separable-point slice. The new canonical-stalk-flat attachment is the narrow existing
source instance, not a second construction of the canonical local spectrum.

## Second reading by W4

1. Compared both delivered modules with the repository: the finite-flat-lift module
   is new; the existing theorem signature is byte-for-byte identical, with no
   definition or visibility change. Original public imports are unchanged. The
   original correct docstring was restored. No change record is needed.
2. Compiled both modules in import order with lcompile.py, without errors or
   warnings. The sole direct sorry is the named finite-flat-lift theorem reported
   above. Scratch-copy #print axioms checks of both delivered theorems returned
   propext, Classical.choice, Quot.sound and sorryAx. The existing slice and stalk
   flatness declarations were also checked. No forbidden declarations or data
   definitions occur. B is the actual stalk, not data selected by an unproved
   existence theorem; existential ring and point witnesses are eliminated inside
   the theorem proof.
3. Read Stacks [07NE](https://stacks.math.columbia.edu/tag/07NE),
   [0EYB](https://stacks.math.columbia.edu/tag/0EYB) and
   [057G](https://stacks.math.columbia.edu/tag/057G). The split is true: successive
   monic quotients realize the finite residue extension; integrality makes the
   algebra local, and its rational fibre lift has an isomorphic residue map.
   Inseparable finite extensions are allowed. For a field base take that finite
   field extension itself; degree one permits the identity; an empty fibre has
   no input x; zero-dimensional smooth fibres are covered. The docstring gives
   the full construction and its properties. This split asserts no section or
   singleton fibre and is strictly part of the argument, not a restatement.
   Independent LeanFinder, Loogle and grep searches using finite-field-extension
   lifting and finite-free residue queries found no realization theorem. Checked
   the source smooth/local file and the tensor-product purely-inseparable local
   base-change theorem: neither handles an arbitrary local A and arbitrary finite
   residue extension. No quick closure of this remaining hole was found. The two
   other new nodes attach existing proved source declarations rather than adding
   duplicate Lean statements.
4. Read the reduction from the top: existing slice, Noetherian stalk, flat
   composition, local-hom TFAE, quasi-finite localization, discrete fibre and
   specialization, followed by pullback and closed-point equations. These prove
   all clauses of the original statement. Removed the redundant direct Flat
   import after a successful compile without it. No original import or proof
   dependency is abandoned, and no globally pruned module is claimed. Read
   sk-prop-input-spreading.realized (all lists empty); the item's local computation
   still follows the unit's finite-residue-lift and etale-slice route.
5. Compared the existing node JSON: only proof, proof_deps and proof_origin change.
   Its three dependencies match the lift, slice and stalk-flatness actually used.
   Read all new node fields, sources, search records and verbatim Lean statements.
   Their chapter, unit and blueprint ancestry agree with the original item.
   The closed declarations' attachment signatures agree with their source files.

Changes made by the second reader: restored the existing docstring; removed the
redundant direct Flat proof import; corrected the report's import list and added
this review. No mathematical proof body or theorem signature needed repair.
The delivery closes one original hole and adds one strictly smaller hole: a
one-for-one decomposition with zero net holes removed, not an axiom-free result.
