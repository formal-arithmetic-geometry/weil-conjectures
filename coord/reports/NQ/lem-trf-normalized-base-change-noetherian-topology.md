## Worker report

The module defines `AlgebraicGeometry.normalizedClosure` as the normalization of the reduced closed subscheme cut out by the closure of a point, and `normalizedClosureMap` as its canonical composite to the ambient scheme. It states `noetherianSpace_normalized_baseChange` with the exact hypotheses of the node: a locally Noetherian and quasi-compact base `S`, a finite-type morphism `f` (rendered by `[LocallyOfFiniteType f] [QuasiCompact f]`), and a point `s : S`; its conclusion is `TopologicalSpace.NoetherianSpace` for the scheme pullback along `normalizedClosureMap s`, equivalent to the minimal-closed-subset formulation.

The reduced closed subscheme is rendered by `Scheme.IdealSheafData.vanishingIdeal ⟨closure ({s} : Set S), isClosed_closure⟩`; its integrality is supplied by `Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure`. Normalization and its map are `Scheme.normalization` and `Scheme.fromNormalization`; fibre product is `CategoryTheory.Limits.pullback (C := Scheme)`. The theorem proof is intentionally `sorry`, with the node proof route recording the Heinzer and finite-type Noetherian-spectrum arguments for stage 3.

Edge cases checked: `s` may be any point, including closed or generic points; the closure may be the whole scheme or a singleton; no finiteness of normalization or Noetherianity of its ring is added; zero and empty affine charts are handled by the source proof route. The theorem uses only topological Noetherianity.

Searches: `msearch.py ... leanfinder "reduced closed subscheme closure scheme normalization residue field"` found only residue-field and generic normalization declarations, with no exact theorem. `msearch.py ... loogle "Scheme, closure, reduced, closed immersion"` returned no hits. `rg` over Mathlib and WeilConjectures for closure/reduced/normalization/noetherian found the existing reduced-closure integrality helper and normalization definitions, but no statement of this theorem.

## Second reading by NQ

Independent maintainer reading of immutable delivery 0789b7987b104ab6745b494a55aeddf8bb6ccd82,
2026-10-18. This section replaces the delivered placeholder; the independent reviewer did
not write or previously second-read the delivery.

Clause audit:
- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`; arbitrary universe `u`, all
  binders explicit. No field, characteristic, separatedness or dimension assumption.
- Noetherian base: `[IsLocallyNoetherian S] [CompactSpace S]`, exactly local
  Noetherianity and quasi-compactness, with no Hausdorff requirement.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the pair recorded
  by `def-weil-finite-type-morphism`, without finite presentation or properness.
- Arbitrary point: `(s : S)`, with no closed-point or generic-point restriction.
- Reduced closed closure: `vanishingIdeal ⟨closure ({s} : Set S), isClosed_closure⟩`
  and its existing `subscheme`; the vanishing ideal is radical and the subscheme
  immersion is closed. Existing `isIntegral_subscheme_vanishingIdeal_closure s`
  supplies integrality for an arbitrary scheme, with no field assumption.
- Normalization: `J.subscheme.normalization` is the recorded normalization in its
  function field, defined by normalizing the generic-point map. The generic stalk of
  this integral reduced closure is canonically κ(s): the closed-immersion stalk map
  is a surjection from the ambient local ring onto a field. Its kernel is the maximal
  ideal. Thus the function field is precisely the field required by the item.
- Canonical map: `J.subscheme.fromNormalization ≫ J.subschemeι`; real construction,
  no arbitrary morphism or choice from a bare existence assertion.
- Fibre product: `CategoryTheory.Limits.pullback (C := Scheme) f (normalizedClosureMap s)`.
- Conclusion: `TopologicalSpace.NoetherianSpace` for this underlying Zariski space;
  Mathlib's `noetherianSpace_TFAE` and `WellFoundedLT (Closeds _)` identify this with
  the minimal-closed-member formulation. No ring Noetherianity of the normalization,
  excellence, or finite normalization is assumed or concluded.
All clauses agree. The node's `lean.statement` equals the theorem signature verbatim.

Dependency declarations read: Mathlib `IsLocallyNoetherian` (Noetherian:57),
`CompactSpace` (Topology.Defs.Filter:283), `IsClosedImmersion` (Morphisms.ClosedImmersion:45),
`IsReduced` and `IsIntegral` (Properties:69,240), `LocallyOfFiniteType` and `QuasiCompact`
(Morphisms.FiniteType:43, Morphisms.QuasiCompact:43), `Scheme.residueField` and
`Hom.residueFieldMap` (ResidueField:45,123), and `Limits.pullback` (HasPullback:95).
Read the actual `Scheme.normalization` and `Scheme.fromNormalization` in
WeilConjectures.Mathlib.AlgebraicGeometry.Normalization:185,191 and the closure-integrality
instance in WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial:97, including
its surrounding binders. The field variables earlier in that file are not dependencies
of this instance. Read the finite-type spectrum theorem in
Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum; it is general in both ring universes.

Source check: Orgogozo's author PDF, printed p. 18, Lemma 8.3.2 and its proof, in particular
the final finite-type alternative (PDF page index 17), explicitly uses Heinzer's
normalization-spectrum fact separately from the excellent/finite-normalization alternative.
Stacks properties.tex definition-noetherian and lemma-Noetherian-topology, the integral
scheme definition and reduced/irreducible characterization, and morphisms.tex finite-type
definition agree with the hypotheses and the affine-cover argument. Read all five node
proof steps against the source and the proposed formal statement.

Edge cases: empty X and empty pullback are allowed; empty S has no point s, exactly as in
the item. Nonreduced S, closed/generic/intermediate points, whole-space closures and
singleton closures, zero chart rings and empty charts are allowed. Empty source affine
covers contribute no charts. Degree-one normalization uses no separability hypothesis.
No assumption on dimension, residue characteristic or normalization finiteness appears.
The single arbitrary universe u is the ordinary Scheme category convention, not a hidden
identification of independently sized sites or coefficient categories.

Independent searches: rg for normalizedClosure, closure/normalization, and
normalization/Noetherian in Mathlib, upstream WeilConjectures, the group's side framework
and lean/Sheaf found no duplicate of the new theorem or helper composite. The existing
normalization and reduced-closure constructions are reused. The nearby
normalization_in_finite_residue_field_extension is an existence/factorization theorem,
not this chosen composite or the topological Noetherianity assertion. Worker searches
also record LeanFinder, Loogle and grep with results. No missing definition or unusable
statement-dependency interface requires §1(A)/(B); no §1(C) correction is needed.

Findings repaired mechanically:
- H8: helper docstrings lacked source places and the theorem lacked the five proof steps.
  Added sources and a complete step-by-step proof plan with dependency ids.
- H11: the second-reading section was only a disclaimer. Replaced it with this actual
  independent clause audit, keeping the Worker report intact.
- H9: added the non-public import of the already stated proof dependency
  Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum. The other non-definition proof
  inputs have no recorded Lean module in the inspected group clone; they are not needed
  to type the statement and have not been invented as extra assumptions.
The theorem signature, definitions' data, and node record are unchanged.

Compilation: the immutable module was reproduced with scompile.py NQ
lem-trf-normalized-base-change-noetherian-topology and its snapshot path: exit 0,
sandbox 2.9 s, library 3.8 s, no warnings/errors. The installed prescribed wrapper is
server-overlay-only (2026-10-17) despite the older local-overlay help in the brief;
its output identifies private /dev/shm compilation, not a global build. The corrected
module was checked under its actual library name through the same wrapper: exit 0,
sandbox 3.7 s, library 2.9 s, no warnings/errors. There is exactly one delivered theorem proof, `by sorry`, and no
sorry in helper data. No repository, branch head or live Lean file was edited, and no
lake/global build or delivery/merge command was run.

Route pivot: intersection of all statement/proof dependency ids with the current
route-pivot-dropped list is empty. There is no repair note for this item, no enhanced,
Quillen, operadic or pro-etale substitute, and no pivot-specific machinery to retain.
