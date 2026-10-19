## Worker report

The module `Sheaf.AlgebraicGeometry.GenericConstancyGeometricReducedness` states
`AlgebraicGeometry.exists_nonempty_open_geometricallyReduced_fiber_iff_generic`.
Its only proof is `sorry`; no definition or additional theorem is introduced. The node
changes only in `lean`.

The source read is `literature/stacks-project/more-morphisms.tex`, the complete statements
and proofs labelled `lemma-not-geometrically-reduced-in-neighbourhood` (Tag 0577) and
`lemma-geometrically-reduced-generic-fibre` (Tag 0578), and the following Tag 0579 proof.
The former two assume finite type, irreducibility, and the respective generic-fibre
alternative; their combination gives exactly the node after qc + lfp implies finite type.
The module docstring carries both steps of the node's proof, including their node ids.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`. The universe `u` is
  explicit and arbitrary; no restriction on the underlying schemes is introduced.
- Quasi-compactness: `[QuasiCompact f]`.
- Local finite presentation: `[LocallyOfFinitePresentation f]`. There is no
  quasi-separatedness hypothesis or bundled finite-presentation hypothesis.
- Irreducible base: `[IrreducibleSpace Y]`, which includes nonemptiness, as the node does.
- Given generic point: `(η : Y) (hη : IsGenericPoint η Set.univ)`. This states that the
  singleton closure is all of the base, without replacing η by a chosen point.
- An open subset of Y: `∃ V : Y.Opens`.
- Its nonemptiness: `(V : Set Y).Nonempty`.
- Every point of that open: `∀ y : Y, y ∈ V →`.
- The scheme-theoretic fibre over its own residue field is rendered by
  `f.fiberToSpecResidueField y : f.fiber y ⟶ Spec (Y.residueField y)`.
  `fiber` is the pullback of f along `Y.fromSpecResidueField y` and this structure map
  is its second projection, so the geometric property uses the specified base field.
- Geometric reducedness agrees with the generic fibre: the conclusion is
  `GeometricallyReduced (f.fiberToSpecResidueField y) ↔
  GeometricallyReduced (f.fiberToSpecResidueField η)`.
  An iff expresses both truth values; no assumption on the generic fibre is added.
- No flatness, reducedness of Y, Noetherianity, or nonemptiness of any fibre is assumed.

Dependency declarations and source signatures/docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  the scheme structure extends a locally ringed space with affine neighbourhoods and
  morphisms are locally ringed space morphisms.
- The convention node `def-weil-pbc-scheme-conventions` defines no notion of its own.
  Its quasi-compactness reference is `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, used directly. Its all-compact-open
  formulation is equivalent to the recorded affine-open formulation.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, with finite-presentation condition
  on induced maps for affine pairs. This is the dependency's recorded match.
- `Mathlib.Topology.Irreducible`: `IsIrreducible`, `IrreducibleSpace`,
  `irreducibleComponents`. Only irreducibility of the whole base is used, via
  `IrreducibleSpace Y`; nonempty and the closed-cover criterion are its recorded notion.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, defined by `closure {η} = Set.univ`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField`, the recorded dependency declarations.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, the residue field
  of the stalk, occurs as the target field of the fibre structure map.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`, the module recorded by
  `def-pc-geometrically-irreducible`, publicly imports
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced` and its
  `AlgebraicGeometry.GeometricallyReduced`: every base change to a field is reduced.
  Applied to the fibre structure map this is exactly geometric reducedness over κ(y).
- Proof dependency `def-weil-finite-type-morphism` uses `LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact`; these are reached
  through the finite-presentation and quasi-compact imports. The two statement proof
  dependencies `lem-trf-generic-fibre-geometrically-reduced-open` and
  `lem-trf-generic-fibre-not-geometrically-reduced-open` currently have no Lean record
  or Mathlib match. They are named in the proof docstring, with no nonexistent module
  import. Neither is needed to state this theorem.

Edge cases checked mathematically before drafting:

- Empty X, hence empty fibres: those fibres are geometrically reduced; the positive
  alternative applies, and there is no nonempty-source restriction in the signature.
- Empty Y is excluded by the node's irreducibility hypothesis, exactly as by
  `IrreducibleSpace Y`, rather than by any added binder.
- Identity over an irreducible nonreduced base: every fibre is its residue-field
  spectrum and is geometrically reduced; reducedness of the base is unnecessary.
- A constant family `Spec(k[ε]/ε²) → Spec k` gives the negative generic alternative,
  which the iff includes without any positivity assumption.
- In characteristic p, `x^p=t` over `Spec k[t]` has a non-geometrically-reduced generic
  fibre; the negative alternative is retained. No characteristic is excluded.
- Non-Noetherian irreducible bases and morphisms lacking quasi-separatedness are
  admitted by exactly the stated hypotheses; local finite presentation plus qc is
  used, rather than strengthening to finite presentation.

Searches, made with the prescribed `msearch.py Q105 <item>` wrapper:

- LeanFinder query: "For a quasi-compact locally finitely presented morphism to an
  irreducible scheme, geometric reducedness of fibres agrees with the generic fibre
  on a nonempty open". Eight hits, on the reducedness definitions, integral schemes,
  and generic-point functoriality; none asserts generic fibre-property constancy.
- Loogle query: `AlgebraicGeometry.GeometricallyReduced,
  AlgebraicGeometry.LocallyOfFinitePresentation`. Zero hits.
- Mathlib grep query: `generic.*[Rr]educed|[Rr]educed.*generic|0577|0578`, in
  `AlgebraicGeometry`. One hit in `Properties.lean` about stalks at generic points
  of a reduced scheme, not fibre-property constancy.
- LeanSearch query: "Geometric reducedness of fibres is generically constant for a
  finite type morphism over an irreducible scheme". Eight hits, on geometric
  reducedness of algebras, fibre construction, and elementary reducedness properties;
  no exact statement.
- `rg` for `generic.*[Rr]educed|[Rr]educed.*generic` and the exact item id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared `lean/Sheaf`:
  upstream has no match; side modules concern other generic-reducedness statements
  or cite this item in proof docstrings. In particular `GeometricallyReducedFibreLocus`
  calls for this lemma but does not state it. The same concept search in
  `dag/lean_names_upstream.json` has no match.

No statement correction, new node, unusable dependency, or statement dispute was found.

Validation: the prescribed scompile.py wrapper compiled this file separately both as
sandbox and library module, with no errors or warnings (1.6 s and 2.0 s respectively).

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
