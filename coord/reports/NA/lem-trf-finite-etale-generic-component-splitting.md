## Worker report

States `AlgebraicGeometry.exists_finite_etale_generic_component_splitting` in
`Sheaf.AlgebraicGeometry.FiniteEtaleGenericComponentSplitting`. Its sole proof is `sorry`.
Source: Stacks Project, Tag 0551, more-morphisms.tex lines 6771–6830, read together
with the field splitting in Tag 054R and reducedness ascent in Tag 025O.
The node's statement is unchanged. No new nodes or dependency repairs are needed.

Hypothesis and clause correspondence:

- Integral Noetherian base T: `{T : Scheme.{u}} [IsIntegral T]
  [IsLocallyNoetherian T] [CompactSpace T]`. The last two are precisely locally
  Noetherian and quasi-compact, as the node explicitly defines Noetherian;
  Mathlib's `IsNoetherian` has exactly those two superclass fields.
- Arbitrary scheme X and finite type f: `{X : Scheme.{u}} (f : X ⟶ T)
  [LocallyOfFiniteType f] [QuasiCompact f]`, the conjunction in the dependency record.
- Nonempty affine open U of T: `∃ U : T.Opens, (U : Set T).Nonempty ∧ IsAffineOpen U`.
- Integral affine scheme S: `∃ S : Scheme.{u}, IsIntegral S ∧ IsAffine S`.
- Finite étale surjective π: `∃ π : S ⟶ U.toScheme, IsFinite π ∧ Etale π ∧ Surjective π`.
- Generic point ξ of S: `∃ ξ : S, IsGenericPoint ξ Set.univ`. Integrality gives existence;
  a scheme is sober, so the point is unique. Explicitly exhibiting it rather than using
  a choice of `genericPoint` changes no mathematical requirement.
- Pullback family X ×_T S over S: `pullback f (π ≫ U.ι)` with structure map
  `pullback.snd f (π ≫ U.ι)`. Its scheme-theoretic generic fibre is
  `(pullback.snd f (π ≫ U.ι)).fiber ξ`.
- Every irreducible component: `∀ A ∈ irreducibleComponents
  ↥((pullback.snd f (π ≫ U.ι)).fiber ξ)`.
- Geometric irreducibility over κ(ξ): for every `(E : Type u) (_ : Field E)` and
  `(z : Spec (CommRingCat.of E) ⟶ Spec (S.residueField ξ))`, take the inverse image
  of A under `pullback.fst ((pullback.snd f (π ≫ U.ι)).fiberToSpecResidueField ξ) z`
  and require `IsIrreducible`. This is precisely irreducible AND nonempty:
  `IsIrreducible` is defined as `s.Nonempty ∧ IsPreirreducible s`.
  A spectrum map between fields is contravariantly a unital field embedding,
  so quantifying z is quantifying every field extension with its specified base map.
  This is the explicit subset formulation used by the recorded field splitting theorem,
  and the field-extension characterization of the imported geometric irreducibility class.
- No properness, flatness, reducedness, or dimension hypothesis is imposed on X/T.
  No condition asks the generic fibre to be inhabited. The generic fibre can be empty.

Dependency declarations used, read at their definitions and docstrings:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`,
  `Scheme.Hom.fiberToSpecResidueField` (and its canonical projection `fiberι`).
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`; affine opens and their
  open subschemes use the existing `IsAffineOpen`, `Scheme.Opens.toScheme` and `ι`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.snd`, `pullback.fst`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, `IsIrreducible`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` imports the dependency's
  `GeometricallyIrreducible`; the statement expands its field-extension test on each
  component subset, without defining a second predicate or introducing a component scheme.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.

Proof dependencies already stated are imported: `GenericComponentsSplit`
(`exists_finite_etale_geometric_component_extension`), `SpreadFiniteSeparableExtension`
(`exists_spread_finite_separable_extension`), and upstream
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale` (`isReduced_of_etale`).
The Mathlib proof leaves are provided by the imported affine, finite type, Noetherian,
residue-field, formally unramified, pullback and prime-spectrum topology modules.
The declaration docstring carries all six steps of the DAG proof.

Edge cases checked: X empty or nondominant (the generic fibre and component set can
be empty, so the final universal assertion is vacuous); T the spectrum of a field
(the field component-splitting lemma applies directly); nonreduced X and inseparable
behaviour (only topological irreducibility is required, with no geometric reducedness);
all characteristics, including positive characteristic; identity field extension z
is included. Empty T is excluded exactly by `IsIntegral T`, and empty S by `IsIntegral S`.
All schemes and test fields share the ambient universe u, the standard Mathlib geometric
property convention; no smaller independent test-field universe is used.

Searches made for an existing statement:

- msearch.py LeanFinder: “A finite type family over an integral Noetherian scheme has
  geometrically irreducible generic fibre components after a finite etale surjective
  integral affine cover of a nonempty affine open”. Eight hits, including
  `finite_irreducibleComponents_of_isNoetherian`, `IsIntegral`, and fibre finiteness;
  none constructs the asserted finite étale cover.
- msearch.py Loogle: `AlgebraicGeometry.Etale, AlgebraicGeometry.GeometricallyIrreducible`:
  zero hits.
- msearch.py grep: `generic.*component|component.*geometric|finite.*separable.*extension`
  in AlgebraicGeometry: three hits in Geometrically/Reduced, Connected, Irreducible.
  Read the relevant definitions: they give properties or component equivalences for
  already geometrically irreducible maps, not this splitting cover.
- rg over upstream WeilConjectures and project lean/Sheaf with the same expression:
  generic-component and field-extension tools, no exact open-base splitting theorem.
  Read `GenericComponentsSplit`, `SpreadFiniteSeparableExtension`,
  `GeometricGenericCoverSpread` and `GeometricGenericCoverModel`:
  the former two supply separate steps, the latter ones spread supplied closed covers.
- rg for the item id in upstream WeilConjectures: no occurrence.
- rg for `FiniteEtaleGenericComponentSplitting` and
  `exists_finite_etale_generic_component_splitting` in upstream, project Lean and
  dag/lean_names_upstream.json: no occurrence before writing this declaration.

The previous worker's stale-dispatch diagnosis confused stage-1 `reviewed` with a
stage-2 `lean`/`reviewed_lean` record. The current node has a reviewed stage-1 split
and no Lean statement, so stage 2 is the assigned next work. No stage-1 split is changed.
No STATEMENT-DISPUTED or statement fault was found.

Validation: the first scompile run elaborated the statement in both sandbox and library
contexts and reported only a long-line warning. That line was split without changing
the statement. The clean rerun and delivery preflight are recorded by the delivery tool.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
