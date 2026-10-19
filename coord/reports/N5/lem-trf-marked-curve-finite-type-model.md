## Worker report

This is a stage-2 delivery. The current node has a reviewed stage-1 split and no
Lean record. The previous worker's conclusion that the assignment was stale
confused the existing stage-1 split with the missing stage-2 statement. This packet
adds that statement and the missing definition of a multipointed relative curve.
The item's statement and proof are preserved verbatim; stmt_deps gains only
`def-trf-multipointed-curve`. No proof is supplied: the only theorem has `sorry`.

Source read: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
§1.2, §3.1 and Remark 3.1.1, and the opening of the proof of Theorem 1.5.
The source PDF was opened at
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf .
The definition in §1.2 explicitly includes full finite presentation, allows an
empty marking, and imposes neither properness nor separatedness on the curve.
The approximation in §3.1 and the opening of Theorem 1.5 give the finite-type
model route. The stronger smooth-generic hypothesis of this node is retained.

Hypotheses and conclusions, clause by clause:

- The integral qcqs base is `{S : Scheme.{u}} [IsIntegral S] [CompactSpace S]
  [QuasiSeparatedSpace S]`. Compactness gives a finite affine subcover, and the
  quasi-separated space predicate gives quasi-compact intersections of affines.
- The multipointed pair is `P : MultipointedCurve S`. Its schemes are `P.X, P.D`,
  its structural maps are `P.x, P.d`, and its closed marking is `P.i`.
  `P.comm : P.d = P.i ≫ P.x` says that the marking is over the base.
- Flatness is `flat_X : Flat x` and `flat_D : Flat d`.
  Full finite presentation is the three fields `lfp_X`, `qc_X`, `qs_X` and the
  corresponding `lfp_D`, `qc_D`, `qs_D`. In particular this is not merely local
  finite presentation. This follows the comparison clause of the recorded
  finite-presentation dependency and the stage-1 review of the item.
- Pure relative dimensions are `pure_X : ∀ t, (x.fiber t).IsPureDimension 1`
  and `pure_D : ∀ t, (d.fiber t).IsPureDimension 0`. The existing
  `Scheme.IsPureDimension` is reused; its component condition is vacuous on empty
  fibres. `closed : IsClosedImmersion i` gives exactly the closed marking.
- `η : S` and `hη : IsGenericPoint η Set.univ` specify the generic point of the
  integral base. This is a witness for its unique generic point, not a new
  mathematical restriction. Smoothness of `X_η` and etaleness of `D_η` are
  `hXη : Smooth (P.x.fiberToSpecResidueField η)` and the analogous `hDη : Etale ...`.
- The conclusion existentially supplies `T : Scheme.{u}` and `hT : IsIntegral T`.
  `ηT` with `IsGenericPoint ηT Set.univ` specifies its generic point.
- `s : S ⟶ T`, `IsDominant s` and `s η = ηT` give both the requested dominance and
  generic-point compatibility. Neither surjectivity nor finite type of s is assumed.
- `tZ : T ⟶ Spec (.of (ULift.{u} ℤ))` with `LocallyOfFiniteType tZ ∧ QuasiCompact tZ`
  is finite type over the integers. The universe lift is the canonical copy of ℤ,
  so it changes no arithmetic condition and avoids restricting all schemes to
  universe zero. No dominance over Spec ℤ is required; characteristic p is allowed.
- `P₀ : MultipointedCurve T` gives the full same kind of pair over T, including both
  finite-presentation conditions, both pure dimensions, and the closed immersion.
  Its generic smoothness and etaleness are explicit predicates on the structural
  morphisms of its scheme-theoretic generic fibres.
- `eX : P.X ≅ pullback P₀.x s` and `eD : P.D ≅ pullback P₀.d s` are the two required
  isomorphisms. Their equations with `pullback.snd` make them isomorphisms over S.
  The final equation
  `eD.hom ≫ pullback.fst P₀.d s ≫ P₀.i = P.i ≫ eX.hom ≫ pullback.fst P₀.x s`
  says they commute with the marking. Together these equations are exactly the
  isomorphism of pairs; no arbitrary comparison map replaces a canonical pullback.
- The original node includes a glossary of semistability and geometric-node
  completions. It does not assume or conclude semistability in this approximation
  theorem. Accordingly no semistability hypothesis, nodal conclusion, completion
  constraint, connectedness, separatedness or properness is added to the Lean.
  Those glossary sentences do not contribute propositions to this theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with its stalkwise equivalent.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; full finite presentation also uses the recorded
  `QuasiCompact` and `QuasiSeparated` notions from their respective modules.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` together
  with `QuasiCompact`, exactly as the finite-type node's recorded interface says.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Mathlib.AlgebraicGeometry.Fiber`:
  `Scheme.Hom.fiber` and `Scheme.Hom.fiberToSpecResidueField`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`,
  itself the recorded componentwise `topologicalKrullDim` definition. This reuses
  `def-weil-pure-dimension` instead of making a private pure-dimension predicate.
- Original glossary dependencies were also inspected: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, `AdicCompletion` in
  `Mathlib.RingTheory.AdicCompletion.Basic`, `MvPowerSeries` in
  `Mathlib.RingTheory.MvPowerSeries.Basic`, and geometric fibres as the recorded
  `pullback` along an algebraic-closure geometric point. Their notions are not
  redefined. The theorem itself only needs the ordinary generic fibre.

The theorem docstring carries all ten proof steps with the cited node ids.
Proof-only imports retain already-stated descent, fpqc and approximation tools.
The two unstated proof nodes `lem-trf-pure-relative-dimension-finite-stage` and
`lem-trf-semistable-marked-base-change` are not needed to *state* the theorem,
and have no module to import yet; no theorem about them is smuggled into a def.

Edge cases checked mathematically: D empty; X and D both empty; empty fibres over
some base points (no surjectivity of either structural map); identity models when
S already is finite type over ℤ; S in positive characteristic; a transcendental
extension of generic fields; reducible curve fibres with each component of dimension
one; and nonseparated curves. Each remains in the statement. The base itself is
nonempty because it is integral. A zero-dimensional component added to a curve
fibre fails `IsPureDimension 1`, as it should. Finite presentation includes QC and
QS even though separatedness is absent. All variables and universe u are explicit.

Searches actually run with msearch.py are retained in searches.jsonl. For the item,
LeanFinder queried “A flat finitely presented multipointed curve over an integral
qcqs scheme descends to an integral finite type scheme over the integers” and
returned integral-scheme and integral-morphism tools, no model theorem; Loogle
queried `"FinitePresentation"` and returned ring/algebra finite-presentation
lemmas, no such scheme theorem; grep queried
`multipointed|finite_type_model|marked.curve` in AlgebraicGeometry, with no hits.
For the new definition, LeanSearch queried “A multipointed curve is a flat finitely
presented curve with a flat finitely presented zero-dimensional closed marking”
and returned Flat, LocallyOfFinitePresentation and unrelated Weierstrass curves;
LeanFinder queried “flat finitely presented morphisms of pure relative dimensions
one and zero with a closed immersion marking” and returned Flat, smoothness and
preimmersion tools; grep queried `MultipointedCurve|multipointed|pure relative dimension`
and returned zero Mathlib hits. An earlier Loogle query of the expected constituent
names reported an unknown identifier, so it was not treated as evidence of absence.
Direct rg of the upstream WeilConjectures source and shared lean/Sheaf source found
no multipointed definition or theorem and no item-id occurrence. A DAG search
found only statement nodes defining the term inline. blueprint_refs.py search
“multipointed curve” returned zero blueprint nodes; ancestor gave
`lem-trf-local-term-locality`. The existing pure-dimension definition was found
and reused. No exact existing declaration states this item.

There is no statement correction and no STATEMENT-DISPUTED flag.

## New nodes

`def-trf-multipointed-curve` packages the exact inline multipointed-curve notion
already used by the item, following Temkin §1.2. Its own module has real structure
data and proof fields, with no `sorry`. It cites the existing scheme, ordinary
fibre, pure-dimension, flatness, finite-presentation and closed-immersion nodes.
The full finite-presentation fields are explicit for each structural map. The
searches described above found no existing node defining this notion separately,
no upstream or side declaration, and no Mathlib declaration. Its blueprint
ancestor and via chain are those of the item, with the item prepended. No other
new node or dependency module is delivered.

## Validation

Each supplied module is compiled separately through scompile.py in dependency
order. The dry run and final delivery are performed through deliver2.py. The
maintainer's independent review is the only independent reading, as required
by the current worker brief; no sub-agent was started.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
