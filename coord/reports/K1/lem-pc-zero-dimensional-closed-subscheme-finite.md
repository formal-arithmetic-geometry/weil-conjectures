## Worker report

The module `Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite` states
`AlgebraicGeometry.closed_subscheme_finite_of_topologicalKrullDim_le_zero`.
Its only theorem has proof `by sorry`; no definition or other theorem is introduced.
The original node is unchanged except for `lean`. No new nodes, dependency repairs,
or statement correction are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field k: `{k : Type u} [Field k]`.
- Schemes X and Z: `{X Z : Scheme.{u}}`, using the definition on `def-pc-scheme`.
- X over k: `f : X ⟶ Spec (.of k)` is its structure morphism.
- X of finite type over k: `[LocallyOfFiniteType f] [QuasiCompact f]`.
  These two properties together are precisely finite type, as fixed by
  `def-pc-morphism-conventions`. They do not impose separatedness or properness.
- A closed subscheme Z of X: `i : Z ⟶ X` with `[IsClosedImmersion i]`.
  This presents an arbitrary closed subscheme by its closed immersion, without
  choosing an ideal or adding reducedness.
- The underlying topological space of Z has dimension at most zero:
  `hZ : topologicalKrullDim Z ≤ 0`. This is the recorded topological dimension,
  valued in `WithBot ℕ∞`, rather than an alternative local-ring dimension.
- The structure morphism Z to Spec(k) is finite: `IsFinite (i ≫ f)`.
  Composition is exactly the induced structure morphism on the closed subscheme.
- Z is affine: `IsAffine Z`.
- Its global-section ring is a finite-dimensional k-algebra:
  `(letI := (i ≫ f).ΓAlgebra; FiniteDimensional k Γ(Z, ⊤))`.
  The algebra structure is the canonical one induced by this structure morphism,
  through `Γ(Spec k) ≅ k`, not an arbitrary algebra structure. The local `letI`
  supplies the corresponding scalar action. `FiniteDimensional` is Mathlib's
  abbreviation for finite generation as a module over the field.
  The node cites `def-weil-vector-space-dimension`, whose declaration is
  `Module.finrank`; the statement asserts finite dimensionality but no numerical
  dimension or bound, so no additional finrank clause is appropriate.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.IsAffine` in
  `Mathlib.AlgebraicGeometry.AffineScheme` expresses its affineness clause.
- `def-pc-morphism-conventions`: its record is explicitly a convention (no module
  or declaration), referring to the canonical properties on named nodes.
  The used properties are `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, available through Finite.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`. The node also records
  `AlgebraicGeometry.IsIntegralHom`; the item uses only its finite clause.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional` in
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- `def-weil-vector-space-dimension`: `Module.finrank` in
  `Mathlib.LinearAlgebra.Dimension.Finrank`; signature/docstring read, with no
  numerical dimension assertion to render, as explained above.
- For the canonical scalar action, the existing fully defined
  `AlgebraicGeometry.Scheme.Hom.ΓAlgebra` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` is reused.

Source check: the local Stacks sources are not present on this machine, so I read
[Stacks Tag 06LH](https://stacks.math.columbia.edu/tag/06LH) and the opening paragraph of
[Tag 03J3](https://stacks.math.columbia.edu/tag/03J3) online. Tag 06LH gives affineness
and finiteness for algebraic dimension-zero schemes. Tag 03J3 identifies a scheme
finite over a field with the spectrum of a finite-dimensional algebra. The empty
case in the node's proof extends dimension zero to dimension at most zero.
The module docstring carries all three proof steps and their dependencies.

Edge cases checked before drafting:

- Empty Z: topological dimension is bottom, hence satisfies `≤ 0`; global sections
  are the zero ring and a zero-dimensional k-vector space. No `Nonempty Z` or
  nontrivial-global-sections assumption is present.
- Empty X forces Z empty for a closed immersion; the same conclusion applies.
- Z = Spec(k) with its identity closed immersion: finite, affine, dimension one
  for its global-section vector space and topological dimension zero.
- Z = Spec(k[ε]/(ε²)) as the closed subscheme of the affine line cut out by t²:
  satisfies the hypotheses and has two-dimensional global sections. Nilpotents
  are retained; reducedness would incorrectly exclude this example.
- Any characteristic and non-algebraically-closed fields are allowed. No
  characteristic, perfection, or algebraic closure assumption is used.
- The arbitrary explicit universe `u` and `Scheme.{u}` are the standard universe
  convention for scheme morphisms to Spec(k); no finite/countable universe or
  point-cardinality constraint is imposed. Every variable and universe is bound.

Searches (all on 2026-10-11; remote-search receipts in `searches.jsonl`):

- `msearch.py leansearch`, query `zero dimensional finite type scheme over field is finite`:
  service unavailable, Internal Server Error; no verdict inferred from failure.
- `msearch.py leanfinder`, query `A zero dimensional closed subscheme of a finite type scheme over a field is finite affine and has finite dimensional global sections`:
  eight hits, including affineness from finite discrete topology,
  `IsArtinianScheme.finite` (finiteness of the point set), and finiteness for a
  reduced subsingleton source. None states the requested closed-subscheme theorem.
- `msearch.py loogle`, query `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsClosedImmersion`:
  three hits; these give finiteness of the immersion itself or characterize
  closed immersions as finite monomorphisms. They do not give finiteness of its
  composite with the finite-type structure morphism.
- `msearch.py grep`, query `topologicalKrullDim|IsArtinianScheme.finite|finite_of`,
  subdirectory `AlgebraicGeometry`: fifteen hits, including
  `IsLocallyArtinian.of_topologicalKrullDim_le_zero`; none gives all item clauses.
- `rg` on upstream `WeilConjectures/AlgebraicGeometry` with
  `topologicalKrullDim.*zero|finite.*dim.*zero|finite_of.*dim`: related dimension-zero
  arguments, but no declaration stating this closed-subscheme result.
- `rg` on project `lean/Sheaf/AlgebraicGeometry` with
  `finite.*(field|dim)|zero.*dim|dim.*zero`: related proper-dimension-zero and
  algebraic-dimension-zero lemmas. The former assumes properness, and the latter
  uses local-ring dimension and omits the finite-dimensional global-section
  clause; neither is the exact statement of this item.
- Search for the item id in upstream `WeilConjectures` and
  `dag/lean_names_upstream.json`: no recorded upstream declaration.
- Search for the chosen full declaration's short name
  `closed_subscheme_finite_of_topologicalKrullDim_le_zero` in Mathlib, upstream
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Validation: server `scompile.py` compiled the 51-line module in 1.7 seconds with
exit code 0, without warnings. The delivery dry run is performed after this report.

## Second reading by K1

I read the node statement and the Lean signature item by item. The field `k` is
rendered by `{k : Type u} [Field k]`; schemes `X` and `Z` are `{X Z : Scheme.{u}}`;
the structure morphism is `f : X ⟶ Spec (.of k)`. The finite-type hypothesis is
exactly `[LocallyOfFiniteType f] [QuasiCompact f]`, matching the project's
finite-type convention. The closed subscheme is `i : Z ⟶ X` with
`[IsClosedImmersion i]`, and the dimension hypothesis is
`hZ : topologicalKrullDim Z ≤ 0`. The conclusion has all three clauses in the
node's order: `IsFinite (i ≫ f)`, `IsAffine Z`, and finite-dimensional global
sections with the canonical scalar action, rendered by
`(letI := (i ≫ f).ΓAlgebra; FiniteDimensional k Γ(Z, ⊤))`.

No hypotheses, objects, quantifiers, or conclusion clauses are added, dropped,
weakened, or strengthened. The explicit universe permits the empty scheme,
zero-dimensional and zero-ring cases, arbitrary characteristics, and arbitrary
fields; no reducedness, separatedness, properness, nonemptiness, or algebraic
closedness is assumed. The empty index and `n = 0` cases are irrelevant to this
statement. The dependency declarations and their signatures were checked, and
the canonical `ΓAlgebra` instance is the existing project declaration.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` (LeanSearch, LeanFinder/
Loogle, and grep); no existing declaration states this result, and the chosen
name has no collision. The Stacks source (Tags 06LH and 03J3) agrees with the
signature. There were no mismatches to repair, no new nodes, no dependency
modules, and no statement correction.
