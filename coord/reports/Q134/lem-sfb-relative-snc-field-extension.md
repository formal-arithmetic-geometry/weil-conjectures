## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeSNCFieldExtension` states
`AlgebraicGeometry.relative_snc_field_extension`, with `sorry` as its only proof.
No definitions or dependency records are changed, and no new nodes are needed.
The node statement is unchanged.

Hypothesis and conclusion correspondence:

- The field and arbitrary extension are `{F L : Type u} [Field F] [Field L]
  [Algebra F L]`. The scheme and its structure map are `{X : Scheme.{u}}`
  and `f : X ⟶ Spec (.of F)`. A single arbitrary ambient universe contains
  the schemes and fields; it imposes no separability, algebraicity or degree bound.
- Smooth finite type is `[Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]`.
  This is the finite-type convention of the recorded dependency.
- The divisor is the actual quasi-coherent ideal `D : X.IdealSheafData`, with
  `hD : D.IsSmoothStrictNormalCrossingsDivisor f`. This imports and uses the
  exact existing SNC definition, including its reducedness and affine-height clauses.
- Enumerate the supplied finite set A by `Fin n`. `C` is its family of closed
  subschemes represented by their ideal sheaves. `hunion : D = ⨅ a, C a`
  identifies the scheme-theoretic union; `hintegral` asserts integral components;
  `hdistinct` asserts pairwise noncontainment. These are the node's distinct integral
  components, rather than an unrelated family. Noncontainment is the existing SNC
  definition's exact expression for irreducible components, not an extra condition.
- `X_L` is `pullback f (Spec.map (CommRingCat.ofHom (algebraMap F L)))`.
  The first projection defines the pulled-back ideal `D.comap (pullback.fst ...)`;
  `comapIso` in Mathlib identifies its subscheme with the fibre product. The
  second projection is its structure map to Spec L.
- The first four conjuncts assert respectively smoothness of X_L, the effective
  Cartier condition `IsInvertible` for the pulled-back ideal, `IsReduced` for
  its subscheme, and `IsSmoothStrictNormalCrossingsDivisor` over L.
- `m : Fin n → ℕ` and the ideal family `B : (Σ a, Fin (m a)) → ...IdealSheafData`
  enumerate the finite splitting of each original component. Each pulled-back
  original component is smooth (the first clause after this existential).
  Its ideal is the infimum of its B pieces; each piece is integral. For each
  piece, the ideal inequality `h` gives Mathlib's canonical `inclusion h`,
  required to be both an open and a closed immersion. Thus the pieces are
  actual clopen subschemes of the specified pulled-back component.
- Distinct pieces over the same a have disjoint supports. Their global union
  is exactly D_L, and global noncontainment ensures all pieces are distinct.
  The `Set.range = irreducibleComponents` equality explicitly identifies their
  supports in D_L with all its irreducible components; their ideal pullbacks
  along D_L.subschemeι give those supports. Integral B pieces carry reduced
  structure, as required.
- A `Finset` s in the sigma index type selects any number r of distinct pieces.
  `s.sup B` is their scheme-theoretic intersection. It is smooth over L;
  every minimal prime of its ideal on every ambient affine chart has
  `height = (s.card : ℕ∞)`. This is exactly pure codimension r, with empty
  intersections allowed because their unit ideal has no minimal primes.
- Failure of `Set.InjOn (fun b ↦ b.1) s` means two selected distinct pieces have
  the same original a. The conclusion `s.sup B = ⊤` says the entire selected
  intersection is the empty closed subscheme, scheme-theoretically.
- If the original indices are distinct, the final ideal inequality gives the
  canonical inclusion of the selected intersection in the pullback of
  `(s.image (fun b ↦ b.1)).sup C`. This inclusion is required to be open and
  closed. This records the claimed clopen subscheme of the specified original
  intersection after scalar extension, with its canonical ambient inclusion.
- For s empty, `s.sup B = ⊥`, whose subscheme is canonically X_L; the smoothness
  and height clauses still apply with `s.card = 0`. This records the empty
  intersection convention without adding a tautological extra conjunct.

Dependency declarations used, with their recorded interfaces read:

- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with the actual `algebraMap F L`;
  `Field` is Mathlib's class, from `Mathlib.Algebra.Field.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor`:
  `Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; scheme pullbacks are provided by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`, which explicitly means locally
  generated by a nonzerodivisor, and its flat-pullback theorem.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`, `IsIntegral`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: actual ideal `comap` and
  `comapIso`; its subscheme API supplies the canonical `inclusion`.

Recorded proof-dependency modules are imported privately: finite-type dimension
bounds, finite-type dimension formula, proper/smooth base change, dimension
constancy, fibre dimension after base change, smooth geometric normality and
normal component decomposition. Generic Noetherian and flat-tensor APIs are
also imported privately. The docstring carries all eight DAG proof steps,
including the flat-tensor reducedness argument, componentwise dimension calculation,
clopen intersection construction, noncontainment argument and all empty cases.

Edge cases checked before writing: n=0 gives D the unit ideal and an empty
sigma family; D empty and X empty are permitted; no nonemptiness hypothesis
was added to X. Empty selected intersections use the zero ideal and cardinality
zero. Repeated original indices give the unit ideal. Ordinary transverse axes,
a smooth divisor splitting into disjoint integral components after extension,
and inseparable extensions over imperfect fields all have the stated interface.
Mixed dimensions of X are allowed, since codimension is measured by local prime
heights, not by one global dimension subtraction. Integral schemes are nonempty;
empty splitting families can occur only for empty schemes, as appropriate.

Searches actually run through msearch.py:

- LeanFinder: `Relative smooth strict normal crossings divisor under arbitrary
  field extension with splitting of integral components`: eight standard-smooth
  algebra/ring-map hits; no SNC or component-family theorem.
- Loogle: `"AlgebraicGeometry", "Smooth"`: twelve smoothness/base-change hits;
  no SNC or splitting theorem.
- LeanSearch: `A smooth strict normal crossings divisor remains strict normal
  crossings under arbitrary field extension`: eight smooth-base-change and
  normal-field-extension hits; none states this result.
- Mathlib grep: `NormalCrossing|normal.crossing|StrictNormal`, unrestricted:
  25 unrelated restrictNormal field-theory hits. Repeating under
  `AlgebraicGeometry` gave zero hits.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for the same pattern and
  the item id found the existing SNC/boundary definitions and consumers, but
  no scalar-extension theorem for this notion. The upstream name index and
  both Lean trees have no `relative_snc_field_extension` declaration or module.
  These existing SNC definitions were read; no private copy is introduced.

Source read: ILO Expose X, printed pp.149--151, especially the definition after
Theorem 2.1 and Step 2's preservation of (i)--(iv). The supplied DAG is the
stronger explicit integral-component form of that scalar-extension input.
The current example CompactObject module is withdrawn and contains no declarations;
the live SNC definition supplies the required header and namespace conventions.
No statement fault or STATEMENT-DISPUTED issue was found.

Validation: the prescribed scompile.py compiles both the sandbox and named library
module. An initial elaboration slowdown in equations between unnamed inclusions
was repaired by using Mathlib's canonical inclusion of ideal-defined subschemes.
No compiler timeout setting or local notation is required. The only postponed
proof is the requested theorem, with the complete natural-language proof above it.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
