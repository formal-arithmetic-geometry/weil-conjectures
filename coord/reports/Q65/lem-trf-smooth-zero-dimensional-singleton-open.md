## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothZeroDimensionalSingletonOpen` states
`AlgebraicGeometry.exists_etale_open_singleton_fibre_of_smooth_of_dimension_zero`.
Its proof is `sorry`; no definitions or other theorems are added. The node changes only
in `lean`. No statement correction, disputed statement, or new node is necessary.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 057G,
`lemma-slice-smooth`, its statement and entire case `d = 0` (lines 10775–10815).
Although the full slicing lemma assumes a closed point in the fibre and a separable
residue extension, the zero-dimensional argument does not use either assumption:
the smooth dimension-zero criterion gives an étale open, then discrete fibre topology
isolates its specified point. The node correctly extracts this case.

Hypotheses and clauses, matched individually:

- Schemes and the morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The point and its base image: `(x : X)` and `f x`; no separate unspecified base point.
- The given open subscheme containing it: `(W : X.Opens) (hx : x ∈ W)`;
  `W.toScheme` and `W.ι` are the existing scheme restriction and inclusion.
- Smoothness of the restricted map: `(hSmooth : Smooth (W.ι ≫ f))`.
- Dimension zero in the original scheme-theoretic fibre:
  `(hDim : topologicalKrullDimAt (f.asFiber x) = 0)`.
  Mathlib's `asFiber` is the point corresponding to `x` under `f.fiberHomeo (f x)`;
  the recorded `topologicalKrullDimAt` is the infimum of dimensions of open neighbourhoods,
  exactly the node's local dimension, not the dimension of a local ring.
- The desired open subscheme inside the given one: `∃ Z : X.Opens, Z ≤ W`.
- It contains the same point: `x ∈ Z`.
- Its map to the original base is étale: `Etale (Z.ι ≫ f)`.
- Its scheme-theoretic fibre over the original base point has underlying set `{x}`:
  `Set.range ((Z.ι ≫ f).fiberι (f x) ≫ Z.ι) = {x}`.
  Here `(Z.ι ≫ f).fiber (f x)` is precisely `Z_s`, and the composite is its canonical
  projection to `X`. Both fibre projection and open inclusion are embeddings, so this
  equality states exactly that the fibre consists of the corresponding point, without
  identifying points of different types or dropping its nonemptiness. Equivalently,
  the fibre homeomorphism identifies this image with `Z ∩ f ⁻¹' {f x}`.
- The inclusion is an immersion: `IsImmersion Z.ι`. Mathlib's
  `IsImmersion.isImmersion_iff_exists` identifies this with the node's factorization
  into a closed immersion followed by an open immersion.
- There are no closed-point, separability, affine, Noetherian, finite-type, separatedness,
  characteristic, or global smoothness hypotheses. Every universe and variable is
  explicitly bound; `set_option autoImplicit false` enforces this.

Recorded dependency declarations used, read at their source:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the canonical open restrictions are represented by `Scheme.Opens` and their inclusions.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; `Mathlib.AlgebraicGeometry.Morphisms.Immersion`:
  `AlgebraicGeometry.IsImmersion`, `IsImmersion.isImmersion_iff_exists`.

Proof dependencies are imported without `public` when not already statement imports:
`WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension`
(`exists_etale_open_of_smooth_of_fibre_dimension_zero`),
`WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
(`Scheme.Hom.etale_fibre_discrete_separable_points`), and
`Mathlib.Topology.Defs.Induced` (`instTopologicalSpaceSubtype`). The composition node's
Mathlib match is already public via the étale import (`Etale.etale_comp`, the
open-immersion-to-étale instance, and `Etale.of_comp`). Their full signatures and
docstrings were read. No private copies or replacement dependency records are needed.

Edge cases checked before writing:

- The empty source has no `x`, so the theorem is vacuous; an empty `W` cannot satisfy `hx`.
- The range equality forces the selected fibre to be nonempty and excludes every other
  point, including when the original fibre is infinite. No finiteness assumption is used.
- For the identity on any scheme, the fibre at any point is a singleton spectrum and has
  dimension zero, including when `x` is a nonclosed generic point of the source.
- A smooth affine line over a field has local fibre dimension one, so its closed points
  do not accidentally satisfy the dimension hypothesis through local-ring dimension.
- Arbitrary residue fields and positive characteristic are allowed. Inseparable residue
  extensions cannot create a counterexample: smoothness with local fibre dimension zero
  already implies an étale neighbourhood.
- An open immersion factors as the identity closed immersion followed by itself; the
  final immersion clause requires no quasi-compactness or separatedness assumption.

Searches performed through the prescribed `msearch.py Q65 <item>` wrapper:

- LeanFinder: "A smooth morphism with fibre dimension zero at a point has an open etale
  neighbourhood with singleton fibre" — 8 hits, including smooth chart declarations,
  algebraic relative-dimension-zero criteria, `IsEtale`, and `IsEtale.instIsSmooth`.
  No hit states the open singleton-fibre conclusion.
- Loogle: `"IsEtale", "singleton"` — 0 hits.
- Mathlib grep in `AlgebraicGeometry`:
  `(Smooth|Etale).*(singleton|fibre_dimension_zero|fiber_dimension_zero)|`
  `(singleton|fibre_dimension_zero|fiber_dimension_zero).*(Smooth|Etale)` — 0 hits.
- LeanSearch: "A smooth morphism at a zero dimensional fibre point admits an etale open
  with singleton fibre" — 8 hits, including `IsSmooth.exists_isStandardSmooth`,
  standard-smooth algebra criteria, and `Algebra.isOpen_etaleLocus`; no exact match.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the smooth/étale singleton
  and dimension-zero patterns returned ingredients or unrelated cohomology/sieve results,
  including the recorded étale-open theorem, not the whole statement.
- `rg` for the item id in `lean/WeilConjectures` and `lean/Sheaf` returned no match.
- Name search in both source trees and `dag/lean_names_upstream.json` for
  `SmoothZeroDimensionalSingletonOpen` and
  `exists_etale_open_singleton_fibre_of_smooth` returned no match before writing.

## Second reading by Q65

I reread the node and final declaration clause by clause. The binders keep the given `W`
fixed; the existential has both `Z ≤ W` and `x ∈ Z`; smoothness is only required on `W`;
the dimension is taken at `f.asFiber x` in the original fibre; the étale map is the
restriction of the same `f`; and the singleton uses the canonical projection of the
actual scheme-theoretic fibre back to `X`. The final conjunction keeps the immersion
clause. No mismatch or node change was found. This is a worker self-check, not an
independent-agent review: the dispatcher explicitly prohibits starting other agents,
and the maintainer performs the independent delivery review.

Validation: `scompile.py Q65 lem-trf-smooth-zero-dimensional-singleton-open <module>`
passed both sandbox and library-mode compilation (3.5 s and 2.0 s), with no errors or
unexpected warnings. A local data check confirms that only `lean` changes in the node,
the stored signature is verbatim, and every Lean source line is at most 100 characters.

The first dry run required the recorded signature to stop immediately before `:=`;
removed that delimiter from `lean.statement` to match the preflight signature convention.
The Lean declaration and mathematical statement are unchanged.
