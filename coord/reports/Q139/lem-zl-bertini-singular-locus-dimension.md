## Worker report

The module `Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension` states
`AlgebraicGeometry.bertini_singularLocus_dimension_lt`, with its proof exactly `sorry`.
Its four helper definitions assemble constructions already supplied by the dependency
interfaces: `bertiniParameterMap` is `Spec.map` of the polynomial coefficient inclusion;
`bertiniUniversalSection` is the finite sum of the coordinate functions times the
canonical tensor-pullback units of the given sections; `bertiniUniversalIdeal` applies
`homOfGlobalSection` and the recorded `Hom.zeroLocus`; `bertiniUniversalProjection` is
the zero-scheme inclusion followed by the coefficient projection. All their data are
explicit constructions. They belong to the universal family introduced in this node;
no independent notion or additional DAG node is required.

I read the full statement and six proof steps, all nine statement-dependency nodes and
their recorded signatures and docstrings, Stacks `varieties.tex` Situation 0FD3 and the
proof of Lemma 0FD6, and the zero-scheme definition in `divisors.tex`, Tag 02OQ.
The proof docstring follows the corrected first-order-kernel argument of the DAG,
including containment in `F = dF = 0` without assuming flatness at the zero coefficient.
The source's inference about smooth fibres at all coefficients is not used.

Hypothesis and clause correspondence:

- A field `k`: `{k : Type u} [Field k]`.
- A scheme `Y` smooth over `k`: `{Y : Scheme.{u}}`, its structure morphism
  `f : Y ⟶ Spec (CommRingCat.of k)`, and `[Smooth f]`. The explicit structure map is
  the input to the recorded projective-morphism construction and to base change.
- The invertible module: `(L : Y.Modules) [L.IsInvertible]`, using the recorded
  `Scheme.Modules.IsInvertible` class rather than the distinct sheaf-level class.
- A finite dimensional vector space with a basis of size `r`: `V : Type u`,
  `[AddCommGroup V] [Module k V]`, a finite index type `[Fintype I]`, and
  `b : Module.Basis I k V`. Here `r` is `Fintype.card I`. An arbitrary finite basis
  is the same data as a numbered basis, without excluding the empty basis.
- The linear map `ψ`: the additive map `ψ : V →+ Γ(L, ⊤)` and `_hlinear` together
  express exactly `k`-linearity. The scalar on the right is the image of `c : k`
  under `Scheme.ΓSpecIso.inv` followed by `f.appTop`; this is the scalar action
  induced by the scheme's structure morphism, not an additional freely chosen action.
- Generation by `ψ(b i)`: `hgen : Epi (L.freeHomEquiv.symm ...)`. Each top-open
  section is converted to the existing compatible-sections representation with
  `SheafOfModules.unitHomEquiv L (Scheme.Modules.homOfGlobalSection L ...)`.
  This is precisely the epimorphism condition recorded by the generation node.
- The associated projective morphism is an immersion: the instance
  `IsImmersion (ProjectiveSpace.homOfGeneratingSections I f L ... hgen)` applies
  to that specific canonical morphism, not an arbitrary immersive map.
- The affine coefficient space is `Spec (CommRingCat.of (MvPolynomial I k))`;
  its coordinates are `MvPolynomial.X i`, transported to global functions by
  `Scheme.ΓSpecIso.inv` and to the product by `pullback.snd.appTop`.
- The product is `pullback f (bertiniParameterMap k I)`. Its first projection is
  `pr_Y` and its second is `pr_A`; this is the factor-swapped form of the node's
  `A^r ×_k Y`, canonically the same fibre product with its named projections.
- The universal section is `bertiniUniversalSection f L (fun i ↦ ψ (b i))`,
  literally `∑ i, x_i • pr_Y^*ψ(b_i)` in the tensor pullback of `L`.
- `H_univ` is `(bertiniUniversalIdeal f L ...).subscheme`, the zero scheme of
  this actual section. The morphism `q` is `bertiniUniversalProjection f L ...`.
- The subset `Σ` is written, in both conclusions, as
  `{h | ¬ ∃ U, h ∈ U ∧ Smooth (U.ι ≫ bertiniUniversalProjection f L ...)}`.
  Thus it is the absence of the exact open neighbourhood specified by the node,
  without replacing this by smoothness of a fibre or of a local-ring map.
- `dim Σ < r` is `topologicalKrullDim` of this subset with its subspace topology,
  compared to `(Fintype.card I : WithBot ℕ∞)`.
- The consequent is `∃ B : Set ..., IsClosed B ∧ B ≠ Set.univ ∧ q '' Σ ⊆ B`:
  it asserts a closed proper subset containing the actual image of `Σ`.

Dependency declarations used:

- `def-weil-pbc-scheme-conventions` and `def-weil-scheme-morphism-properties` are
  convention records with no declaration of their own; I followed their recorded
  instructions to use Mathlib `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.IsImmersion` (Mathlib.AlgebraicGeometry.Morphisms.Immersion).
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (publicly supplied by the
  projective-morphism and zero-locus imports).
- `def-weil-pbc-generating-sections`: `SheafOfModules.GeneratingSections`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`; use its recorded `Epi`
  condition for the specified finite family, rather than quantifying over a new family.
- `def-weil-pbc-morphism-to-projective-space-by-sections`:
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`,
  `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`.
- `def-pc-zero-scheme`: `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`,
  `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`; the ideal's existing
  `subscheme` and `subschemeι` give the closed subscheme and inclusion.
- `def-pc-base-change`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, as explicitly prescribed by the record's note and the module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`. Module pullback is
  the existing `AlgebraicGeometry.Scheme.Modules.tensorPullback`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, valued in `WithBot ℕ∞`.

The construction also reuses `Scheme.Modules.tensorSectionsUnit` from
`Sheaf.AlgebraicGeometry.EtaleTensorSections` and `Scheme.Modules.homOfGlobalSection`
from `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`. These are
canonical section maps, not replacement definitions. I deliberately do not import the
downstream `BertiniSmoothMember` module for its section-family helper: its proof uses
this node. Instead the theorem uses the existing unit/global-section equivalence
inline, so no duplicate section-family declaration or cyclic import is introduced.

Available proof dependencies are imported as non-public imports: relative differentials,
proper/smooth base change, the polynomial Krull-dimension formula, finite type and
Noetherian spectra and spaces, the conormal sequence for smooth immersions, and the
smooth-differentials rank/fibre-dimension statement. The two proof-only prerequisites
`lem-zl-hypersurface-nonzero-relative-differential` and
`lem-zl-finite-type-fibre-image-dimension-bounds` have no recorded Lean interface in
the read DAG; they are named in the complete proof docstring and require no declaration
to type this statement.

Edge cases checked: empty `Y` gives empty `H_univ` and `Σ`, with dimension `⊥` and
`B = ∅`. An empty basis (`r = 0`) is allowed: generation plus invertibility forces
empty `Y`, the empty-index projective morphism interface supports it, and `⊥ < 0`
is the desired inequality. For `r = 1`, the possible non-smooth locus at the zero
coefficient is retained; no flatness hypothesis or smooth-fibre equivalence removes it.
No perfectness, algebraic closedness, positive dimension, nonemptiness, finite type or
separatedness assumption has been added. Finite type and separatedness are consequences
of the given smoothness and immersion. All universes and variables are explicit, and
`autoImplicit` is disabled. Every theorem proof in this delivery is `sorry`.

Searches for an existing statement and constructions:

- `msearch.py` LeanFinder, query “dimension bound for non smooth locus of universal
  hyperplane section immersive linear system”: eight hits for standard smooth
  relative dimensions, smooth loci and unrelated constructions; no incidence bound.
- `msearch.py` Loogle, query `"bertini"`: zero hits.
- `msearch.py` grep, query `Bertini|singular.*locus|universal.*[Ss]ection` in
  Mathlib/AlgebraicGeometry: zero hits.
- `msearch.py` LeanSearch, query “Dimension of the non smooth locus of a universal
  hyperplane family from an immersive linear system”: eight hits, including
  `Algebra.smoothLocus`, openness and relative-dimension facts; none states this bound.
- `rg` in upstream `WeilConjectures` for Bertini/singular-locus names found
  Bertini-Noether generic irreducibility and the curve construction. Neither has
  this universal-family theorem. The exact node id and all five proposed declaration
  names have no upstream hit (also checked the upstream-name index).
- `rg` in `lean/Sheaf` found `BertiniSmoothMember` and `BertiniIrreducibleMember`,
  which concern general members rather than the non-smooth-locus dimension. I read
  `BertiniSmoothMember` and reused its established scalar-law encoding and canonical
  tensor-section API without importing that downstream result. Searches of all five
  proposed declaration names in both source roots had no hit.

No statement correction, disputed statement, new node or dependency-record repair is
needed. The original node changes only in `lean`. The helper source tag was checked
against the local Stacks tag table: the zero-scheme definition is 02OQ.

## Second reading by Q139

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
