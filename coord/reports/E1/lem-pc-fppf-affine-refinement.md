## Worker report

The module states Stacks Project Tag 021P, Lemma 34.7.4: a finite fppf refinement
of an fppf covering of an affine scheme by affine opens of original members.

- The affine base `U = Spec(A)` is `{U : Scheme.{u}} [IsAffine U]`; Mathlib's
  `IsAffine` means isomorphic to a spectrum, so no ring is fixed artificially.
- The arbitrary original index set and schemes are `{I : Type v}` and
  `T : I → Scheme.{u}`. Their arrows are `f : ∀ i, T i ⟶ U`.
- Flatness, local finite presentation, and joint surjectivity of the original
  family are all encoded by `hf : Presieve.ofArrows T f ∈ fppfPrecoverage U`.
  Mathlib's `Scheme.fppfPrecoverage` is the precoverage of jointly surjective
  families of morphisms satisfying `Flat ⊓ LocallyOfFinitePresentation`.
- Finite selection is `∃ (n : ℕ) (i : Fin n → I)`. Repeated selections are
  allowed, just as repeated indices in a finite indexed family are allowed.
- The affine open subschemes inside `T (i j)` are
  `V : ∀ j, (T (i j)).Opens` and `∀ j, IsAffineOpen (V j)`.
- Their factorization through original members is the composite
  `(V j).ι ≫ f (i j)`. Its domain is `(V j).toScheme`.
- The finite composites being flat, locally of finite presentation, and jointly
  surjective is their `Presieve.ofArrows ... ∈ fppfPrecoverage U` membership.

Dependency declarations: `def-pc-fppf-site` uses
`Mathlib.AlgebraicGeometry.Sites.Fpqc`,
`AlgebraicGeometry.Scheme.fppfPrecoverage`; its recorded big-site construction
also cites `AlgebraicGeometry.Scheme.fppfTopology` and
`AlgebraicGeometry.Scheme.overGrothendieckTopology` in
`Mathlib.AlgebraicGeometry.Sites.Small`. `def-pc-scheme` uses
`Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom`; Mathlib's `AlgebraicGeometry.IsAffine` and
`AlgebraicGeometry.IsAffineOpen` render the affine clauses.

Edge cases: `I` may be empty; then the covering condition only holds for an
empty base. `n = 0` permits the empty refinement of an empty affine base.
Nonempty affine schemes require actual selected covering members. The
universe `v` of `I` is independent of the scheme universe `u`.

Searches: `msearch leanfinder` with "an fppf covering of an affine scheme has
a finite refinement by affine open subschemes of its members" returned general
affine-open-cover and affine-cover declarations, no matching theorem.
`msearch loogle` with "Scheme.fppfPrecoverage, Scheme.IsAffine,
Scheme.IsAffineOpen" returned no hits. `msearch grep` with
"fppf.*affine|affine.*fppf" in `AlgebraicGeometry/Sites` returned no hits.
`rg` over `WeilConjectures` and `lean/Sheaf` found a distinct fpqc singleton
affine-refinement theorem but no fppf theorem with this conclusion.
`grep -rn` for the node id over `WeilConjectures` returned no hits.
The local Stacks `.tex` checkout was absent; Tag 021P was read from its
published Stacks Project page at https://stacks.math.columbia.edu/tag/021P.

The server single-file compile completed cleanly.

## Second reading by E1

I opened the stage-2 node, its source reference (Stacks Project Tag 021P, Lemma
34.7.4), the dependency records, and
`lean/Sheaf/AlgebraicGeometry/FppfAffineRefinement.lean`. The itemized comparison
is:

- The affine base `U = Spec(A)` is rendered by `{U : Scheme.{u}} [IsAffine U]`.
  Verdict: exact up to Mathlib's equivalent `IsAffine` formulation; no ring or
  universe restriction is added.
- The arbitrary index set and family are rendered by `{I : Type v}`,
  `T : I → Scheme.{u}`, and `f : ∀ i, T i ⟶ U`. Verdict: exact, with an
  independent index universe.
- Flatness, local finite presentation, and joint surjectivity of the original
  family are rendered together by
  `hf : Presieve.ofArrows T f ∈ fppfPrecoverage U`. Verdict: exact; Mathlib's
  `fppfPrecoverage` is the jointly-surjective precoverage for
  `Flat ⊓ LocallyOfFinitePresentation`.
- Finiteness and selected indices are rendered by
  `∃ (n : ℕ) (i : Fin n → I)`. Verdict: exact; repetitions are permitted and
  `n = 0` remains expressible.
- The affine open members are rendered by
  `V : ∀ j, (T (i j)).Opens` together with
  `∀ j, IsAffineOpen (V j)`. Verdict: exact; `IsAffineOpen` means the associated
  open subscheme is affine.
- Containment and factorization are rendered by the canonical inclusion
  `(V j).ι` and the composite `(V j).ι ≫ f (i j)` from
  `(V j).toScheme` to `U`. Verdict: exact; no private factorization object is
  introduced.
- The conclusion that every selected composite is fppf and that their images
  jointly cover `U` is rendered by
  `Presieve.ofArrows (fun j ↦ (V j).toScheme)
  (fun j ↦ (V j).ι ≫ f (i j)) ∈ fppfPrecoverage U`. Verdict: exact, since the
  same precoverage encodes both properties.

Edge cases were checked: `I` can be empty; `n = 0` is allowed (and can only
cover bases for which the precoverage permits it); empty schemes and zero
objects are not excluded; no characteristic, Noetherian, separatedness, or
finite-type hypothesis is added; and the index and scheme universes `v` and
`u` are independent.

For the one-definition check, I searched with `msearch.py` (LeanFinder query
for a finite fppf affine refinement), Loogle (fppf precoverage/refinement),
LeanSearch (finite affine refinement), `rg` over `WeilConjectures/` and
`lean/Sheaf/`, and `grep` over Mathlib's algebraic-geometry site files. The
results were general affine-cover declarations and the underlying
`fppfPrecoverage`, but no theorem with this conclusion; no existing declaration
was found. The dependency declarations were read: `def-pc-fppf-site` points to
Mathlib's exact fppf precoverage/topology construction, and `def-pc-scheme`
supplies the scheme and affine notions.

No mismatch was found, so no Lean statement or node metadata required repair.
The sandbox file compiles cleanly with `scompile.py`; its node `lean.statement`
is verbatim equal to the theorem signature.
