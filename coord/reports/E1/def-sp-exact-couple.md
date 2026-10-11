## Worker report

The module defines a bigraded exact couple of type `s`, its derived couple,
and the recursively derived pages and differentials. Type `0` is the node's
initial couple. The explicit family `D p q`, `E p q` represents the bigraded
objects; no arbitrary coproduct in the abelian category is assumed or needed.

Clause mapping:

- Abelian-category hypothesis: `[Category.{v} C] [Abelian C]`.
- Nonnegative type parameter: `(s : ℕ)`; initial couple is
  `BigradedExactCouple C 0`.
- The objects at every integer bidegree: fields `D`, `E : ℤ → ℤ → C`.
- The three bidegrees: fields `alpha`, `f`, `g` in `BigradedExactCouple`.
- Consecutive composites vanish: `alpha_f_zero`, `f_g_zero`,
  `g_alpha_zero`.
- The three kernel-image equalities: `exact_alpha`, `exact_f`, `exact_g`.
  They are indexed at the incoming map, so the subobjects are of one object.
- `d = g ∘ f` and its bidegree: `BigradedExactCouple.d`;
  `d_comp_d` names the square-zero claim.
- `D' = im alpha`: `derivedD`; `E' = ker d / im d`: `derivedE`, using
  the cokernel of `dInto` lifted into the kernel of outgoing `d`.
- The induced `alpha'`, `f'`, `g'` and their bidegrees: fields of
  `DerivedMaps`; `alpha_comm`, `f_comm`, `g_comm` identify them with the
  restriction, map on cycles, and the map from an `alpha`-preimage.
  `derivedMaps_exists` supplies their well-definedness and exactness, and
  `derived` selects the resulting type-`s+1` couple.
- `C₂ = C`, `C_{r+1} = C_r'`, and `E₂ = E`: `pageCouple` indexed by `r-2`
  and `page`. The differential `d_r = g_r ∘ f_r` is `pageDifferential`;
  for `r ≥ 2`, its source and target differ by `(r,1-r)`.
- `E₃ = E'` and `E_{r+1} = ker d_r / im d_r` follow definitionally from
  `pageCouple` and `derivedE` after the index shift. The type of `g'`
  in `DerivedMaps` is `(s+1,-s-1)`, yielding `(1,-1)` for the first
  derived couple.

Dependency: `def-sp-abelian` is
`CategoryTheory.Abelian` in `Mathlib.CategoryTheory.Abelian.Basic`.
Its source declaration extends preadditive, normal mono and epi classes and
provides finite products, kernels, and cokernels. Images, kernels, cokernels,
and subobject equalities use `Mathlib.CategoryTheory.Abelian.Exact`
(the unused `ShortComplex.LeftHomology` import was removed by reviewer R-exc0620).

Edge cases: `p,q : ℤ` includes negative indices; `s : ℕ` includes zero;
`r = 2` selects the original couple, and there is no first-quadrant
restriction. Zero objects and zero maps are admitted. No coproduct
existence is imposed on `C` beyond the stated abelian structure.

Searches: `msearch leanfinder "bigraded exact couple with maps alpha f g
and derived couple spectral sequence"` returned unrelated homological
bifunctor declarations. `msearch loogle "ExactCouple, SpectralSequence,
DerivedCouple"` returned no hits. `msearch grep "ExactCouple|exact couple|
DerivedCouple" Algebra/Homology` returned no hits. `rg` on
`WeilConjectures` and `lean/Sheaf` found spectral-sequence infrastructure
but no exact-couple definition; `grep -rn "def-sp-exact-couple"` on
`WeilConjectures` returned none. The Stacks Project source was read at
Tags 011Q, 011R, 011S, and 0AMJ; the local `literature/stacks-project/`
checkout was absent on this machine.

The named `sorry` theorems `d_comp_d`, `g_comp_d`, `dInto_comp_d`, and
`derivedMaps_exists` are the construction and exactness obligations of
`lem-sp-derived-couple-exact`; no definition contains `sorry` data.

## Second reading by E1

Independent comparison with the node and Stacks Tags 011Q, 011R, 011S, 0AMJ:

- The ambient abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`.
  I checked `CategoryTheory.Abelian` in Mathlib's `Abelian/Basic.lean`:
  it supplies the node's preadditivity, zero object, finite biproducts,
  kernels, cokernels, and normal mono/epi conditions. No further structure
  is assumed.
- The arbitrary integer-indexed objects are `D E : ℤ → ℤ → C` in
  `BigradedExactCouple`. This gives every `(p,q)`, including negative ones.
  The node's direct-sum notation is represented componentwise; no coproduct
  is needed to express its componentwise maps or exactness.
- The initial degrees `(-1,+1)`, `(+2,-1)`, `(0,0)` are respectively the
  fields `alpha`, `f`, `g` at `s = 0`; `s : ℕ` gives the node's general
  nonnegative type, with `g` landing in `E (p+s) (q-s)`.
- The three zero composites are `alpha_f_zero`, `f_g_zero`, and
  `g_alpha_zero`. The three equalities are `exact_alpha`, `exact_f`, and
  `exact_g`, indexed by the incoming map. Each `imageSubobject` and
  `kernelSubobject` is therefore a subobject of the same target. Reindexing
  their integer variables gives exactly the three displayed equations.
- `d` is `f ≫ g` and has degree `(s+2,-s-1)`; `d_comp_d` states its square
  is zero. The initial `s=0` specialization has degree `(2,-1)`.
- `derivedD p q` is the image of incoming `alpha (p+1) (q-1)`.
  `derivedE p q` is the cokernel of the incoming `dInto` lifted to the
  kernel of outgoing `d`, hence cycles modulo boundaries at `(p,q)`.
  `dInto_comp_d` is the named proof that this lift exists.
- `DerivedMaps.alpha`, `.f`, `.g` have the required target bidegrees.
  `alpha_comm` says `alpha'` restricts `alpha`; `f_comm` says the map from
  cycles descends to `E'` and lands in `D'`; `g_comm`, precomposed with
  `factorThruImage`, says `g'` is `g` of an `alpha`-preimage modulo
  boundaries. `derivedMaps_exists` asserts existence, well-definedness,
  zero composites, and the three exactness equalities. Its docstring
  explains each descent and the exactness chase of Tag 011R.
- `derived` uses those maps and has type `s+1`; its `g` has degree
  `(s+1,-s-1)`. `pageCouple 0 = X` and its successor is `.derived`, so
  `pageCouple (r-2)` is `C_r` for `r ≥ 2`. `page` is its `E` field and
  `pageDifferential` its `d`. At `r=2`, these are `E` and `g ∘ f`;
  at `r=3`, they are `E'` and `g' ∘ f'`; in general the degree is
  `(r,1-r)` and successor `E` is the cycles/boundaries quotient.

Edge cases: `s=0` is admitted; there is no first-quadrant, nonzero-object,
nonempty-index, characteristic, Noetherian, or finiteness assumption. The
only page indices used by the node are `r ≥ 2`; `Nat` subtraction also gives
arbitrary values at `r=0,1`, which adds no condition on those pages. `u,v`
are explicit and unconstrained, so neither object nor morphism universes
are fixed. The statement has no scheme parameter.

Independent searches: `msearch leanfinder` for "derived exact triangle
bigraded spectral sequence in an abelian category" returned derived-category
triangles, not this notion; `msearch loogle "ExactCouple"` found no identifier;
`msearch grep` for exact/derived couples found no match. `rg` for the same
terms across source `WeilConjectures`, project `lean/Sheaf`, and Mathlib's
homology and triangulated directories found only spectral-sequence and
spectral-object frameworks, not a bigraded exact couple. In particular,
Mathlib's `SpectralSequence` is generic page data, not this construction.
Stacks' cited pages assume only an abelian category; their ungraded page
numbering starts at one, while the node explicitly starts at two.

Mismatch and repair: the main Lean header was split across two lines, while
the node's `lean.statement` recorded it on one line. I put the header on
one line so the recorded signature matches verbatim; the delivery preflight
convention excludes the terminal `where`. No mathematical declaration changed.

## Review by R-exc0620 (FIX)

Matched against the node: abelian `C` with free universes; `D E : ℤ → ℤ → C`;
bidegrees of `alpha`, `f`, `g` (type `s`, type 0 = the node's couple); the three
zero composites and the three kernel = image equalities as subobjects of one
object; `d = g ∘ f` of bidegree `(s+2,-s-1)`; `D' = im alpha`, `E' = ker d / im d`;
`alpha'`, `f'`, `g'` pinned down uniquely by `alpha_comm`, `f_comm`, `g_comm`
(mono inclusion, epi projection, epi `factorThruImage`), so the choice in
`derived` is canonical; `g'` of bidegree `(s+1,-s-1)`; `C_2 = C`,
`C_{r+1} = C_r'`, `d_r` of bidegree `(r,1-r)`. `derivedMaps_exists` is items
2-3 of lem-sp-derived-couple-exact. No `ExactCouple` in Mathlib, the source or
`lean/Sheaf`. Fixes: dropped the unused import
`Mathlib.Algebra.Homology.ShortComplex.LeftHomology`; gave `dInto_comp_d` its
proof in words.
