## Worker report

The module states `CochainComplex.exists_lowerTruncationStepSES` for any abelian
category `C`, any cochain complex `K : CochainComplex C ℤ`, and every integer `m`.
The proof is `sorry`. The theorem chooses the canonical transition `q K m` and
identifies its kernel with the node's two-term complex `C_m(K)`. Mathlib's
`truncGE` is the canonical lower truncation: its degree-`m` object is
`K.opcycles m`, the cokernel of the preceding differential, and above `m` it
has the objects of `K`. The theorem chooses the canonical map `φ` from the
complex concentrated in degree `m` with value `K.homology m` into that kernel.

The node's hypotheses and clauses correspond to Lean as follows:

- Abelian category: `[Category.{v} C] [Abelian C]`; arbitrary integer and
  complex: the binders `(K : CochainComplex C ℤ) (m : ℤ)` throughout.
- Cohomology `ker d^m / im d^(m-1)` and quasi-isomorphism: `K.homology m`,
  `HomologicalComplex.homologyMap`, and `QuasiIso (φ K m)`.
- Lower truncations and the canonical quotient transition: `K.truncGE m`,
  `K.truncGE (m + 1)`, `q K m`, and
  `K.πTruncGE m ≫ q K m = K.πTruncGE (m + 1)`.
- The two-term complex: `kernel (q K m)`. The existential isomorphisms `e₀`
  and `e₁` identify its degrees `m` and `m + 1` with `K.opcycles m` and
  `Abelian.image (K.d m (m + 1))`; `IsZero` states all other degrees vanish.
  The equation ending in `K.fromOpcycles m (m + 1)` specifies its induced
  differential after the two identifications and inclusion of the image.
- Inclusion in degree `m`: the equation with `e₀.inv` and
  `K.truncGEXIsoOpcycles m`. Inclusion in degree `m + 1`: the equation with
  `e₁.inv`, `K.truncGEXIso`, and `Abelian.image.ι`.
- Quotient map in degree `m`: `(q K m).f m = 0`. In degree `m + 1`: the
  equation with `(K.πTruncGE (m + 1)).f (m + 1)`. In degrees above `m + 1`:
  the identity equation using both `truncGEXIso` maps.
- Degreewise short exact sequence: `ShortComplex.mk` of `kernel.ι` and `q`
  is `ShortExact`. For complexes over an abelian category, Mathlib's
  `HomologicalComplex.shortExact_iff_degreewise_shortExact` identifies this
  with exactness in each degree.
- `H^m(K)[-m] → C_m(K)`: the domain of `φ K m` is
  `(singleFunctor C m).obj (K.homology m)`. Its component equation with
  `singleObjXSelf` and `K.homologyι m` makes it the canonical inclusion of
  cycles modulo boundaries, with zero other source components. `QuasiIso`
  gives the asserted cohomology equivalence.
- Naturality: for every `f : K ⟶ L`, the last clause gives the commuting
  transition square, a map `g` between the two kernels compatible with their
  inclusions, and the commuting square for `φ` using `homologyMap f m`.

Dependency declarations used: `CategoryTheory.Abelian` in
`Mathlib.CategoryTheory.Abelian.Basic` (def-sp-abelian);
`DerivedCategory`, together with Mathlib's `CochainComplex`, `homology`,
`QuasiIso`, `truncGE`, and `singleFunctor`, under
`Mathlib.Algebra.Homology.DerivedCategory.Basic` and its imports
(def-weil-abstract-derived-category); `DerivedCategory.TStructure.t` in
`Mathlib.Algebra.Homology.DerivedCategory.TStructure`
(def-sbc-standard-tstructure-derived-category). The last dependency supplies
the standard-truncation context; the theorem uses the underlying cochain
truncations directly.

Edge cases checked: `K = 0`; `m = 0` and negative `m`; zero and surjective
`d^m`; and degrees below `m`, exactly `m`, exactly `m + 1`, and above
`m + 1`. No boundedness, nonzero-object, or derived-category-size
assumption is added. At zero differentials the image term vanishes while
`H^m(K)` fills the degree-`m` term. If `d^m` is epi, the degree-`m + 1`
term is all of `K^(m+1)` and the target quotient there is zero.

Searches: `msearch.py leanfinder` with “degreewise short exact sequence of
successive canonical lower truncations ... shifted cohomology” found
`CochainComplex.shortComplexTruncLE_shortExact` and related truncation APIs,
but no successive lower-truncation sequence; `msearch.py loogle` with
`CochainComplex.truncGE, CochainComplex.truncGEMap,
CochainComplex.homology` returned no hit (unknown `CochainComplex.homology`);
`msearch.py grep` for `truncGE.*truncGE|truncGE.*single|shortExact.*truncGE|
lower truncation` in `Algebra/Homology` found the canonical truncation
implementation but no matching theorem. `rg` in Mathlib, the upstream
`WeilConjectures`, and `lean/Sheaf`, and `grep -rn` for the node id in
`WeilConjectures`, found no exact statement or duplicate declaration.

The local `literature/stacks-project/` checkout is absent on this machine.
I read the cited source directly at
https://stacks.math.columbia.edu/tag/0118 and
https://stacks.math.columbia.edu/tag/08J5. Tag 0118 gives the cochain
canonical truncation with the cokernel at its boundary; Tag 08J5 names the
resulting lower-truncation triangle.

## Second reading by F1

The node introduces an abelian category `𝒜`, a cochain complex `K`, its cohomology
`H^r(K)`, and an integer `m`. The Lean binders
`{C : Type u} [Category.{v} C] [Abelian C]`, `(K : CochainComplex C ℤ)`, and
`(m : ℤ)` render these objects without boundedness, nonzero, or universe
restrictions beyond the stated category instances. The node's lower truncations and
canonical transition are rendered by `K.truncGE m`, `K.truncGE (m + 1)`, and the
existential `q`, with
`K.πTruncGE m ≫ q K m = K.πTruncGE (m + 1)` identifying the canonical quotient.

The node's two-term kernel `C_m(K)` is rendered as `kernel (q K m)`: the existential
isomorphisms `e₀` and `e₁` identify its degree `m` and `m + 1` objects with
`K.opcycles m` and `Abelian.image (K.d m (m + 1))`, the `IsZero` clause makes all
other degrees vanish, and the displayed differential equation identifies the induced
differential. The two inclusion equations give the identity in degree `m` and the
image inclusion in degree `m + 1`; the quotient equations give zero at `m`, the
cokernel map at `m + 1`, and identities above. `ShortExact` states the degreewise
short exact sequence. The map from `H^m(K)[-m]` is
`φ K m : (singleFunctor C m).obj (K.homology m) ⟶ kernel (q K m)`; its component
equation is the canonical cycles-modulo-boundaries inclusion and `QuasiIso (φ K m)`
is the node's quasi-isomorphism clause. Finally, the last conjunct quantifies over
every chain map `f : K ⟶ L`, gives the commuting transition square, supplies the
induced kernel map `g`, and gives the commuting square with `homologyMap`, exactly
the node's naturality clause.

Edge cases checked: `K = 0`; `m = 0` and negative `m`; zero or epimorphic
`d^m`; degrees below `m`, equal to `m`, equal to `m + 1`, and above `m + 1`.
The arbitrary `Type u` and `ℤ` binders retain all universes and integer cases, and
no empty-index, characteristic, boundedness, or nonzero assumptions are introduced.

Searches were checked independently: LeanFinder found only the generic truncation
short-complex API (`CochainComplex.shortComplexTruncLE_shortExact`) and no theorem
for this successive lower-truncation kernel; Loogle's query for `truncGE` and
homology had no usable match; grep over Mathlib's `Algebra/Homology`, the source
`WeilConjectures`, and `lean/Sheaf` found no duplicate statement. The node's
recorded searches also include LeanSearch (service unavailable), Loogle, LeanFinder,
and grep, with the same no-match verdict. No existing declaration or dependency
record was unusable, and no new node was needed.

The semantic statement required no repair: every node object, hypothesis, clause,
quantifier order, and edge case is rendered by the theorem signature. I changed only
the declaration docstring, adding the three proof steps required by H8: degreewise
exactness and chain-map verification; the cohomology computation proving the
quasi-isomorphism; and functoriality under a chain map. The theorem remains
statement-only with `sorry` proof.
