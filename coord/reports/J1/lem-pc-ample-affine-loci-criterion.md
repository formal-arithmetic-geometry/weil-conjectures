## Worker report

The module states `AlgebraicGeometry.isAmple_of_affine_generatingLoci` with a `sorry`
proof. Stacks Properties, Tag 01PS gives the affine-locus definition; Morphisms, Tag
01VT gives the projective-space immersion. The local Stacks source checkout was absent,
so I read https://stacks.math.columbia.edu/tag/01PS and
https://stacks.math.columbia.edu/tag/01VT.

Statement correspondence:

- The field `k` is `{K : Type u} [Field K]`. No characteristic condition is imposed.
- The scheme over `k` is `{X : Scheme.{u}}` with `f : X ⟶ Spec (.of K)`.
- Its properness is `(hproper : IsProper f)`.
- The invertible module is `(L : X.Modules) (hL : L.IsInvertible)`.
- Every point is `∀ x : X`; the positive power is `∃ (n : ℕ) ... 0 < n`.
- A global section of that power is `s : Γ(L.tensorPow n, ⊤)`.
- `x ∈ Scheme.Modules.generatingLocus s` expresses nonzero image of `s` in the
  one-dimensional residue fiber at `x` of the invertible module. The source library
  defines this as local generation; its `generatesAt_iff_mem_basicOpen` identifies it
  with nonvanishing of the local coefficient of `s` in a trivialization.
- `IsAffineOpen (Scheme.Modules.generatingLocus s)` states that this exact open is
  affine, not merely that it contains an affine neighborhood of `x`.
- `IsAmple f L` is the node's conclusion, defined by a positive tensor power with a
  closed projective-space immersion; the node's complete-system interpretation is
  carried by its recorded `def-sc-ample` declaration.

Dependency declarations read and used: `AlgebraicGeometry.IsAmple` in
`WeilConjectures.AlgebraicGeometry.Modules.Ample` (`def-sc-ample`),
`AlgebraicGeometry.Scheme.Modules.IsInvertible` in
`WeilConjectures.AlgebraicGeometry.Modules.Invertible` (`def-sc-invertible-module`),
`AlgebraicGeometry.IsProper` in `Mathlib.AlgebraicGeometry.Morphisms.Proper`
(`def-weil-proper-morphism`), and `AlgebraicGeometry.Scheme.residueField` in
`Mathlib.AlgebraicGeometry.ResidueField` (`def-weil-residue-field`). The latter
supplies the interpretation of nonvanishing; the signature uses the equivalent
existing `Scheme.Modules.generatingLocus` from
`WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`.

Edge cases: the empty scheme makes the pointwise condition vacuous and remains
allowed; `n = 0` is excluded by `0 < n`; a zero section has empty generating locus
on a nonempty invertible module; no nonemptiness, connectedness, dimension,
Noetherian, or characteristic hypothesis was added.

Searches: `msearch leanfinder` with "proper scheme over a field invertible sheaf
affine nonvanishing locus for every point implies ample" found only affine/basic
open and quasi-affine results, not this theorem. `msearch loogle` with
`AlgebraicGeometry.IsAmple, AlgebraicGeometry.Scheme.Modules.generatingLocus`
found no match (its Mathlib-only index does not know the project names).
`msearch grep 'ample|generatingLocus|nonvanishing' AlgebraicGeometry` found no
Mathlib ampleness theorem. `rg` of the source modules found the reusable
`generatingLocus` but no criterion theorem; `rg` of `lean/Sheaf` and `grep -rn`
for the node ID in the source checkout found no existing declaration. The new
declaration name also had no `rg` hit in Mathlib or either library.

The server compile completed with no errors or warnings.

## Second reading by J1

I read the node, both Stacks tags 01PS and 01VT, the module, and the dependency
declarations independently. Item-by-item comparison:

- Base field: `K : Type u` with `[Field K]` is the node's arbitrary field `k`;
  no characteristic, algebraic closure, or nonemptiness assumption appears.
- Scheme and structure map: `X : Scheme.{u}` and `f : X ⟶ Spec (.of K)` are
  precisely a scheme over `k`. `hproper : IsProper f` is its properness;
  Mathlib's definition is separated, universally closed, and locally of finite
  type, hence finite type because universally closed implies quasi-compact.
- Invertible module: `L : X.Modules` and `hL : L.IsInvertible` give the node's
  invertible `O_X`-module. The recorded declaration is local rank one, with no
  extra coherence or finite-presentation binder.
- Each point and positive exponent: `∀ x : X, ∃ (n : ℕ) ... 0 < n` preserves
  the pointwise quantifier order and `n ≥ 1`. The section
  `s : Γ(L.tensorPow n, ⊤)` is a global section of exactly that power.
- Nonvanishing locus: `x ∈ Scheme.Modules.generatingLocus s` says the section
  freely generates near `x`. In a local trivialization of an invertible module,
  `generatesAt_iff_mem_basicOpen` makes this equivalent to the node's condition
  that its image modulo the maximal ideal at `x` is nonzero. The same
  `generatingLocus s` occurs in `IsAffineOpen ...`, so the entire nonvanishing
  open is affine, as required by Stacks 01PS; an affine subneighborhood alone
  would be weaker.
- Conclusion: `IsAmple f L` records invertibility and a positive tensor power
  with a closed projective-space immersion. Its `IsVeryAmple` definition uses
  finitely many sections rather than literally naming the complete linear
  system in the node. The node's `lem-pc-complete-linear-system-closed` bridge
  establishes their equivalence for this proper `X`; the recorded
  `def-sc-ample` attachment also flags this distinction. Thus the Lean
  conclusion represents the node's ampleness notion, conditional on that
  bridge, and it does not add a hypothesis to this statement.

Edge cases: `X` may be empty, making the pointwise premise vacuous; `n = 0` is
excluded by `0 < n`. A zero section cannot cover a point of a nonempty
invertible module. The theorem does not constrain the characteristic,
dimension, connectedness, or choice of universe `u`; there is no index set.

Independent searches: `msearch leanfinder` for "proper scheme line bundle affine
nonvanishing opens characterize ample projective embedding" returned Proj
basic-open and quasi-affine results but no criterion. `msearch loogle` for
`IsAmple, IsAffineOpen` found no Mathlib match (the project name `IsAmple` is
not in its index). `msearch grep` for ample/nonvanishing/generating-locus
terms returned no relevant Mathlib theorem. An `rg` search for affine-locus
ampleness in `WeilConjectures/` and `lean/Sheaf/` found only an ample-family
criterion for group schemes, which is a different statement.

Mismatch found: the worker report said that the complete-system
interpretation was carried by the recorded `def-sc-ample` declaration itself.
The declaration only requests some closed immersion; the complete-system
claim uses the separately cited bridge node. I corrected that account here.
No Lean or node signature change was needed; no hollow definition or proved
theorem occurs in this module, and its only proof is `sorry`.
