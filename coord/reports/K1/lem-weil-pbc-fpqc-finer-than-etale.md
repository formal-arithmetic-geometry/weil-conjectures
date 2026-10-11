## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` states
`AlgebraicGeometry.Scheme.fpqcCover_of_smallEtaleCover`.  It uses a scheme `T`,
an object `U : T.Etale` of the small etale site, and an etale covering family
`𝒰` of `U.left`; `[𝒰.Over T]` and `hEt` express that all source schemes are
objects over `T` and etale over `T`.  The first conjunct `(∀ i, Flat (𝒰.f i))`
renders the clause that every covering arrow is flat.  The second conjunct
quantifies an affine open `V : U.left.Opens` and states existence of a natural
number `n`, indices `a : Fin n → 𝒰.I₀`, and affine opens `W j` in the selected
sources, with the union of their images equal to `V`; `n = 0` is allowed.

The statement is intentionally unproved (`sorry`).  Its proof docstring records
Tag 022C's route: etale implies flat; restriction over an affine open remains
etale and jointly surjective; quasi-compactness yields a finite affine
refinement; these are exactly the fpqc clauses.

Dependencies used as declarations:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` (Mathlib scheme structure).
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.smallEtaleTopology` and
  `AlgebraicGeometry.Scheme.Etale` (Mathlib).
- `def-weil-pbc-fpqc-covering`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`
  (Mathlib; the conclusion is rendered directly in the node's affine-open
  formulation).

Edge cases checked: the finite index type is `Fin n`, so `n = 0` is permitted;
the source and target schemes are arbitrary universe-`u` schemes; affine opens
are represented by `Scheme.Opens` with `IsAffineOpen`, and no nonemptiness or
separatedness assumption is added.

Searches made: `msearch.py K1 lem-weil-pbc-fpqc-finer-than-etale leanfinder
"every jointly surjective family of etale morphisms of schemes is an fpqc covering"`:
no exact project declaration; Mathlib candidates `Scheme.JointlySurjective`,
`smallEtaleTopology`, `fpqcPrecoverage`. `msearch.py ... loogle
"Scheme.Etale, fpqcPrecoverage, QuasiCompactCover"`: no single theorem matching
this small-site statement. `msearch.py ... grep
"etalePrecoverage_le_fpqcPrecoverage|fpqcPrecoverage" Mathlib/AlgebraicGeometry/Sites`:
found only the composite big-site comparisons and the definitions of
`smallEtaleTopology`/`fpqcPrecoverage`. `rg` over `WeilConjectures/` and
`lean/Sheaf/` found no existing declaration of this statement.

## Earlier second reading (a previous round; superseded)

I reread the target node and its three statement dependencies.  The `T` and `U`
binders render the base scheme and an object of its small étale site; `𝒰` is
an indexed covering family over `U.left`, with `[𝒰.Over T]` and `hEt` supplying
the source objects' structure over `T`.  The first conjunct is exactly the
flatness clause.  The second conjunct binds every affine open `V`, then gives
finitely many indices and affine opens whose image union is `V`, including the
empty finite case.  No other hypotheses or conclusions occur.  The dependency
records were checked against Mathlib declarations: `Scheme`, `Scheme.Etale` /
`smallEtaleTopology`, and `Scheme.fpqcPrecoverage`; no existing project theorem
states this specialized small-site implication.

## Second reading by K1

I opened the node, its source place (Stacks Project, `topologies.tex`, Tag
022C, lines 3043--3077), and the delivered module. The node's statement has
the following objects and clauses, matched against the Lean signature:

* `T` is a scheme, rendered by `(T : Scheme.{u})`.
* `U` is an object of the small étale site of `T`, rendered by
  `(U : T.Etale)`.
* The covering family has target `U.left`, is étale, and is over `T`, rendered
  by `𝒰 : U.left.Cover (precoverage @Etale)` and `[𝒰.Over T]`; its members are
  étale over `T`, as required for objects of `T.Etale`, rendered by
  `hEt : ∀ i, Etale (𝒰.X i ↘ T)`.
* The first conclusion clause, that every covering arrow is flat, is exactly
  `(∀ i, Flat (𝒰.f i))`.
* The second clause quantifies every affine open `V` of `U.left`, rendered by
  `(∀ (V : U.left.Opens), IsAffineOpen V → ...)`, and asserts a finite list
  (`n : ℕ`, with `n = 0` allowed), selected indices (`a : Fin n → 𝒰.I₀`),
  affine opens in the selected sources (`W`) and their affine-open proofs,
  with image union equal to `V`; this is rendered by the existential and the
  equality `⋃ j, 𝒰.f (a j) '' ... = (V : Set U.left)`.

No hypothesis is added beyond the data needed to represent a covering family
of the small site: `𝒰.Over T` supplies the structure maps to `T`, and `hEt`
supplies the étaleness of those source objects. No separatedness, Noetherian,
finite-type, nonemptiness, or universe restriction is present. The dependency
declarations were checked: `Scheme` is Mathlib's scheme, `Scheme.Etale` /
`smallEtaleTopology` is the small étale-site notion, and the fpqc-covering node
is rendered by the two displayed clauses (flatness and finite affine image
refinement). No dependency module or definition was needed.

Edge cases were checked directly in the signature: arbitrary index types are
allowed; `Fin 0` gives the permitted empty finite list; empty affine opens and
empty schemes are not excluded; no characteristic or nonzero assumption is
introduced; and the single universe `u` is used for all schemes, as in the
Mathlib site declarations. Searches with LeanSearch, Loogle/LeanFinder, and
`rg` over Mathlib, `WeilConjectures/`, and `lean/Sheaf/` found no declaration
of this small-site implication. The existing Mathlib big-site comparisons do
not state this small-site family form, so the module is necessary.

I found no mismatch and made no changes to the worker's statement or module.
