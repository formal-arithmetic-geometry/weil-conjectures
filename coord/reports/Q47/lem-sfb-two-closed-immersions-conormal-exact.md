## Worker report

The module `Sheaf.AlgebraicGeometry.TwoClosedImmersionsConormalExact` states
`AlgebraicGeometry.Scheme.Modules.twoClosedImmersions_conormal_exact`, with its sole proof
`sorry`. It adds no definitions and changes only the item's `lean` record. The node statement,
dependencies and accepted five-step proof are unchanged. The theorem docstring transcribes
those five steps, including the construction of the second arrow and the stalk computations.

Source read: Stacks `morphisms.tex`, `lemma-two-immersions` (067L), and
`lemma-differentials-relative-immersion` (01UZ). The former gives precisely the right-exact
sequence and cites conormal functoriality (01R4) for its first arrow. The latter specifies
its differential-induced second arrow. The node is the closed-immersion specialization
already selected by its accepted statement, rather than the more general immersion version.

Every hypothesis and clause is represented as follows:

| Node clause | Lean rendering |
| --- | --- |
| Arbitrary schemes X, Y, Z | `{X Y Z : Scheme.{u}}`, with explicitly declared universe `u` |
| Any morphism f : X → Y | `(f : X ⟶ Y)` with no property instance on f |
| i : Z → X and j : Z → Y are closed immersions | The two morphism binders and `[IsClosedImmersion i] [IsClosedImmersion j]` |
| f composed with i is j | `(h : i ≫ f = j)` |
| Their ideal sheaves | `i.ker.toModules` and `j.ker.toModules`, the existing ideal-sheaf modules |
| C_{Z/X} = i* I_i, C_{Z/Y} = j* I_j | `(tensorPullback i).obj i.ker.toModules` and `(tensorPullback j).obj j.ker.toModules` |
| Relative differential sheaf and its pullback | `f.relativeDifferentials` and `(tensorPullback i).obj f.relativeDifferentials` |
| An O_Z-linear sequence with these objects | Existential morphisms `u` and `v` in `Z.Modules` with exactly these sources and targets |
| u is exactly the functorial conormal map for top 1_Z and bottom f | Equality of `u` to the inverse canonical identity-pullback comparison followed by the unique `c` of `closedImmersion_conormal_functorial i j f (𝟙 Z) (h.trans (Category.id_comp j).symm)` |
| v sends a local equation class a to 1 tensor d a | For every open `U` and `a : Γ(i.ker.toModules, U)`, the equation for `v.app (i ⁻¹ᵁ U)` on `tensorPullbackSection i i.ker.toModules U a`, with right side `tensorPullbackSection i f.relativeDifferentials U (f.relativeDifferentialsDerivation.d (X := op U) (i.ker.toModulesι.app U a))` |
| The sequence is a complex | `∃ w : u ≫ v = 0` |
| Kernel of v equals the sheaf image of u | `(ShortComplex.mk u v w).Exact` |
| v is surjective as a sheaf morphism, ending in zero | `Epi v`; this is sheaf epimorphy, and does not assert surjectivity on every open's sections |
| No finite type, smoothness, flatness, Noetherian hypotheses | None of these is present in the signature |

The existential `u` is only a name for the displayed fixed expression, not an arbitrary
arrow. Its expression is literally the one already used in
`Sheaf.AlgebraicGeometry.ConormalSurjectionUnramified`, so that downstream lemma can use the
sequence directly. The chosen conormal map is supplied by the dependency's existence and
uniqueness result, with the ideal map fixed by its section formula. The canonical identity
comparison is `tensorPullbackSectionId`. The formula for `v` is stated on *all* local ideal
sections. Their unit images locally generate the tensor pullback, so it characterizes the
canonical arrow, without assuming an arbitrary linear map or choosing unrelated isomorphisms.

Dependency interfaces read and used (names in their original namespaces):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `AlgebraicGeometry.Scheme.Hom.ker`.
  Its module realization and inclusion are the existing `IdealSheafData.toModules` and
  `IdealSheafData.toModulesι` of
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`, publicly exposed by the
  conormal-functoriality module. Closed immersions provide the quasi-compactness needed
  for the kernel-ideal identification.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  `Scheme.Modules.tensorPullbackSectionAdjunction`, its `tensorPullbackSection`, and
  `tensorPullbackSectionId`. The original functor is the publicly imported
  `Scheme.Modules.tensorPullback` from `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials` and `Scheme.Hom.relativeDifferentialsDerivation`.
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial`:
  `Scheme.Modules.closedImmersion_conormal_functorial`, including its full unique-map
  condition and affine equation-class formula.
- `Mathlib.Algebra.Homology.ShortComplex.Exact`: `CategoryTheory.ShortComplex.Exact`.

All recorded proof dependency modules are imported plainly:
`Mathlib.RingTheory.Kaehler.Basic` (`KaehlerDifferential`),
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`
(`Scheme.Modules.exists_tensorPullbackAdjunction`),
`WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealStalkRange`
(`Scheme.Modules.closedImmersion_ideal_stalk_range`),
`WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`
(`Scheme.Modules.exists_tensorPullback_stalk_iso`), and
`WeilConjectures.Algebra.Homology.ModuleStalkExact` (`RingedSpace.module_stalk_exact`).
Proof dependencies that are also statement dependencies have public imports.
`lem-sfb-relative-differentials-stalk` and `lem-sfb-ring-two-quotients-conormal-exact`
have no Lean record or Mathlib match in the read snapshot, so there is no recorded module
to import for them. They are only proof dependencies, and no missing notion is needed
for this statement. Their role remains explicit in the proof docstring.

Edge cases checked mathematically before writing:

- Empty Z: all three modules on Z are zero and the local equation conditions and stalk
  exactness tests impose no excluded nonempty case.
- f = identity, j = i: u is the identity conormal map; the differential sheaf is zero.
- i = identity and j = f a closed immersion: its conormal module is zero and
  Ω_{X/Y} vanishes, giving the asserted zero-ending sequence.
- j = identity and i a section of f: the first conormal is zero and the second arrow
  identifies the conormal with the pulled-back differentials, as 01UZ predicts.
- On stalk rings k[t] → k → k, the first arrow k → 0 need not be injective. The Lean
  statement asserts no injectivity at the left endpoint.
- k → k[e]/(e²) → k is permitted, although the closed immersion is nonflat. Its second
  arrow takes e to de and is an isomorphism after tensoring to k, in every characteristic,
  including 2. No regularity, reducedness, flatness or characteristic hypothesis appears.

Searches for an existing statement:

- `msearch.py leanfinder`, query "For two closed immersions Z into X and Y and a morphism
  X to Y the conormal sheaves and pullback relative differentials form a right exact
  sequence": 8 results, consisting of ideal-sheaf functoriality, closed-immersion lifting,
  ring cotangent exactness and Jacobi--Zariski exactness; none is the stated sheaf sequence.
- `msearch.py leansearch`, query "For two closed immersions Z to X and Z to Y the conormal
  sheaves and pullback relative differentials form a right exact sequence": 8 results on
  ideal-sheaf functoriality, immersions and open restriction; none matches.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials, CategoryTheory.ShortComplex.Exact`:
  0 results; Loogle does not index the project-relative-differentials name.
- `msearch.py grep`, query `conormal|two_immersions|twoImmersions` in Mathlib
  `AlgebraicGeometry`: 0 results.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `two_immersions|twoImmersions|lem-sfb-two-closed-immersions-conormal-exact`:
  only the downstream `ConormalSurjectionUnramified.lean` refers to the item; it does not
  state this sequence. Broader conormal searches find the functoriality theorem, affine
  section identifications, smooth-immersion and lci splitting statements, not this result.
- `rg` of `dag/lean_names_upstream.json` for the item's ID and `conormal_exact` found
  no existing declaration. A separate full-name search in the project source found no
  declaration `twoClosedImmersions_conormal_exact`.

No statement dispute, correction, new node or dependency repair is needed.

Validation: `scompile.py Q47 lem-sfb-two-closed-immersions-conormal-exact` compiled the
single module both as sandbox and library module, cleanly (6.0 s and 5.8 s). Every variable
and universe is explicit; both `autoImplicit` and `relaxedAutoImplicit` are disabled.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
