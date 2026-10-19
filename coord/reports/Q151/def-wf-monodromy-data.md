## Worker report

Existing declaration delivery; no new Lean module or definition. The declaration is
`AlgebraicGeometry.Monodromy.RepresentedDegreeDatum` in
`WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy`.
I read its full definition and docstring, `DegreeDatum`, and the complete signatures,
definitions and docstrings recorded by all five statement dependencies. I also checked
the current source with `scompile.py --source` and the current blueprint
`main-20261015/blueprint/sec-algebraic-groups-lie-algebras/sk-d-monodromy/def-wf-monodromy-data.md`
and `_section.md`. The module's Blueprint paragraph explicitly identifies its attached
monodromy tuple with this node. The structure stores the independent input; its other
factors are canonical definitions of that input, so an additional tuple structure
would duplicate the same notion.

Clause-by-clause correspondence (below, `D` is the represented datum, and the namespace
of all attached declarations is `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum`):

- The representation `rho` is `D.rep : W →* GL n k`. The ambient `W`, degree map and
  degree-one lift are supplied by `DegreeDatum W`: `deg`, `surjective_deg`,
  `degreeOneElement`, and `deg_degreeOneElement`. The current enclosing blueprint unit
  states exactly this abstract degree-datum setting over a field with `V = k^n`.
  `[Fintype n] [DecidableEq n] [Field k]` implement those coordinates; the Weil-sheaf
  specialization uses its Weil degree datum and attached representation. No
  semisimplicity assumption is imposed.
- The geometric closed subgroup `H_geom` is `D.geometricMonodromy`, the Hopf ideal
  `vanishingIdeal (D.degreeZero.map D.rep : Set (GL n k))`, with
  `D.degreeZero = D.deg.ker`. Its points are `zeroLocus D.geometricMonodromy k`.
  Thus the closure is inside GL, not inside all matrices. This is the exact existing
  declaration of `def-wf-geometric-monodromy-group`.
- The arithmetic extension factor is `D.ArithmeticMonodromyExtension`, the existing
  interface of `def-wf-arithmetic-monodromy-extension`: on k-points it is
  `zeroLocus D.geometricMonodromy k ⋊[D.frobeniusAction] Multiplicative ℤ`, with
  `frobeniusConj` conjugating by `D.rep D.degreeOneElement` and `frobeniusAction`
  its integral powers. This retains the integer coordinate. The dependency already
  presents the disjoint union of copies of the geometric closed group by its
  semidirect-product points; this delivery uses that interface unchanged.
- The degree components are `D.degreeComponent m`, defined as the preimage of
  `{Multiplicative.ofAdd m}` under `SemidirectProduct.rightHom`. Its
  `degreeComponent_eq_range` identifies this with `H(k) × {m}`. This is precisely
  `def-wf-degree-components`, including negative degrees.
- The stipulated grading is supplied by the recorded declarations of
  `lem-wf-degree-components-grading`: `degreeComponent_mul_degreeComponent`
  gives `G^[m] * G^[n] = G^[m+n]`, and `inv_degreeComponent` gives inversion to
  degree `-m`. These are properties of the canonical components, not extra fields
  chosen independently.
- The map to matrices is `D.arithmeticMonodromyExtensionHom`; its application formula
  is `x.left * D.frobenius ^ x.right.toAdd`. `image_degreeComponent` identifies
  its component image with `zeroLocus D.geometricMonodromy k * {D.frobenius ^ m}`.
  The dependency `lem-wf-degree-component-image` is its recorded
  `image_degreeComponent_eq_closure`, whose right side consists of matrices
  annihilating every member of the vanishing ideal of
  `D.rep '' (D.deg ⁻¹' {Multiplicative.ofAdd m})`. This is the current blueprint's
  closure/translate clause, using the same group and matrix map.

All five dependency nodes use the same module named above. Their declarations used
are respectively `degreeComponent_mul_degreeComponent` and `inv_degreeComponent`;
`image_degreeComponent_eq_closure`; `frobeniusConj`, `frobeniusAction`,
`ArithmeticMonodromyExtension`, `arithmeticMonodromyExtensionHom`;
`degreeComponent` and `degreeComponent_eq_range`; and `geometricMonodromy`.

Naming caveat for the independent reviewer: the current structure docstring's
parenthetical list calls one tuple entry `arithmeticMonodromy`, but that definition
is the finite-type Zariski closure of the whole matrix image. The file's main
Blueprint paragraph and the actual arithmetic-extension definition distinguish them.
The lean record explicitly binds `ArithmeticMonodromyExtension` and its matrix map;
no identification of that degree-graded extension with `arithmeticMonodromy` is made.

Edge cases checked by reading the definitions: dimension zero (empty finite index
set) is allowed; the identity representation gives trivial geometric group but still
one component for every integer, even though all matrix images coincide; `m = 0`
gives the geometric group and negative degrees use integer powers; no injectivity
of the matrix map is assumed. The degree map remains surjective independently of
the representation. The algebraic definitions do not impose a characteristic or
semisimplicity restriction; the intended algebraically closed characteristic-zero
coefficient field is included. The definitions carry their existing independent
universes without introducing any new size equality.

Searches performed:

- `msearch.py ... leanfinder "monodromy data representation geometric Zariski closure
  arithmetic degree graded monodromy extension"`: eight hits, principally Galois
  categories and Chevalley results; none define this tuple.
- `msearch.py ... loogle "Monodromy, SemidirectProduct"`: zero hits, unknown identifier
  `Monodromy`.
- `msearch.py ... grep "MonodromyData|monodromyData|RepresentedDegreeDatum|monodromy"`:
  six Mathlib hits in homotopy lifting and torsors; no algebraic monodromy tuple.
- `rg` of the source project for `MonodromyData|monodromyData|RepresentedDegreeDatum|
  def-wf-monodromy-data` finds the represented datum and its attached constructions
  in `Monodromy.lean`, and consumers in `RankOne.lean` and `Weights.lean`.
  `grep -rn "def-wf-monodromy-data"` finds the explicit Blueprint attachment in that
  module. The current published source additionally tags the structure docstring.
- The same `rg` search of `lean/Sheaf` finds no competing definition.
- `dag/lean_names_upstream.json` indexes `RepresentedDegreeDatum` and the geometric
  monodromy declarations under the monodromy unit. The item's existing audit already
  records the structure as closed. All dependency records agree on the module.

No node statement correction, new node, dependency repair or new sorry is introduced.
The existing-declaration probe and server preflight are run by `deliver2.py`.

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
