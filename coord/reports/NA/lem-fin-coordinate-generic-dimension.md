## Worker report

The module `Sheaf.AlgebraicGeometry.CoordinateGenericDimension` states
`AlgebraicGeometry.coordinate_generic_fiber_dimension_lt`, with only a `sorry` proof.
No definitions, dependency repairs, new nodes, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- Integral base S: `(S : Scheme.{u}) [IsIntegral S]`. This includes nonemptiness,
  reducedness and irreducibility; no Noetherian hypothesis is imposed.
- Function field K: the dimension hypothesis uses the scheme-theoretic fibre at
  `genericPoint S`. Its residue field is canonically the generic stalk `S.functionField`,
  since this stalk is a field for integral S. Thus this is precisely X_K, without
  introducing a redundant arbitrary field or field comparison hypothesis.
- Finite affine dimension m: `m : ℕ` and `AffineSpace (ULift.{u} (Fin m)) S`.
  ULift puts the finite coordinate set in the scheme universe, as Mathlib requires.
- Closed immersion Y into affine space: `i` with `[IsClosedImmersion i]`.
- Open X in Y: `j : X ⟶ Y` with `[IsOpenImmersion j]`. This is the usual
  isomorphism-invariant description of an open subscheme, with no extra hypothesis.
- Dimension bound: `hdim` says `topologicalKrullDim` of the fibre of
  `j ≫ i ≫ (AffineSpace … S ↘ S)` at the generic point of S is at most n.
- Every coordinate r: `(r : Fin m)`. The displayed morphism is exactly `j ≫ i`
  followed by `AffineSpace.reindex (fun _ : ULift (Fin 1) ↦ ULift.up r) S`;
  this selects the specified coordinate, rather than quantifying over an arbitrary map.
- Generic point of the relative affine line: `genericPoint (AffineSpace
  (ULift.{u} (Fin 1)) S)`. Mathlib derives integrality of this scheme from integral S.
- Dimension at most n−1: `topologicalKrullDim (…) < (n : WithBot ℕ∞)`.
  For n positive this is exactly at most n−1; for n=0 it means dimension ⊥,
  hence the empty fibre. This avoids truncated natural subtraction at zero.
- Empty fibre convention: `topologicalKrullDim` takes values in `WithBot ℕ∞` and
  the empty space has dimension ⊥, the node's −∞. No reducedness of X or Y is required.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.FunctionField`: its documented arbitrary integral-scheme
  clause reuses `AlgebraicGeometry.Scheme.functionField` from
  `Mathlib.AlgebraicGeometry.FunctionField`. The component-product definition is not
  substituted for an integral function field.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`,
  its structural Over map, `AffineSpace.reindex` and its coordinate characterization.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, used
  through the recorded `Scheme.Hom.fiber` definition.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: the recorded dimension interface;
  its global dimension is Mathlib's `topologicalKrullDim`.

The module also imports the stated proof-dependency interfaces: Proper,
FinitePresentation, QuasiSeparated, Immersion, residue-field fibre localization,
transcendence bases/towers, `Scheme.finite_affine_tensor_base_change`,
`IsLocalization.prime_localRing_residueField_iso`, and
`topologicalKrullDim_closed_irreducible_eq_trdeg`. The proof docstring follows all
six recorded proof steps, including the affine-cover chain argument rather than
assuming a finite component decomposition for an arbitrary open X.

Edge cases checked: m=0 gives no coordinate r; n=0 forces the coordinate generic
fibre empty, not merely zero-dimensional. X or Y empty gives dimension ⊥.
Constant/algebraic coordinates have empty generic fibre. Arbitrary non-Noetherian
integral bases, all characteristics, and nonreduced X and Y remain allowed.
All schemes live in a single arbitrary explicit universe u, with finite indices lifted.

Searches for an existing statement:

- `msearch.py … leanfinder "The generic fiber of a coordinate projection to the
  affine line has dimension at most the dimension of the generic source fiber minus one"`:
  eight hits (smooth presentation dimensions, fibre ranges, projectivization, and
  polynomial-ring dimension lower bounds); none states the lemma.
- `msearch.py … loogle "AlgebraicGeometry.AffineSpace, topologicalKrullDim"`: zero hits.
- `msearch.py … grep "generic.*[dD]im|[dD]im.*generic" AlgebraicGeometry`: zero hits.
- `rg` in upstream WeilConjectures and project lean/Sheaf for the item id and generic
  dimension patterns: NoetherNormalization gives a generic dimension equality for
  finite surjections onto an affine space, not this coordinate bound; the other
  matches concern curves and unrelated local dimension arguments.
- Read the full Mathlib AffineSpace API: `reindex` already supplies the coordinate
  projection, so there is no new helper definition. Read the blueprint node and
  scheme-conventions source, and each statement dependency's recorded declaration.

No statement dispute or node fault found. Validation uses only scompile.py and
prescribed delivery bookkeeping; no direct Git commands or live-library writes.

## Second reading by NA

Independently read the sandbox node and module, the original blueprint lemma at
sec-smooth-purity/sk-prop-sf-cbc/lem-fin-coordinate-generic-dimension.md, and its
scheme-conventions source. The source introduces no standing Noetherian,
separatedness, reducedness, or characteristic hypothesis. Also read Stacks
Morphisms 01RV and 01RW in morphisms.tex: the generic stalk of an integral
scheme is its function field and equals its generic residue field.

Object/hypothesis/conclusion checklist (all verdicts: exact):

- Integral scheme S: `(S : Scheme.{u}) [IsIntegral S]`. Read the class in
  Mathlib.AlgebraicGeometry.Properties: nonempty and domain sections on every
  nonempty open. This is the integral-scheme dependency, including irreducibility.
- Its function field K: no independent choice is needed. Read
  `Scheme.functionField` and its integral field instance in Mathlib's FunctionField,
  and the project's FunctionField module. The dependency explicitly reuses this
  generic stalk for arbitrary integral schemes. The fibre at `genericPoint S`
  therefore is the specified X_K, not a component product for a general curve.
- Finite affine dimension m and bound n: `{m n : ℕ}`. Affine space is exactly
  `AffineSpace (ULift.{u} (Fin m)) S`; its Mathlib definition is the polynomial
  affine-space base change. The finite lifting changes only the index carrier.
- Closed immersion Y into that space: `i` and `[IsClosedImmersion i]`. Read the
  recorded class: closed embedding and surjectivity on stalks, exactly the node.
- Open subscheme X of Y: `j : X ⟶ Y` and `[IsOpenImmersion j]`, the recorded
  locally-ringed-space open immersion. This allows any open, with no compactness
  condition; using a morphism rather than a literal open subset is equivalent.
- Bound on dim X_K: `hdim` applies `topologicalKrullDim` to the fibre of
  `j ≫ i ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)` at `genericPoint S` and
  bounds it by `(n : WithBot ℕ∞)`. This is the composite structural morphism.
- Every coordinate r: `(r : Fin m)` follows the common dimension hypothesis.
  Read `AffineSpace.reindex`, `reindex_over`, and `reindex_appTop_coord`: the
  constant singleton-to-coordinates function selecting `ULift.up r` sends the
  line's coordinate to exactly coordinate r. It is not an arbitrary function.
- Its generic fibre: the conclusion uses `.fiber` at
  `genericPoint (AffineSpace (ULift.{u} (Fin 1)) S)`. Mathlib's integral affine
  space instance supplies this generic point; no extra hypothesis is imposed.
  Read `Scheme.Hom.fiber`: it is the pullback along `fromSpecResidueField`, as
  required by both the fibre and fibre-product dependency nodes.
- Dimension at most n minus one, including the empty convention: the conclusion
  is `< (n : WithBot ℕ∞)`. Read Mathlib's `topologicalKrullDim`, the supremum
  of lengths of chains of irreducible closed subsets, and the recorded upstream
  KrullDimension module. Its bottom is the stipulated minus infinity. For n > 0
  this strict inequality is exactly the stated integer bound; for n = 0 only
  bottom satisfies it. This is not truncated natural subtraction.

Edge cases: m = 0 makes `Fin m` empty, so the assertion about each coordinate
is vacuous, as in the source. Empty X or Y and constant/algebraic coordinates
are allowed and have empty generic coordinate fibre. Integral S cannot be
empty, precisely as in the source. The n = 0 case forces that fibre empty.
Nilpotents in X and Y, non-Noetherian S, and all characteristics are allowed.
The arbitrary explicit universe u is shared only by schemes that already have
morphisms between them; there are no test-object quantifiers or size equalities
that exclude a case. Every variable and universe in the signature is bound.

Independent searches: msearch leanfinder, "dimension of the generic fibre over a
coordinate of affine space", returned eight smooth-presentation, polynomial-rank,
and dimension-lower-bound hits, none the assertion. Loogle for
`AlgebraicGeometry.AffineSpace.reindex` returned the canonical coordinate API
(including its coordinate formula), not a dimension theorem. msearch grep for
`coordinate.*fiber|fiber.*coordinate` in AlgebraicGeometry returned no hits.
Direct rg in Mathlib/AlgebraicGeometry, upstream WeilConjectures, and project
lean/Sheaf for generic/dimension/Krull combinations and the declaration name
found no duplicate. Opened the closest upstream NoetherNormalization theorem:
it computes dimension r for a finite injective polynomial presentation, which
is not this coordinate generic-fibre bound. Thus the new theorem is needed;
the existing coordinate and fibre definitions are correctly reused.

No mismatches found; no Lean or node changes needed. There are no new definition
nodes, dependency modules, statement corrections, hollow definitions, or proved
lemmas to audit. The source/blueprint docstrings and all six proof steps match
the node, including the chain argument replacing the source's unnecessary finite
component argument. The node's lean.statement equals the signature verbatim.
Compiled the sole delivered module with the required scompile.py wrapper:
sandbox and library compilation both succeeded without errors or warnings.
