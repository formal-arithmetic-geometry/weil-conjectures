## Worker report

The module `Sheaf.AlgebraicGeometry.SeparatedAffinePairNeighbourhoods` states
`AlgebraicGeometry.Scheme.separated_of_affine_pair_neighbourhoods`. Its single
proof is `sorry`; it introduces no definition or auxiliary theorem. The copied
node changes only in `lean`. The source paragraph was read in
`literature/stacks-project/more-morphisms.tex`, following
`definition-ind-quasi-affine` (Tag 0AP6). It asserts separatedness because each
pair of affine opens lies in a separated open; the node isolates that argument.

Hypothesis and clause correspondence:

- An arbitrary scheme is `X : Scheme.{u}`; `u` is explicitly declared.
- Every pair of affine open subschemes is quantified as `∀ A B : X.Opens,
  IsAffineOpen A → IsAffineOpen B → ...`. Both opens may be empty or equal.
- The witnessing open subscheme is `∃ W : X.Opens`.
- Containment of the union is `A ⊔ B ≤ W`, since join in the opens lattice is union.
- Separatedness of that open over Spec Z is `W.toScheme.IsSeparated`.
  Mathlib's `Scheme.IsSeparated` is separatedness of `terminal.from`, defined
  by the diagonal being a closed immersion. The terminal scheme is canonically
  isomorphic to Spec of the universe lift of Z, by `specULiftZIsTerminal` in
  `Mathlib.AlgebraicGeometry.Limits`; this is precisely absolute separatedness.
- The first conclusion is
  `IsClosedImmersion (pullback.diagonal (terminal.from X))`, the absolute diagonal
  into the fibre product over the terminal scheme, hence over Spec Z.
- The separatedness consequence is `X.IsSeparated`.
- The quasi-separatedness consequence is `QuasiSeparated (terminal.from X)`.
  This is the node's definition of a quasi-separated scheme; equivalence with
  `QuasiSeparatedSpace X` is available in Mathlib.
- No quasi-compactness binder occurs for either X or W. No finiteness or
  nonemptiness condition is imposed. All variables and the universe are explicit,
  with no local notation, local instance, `let`, or `show` in the signature.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`. Open subschemes and affineness use Mathlib's
  `Scheme.Opens.toScheme` and `IsAffineOpen`, not a new encoding.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections and
  diagonal, from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
  and the scheme pullback instances in `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, a closed embedding with
  surjective stalk maps.
- `def-weil-proper-morphism`: the recorded `AlgebraicGeometry.IsSeparated`
  (among its `lean.declarations`), exposed by
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; it means a closed-immersion
  diagonal. `Scheme.IsSeparated` is the absolute specialization. No properness
  assumption is introduced.
- `def-weil-quasi-separated-morphism`: `AlgebraicGeometry.QuasiSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, meaning a quasi-compact
  diagonal.

Proof dependency modules are imported privately: the open-product lemmas are in
`Mathlib.AlgebraicGeometry.Pullbacks` and `PullbackCarrier`; the open-preimage
pullback is in `Restrict`; the affine-cover closed-immersion criterion uses
`Morphisms.ClosedImmersion`, `Morphisms.Affine`, `Morphisms.Basic`; and
separated-implies-quasi-separated is in `Morphisms.Separated`. Public imports
already provide the statement-side parts. All these dependencies are Mathlib
leaves; no missing interface or new node is required. The declaration docstring
carries all four proof steps, including the covering, pullback identification,
affine-local closed-immersion test, and final quasi-separatedness consequence.

Edge cases checked mathematically before writing:

- Empty X: the opens and witness can be empty; its diagonal is a closed immersion.
- Affine X: W = X witnesses every pair, and the conclusion is the affine case.
- A = B, and either or both opens empty: containment has its ordinary meaning.
- Infinite disjoint unions of affine schemes: each pair of affine opens meets
  finitely many components; their union lies in a separated finite union of
  components. The theorem applies although X need not be quasi-compact.
- The affine line with doubled origin fails the hypothesis for its two standard
  affine charts, whose union is X; it is therefore correctly excluded.
- W itself need not be quasi-compact. The proof only refines arbitrary open
  covers by affine covers, never by finite subcovers.

Searches performed through the prescribed msearch wrapper:

- LeanFinder: "A scheme is separated if every pair of affine open subschemes is
  contained in a separated open subscheme". Eight hits: the separated classes,
  their affine/quasi-affine instances, locality, and quasi-separatedness. None
  gives the pairwise separated-neighbourhood criterion.
- Loogle: `AlgebraicGeometry.Scheme.IsSeparated, AlgebraicGeometry.IsAffineOpen`.
  Zero hits.
- Mathlib grep: `isSeparated_of|[Pp]air.*[Ss]eparated|[Ss]eparated.*[Nn]eigh`
  under AlgebraicGeometry. Five hits, about monomorphisms, injective morphisms,
  and equality of rational maps; none states the item.
- Direct rg over both `lean/WeilConjectures` and `lean/Sheaf` with
  `separated_affine_pair|pair.*[Ss]eparated|[Ss]eparated.*[Nn]eigh|isSeparated_of`.
  The upstream affine separating-pair cover criterion requires affine
  intersections and separating-pair ring maps, rather than the node's hypothesis;
  its full signature and docstring were read. Other hits concern unrelated
  separated morphisms, approximation, or curve results. No exact match.
- Direct grep of the item id under `lean/WeilConjectures`: no result.

There is no statement correction or disputed clause. The live node's passed
stage-1 review by Q02 is preserved verbatim; there is no repair note reopening
that review. This delivery adds its first Lean statement binding.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
