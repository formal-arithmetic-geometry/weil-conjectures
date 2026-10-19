## Worker report

Reuse `AlgebraicGeometry.IsHProjective` from
`Sheaf.AlgebraicGeometry.Morphisms.Projective`, read in the existing project module
`lean/Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`, lines 37–44.
No module or new definition is written, and no statement is corrected.

Clause-by-clause correspondence:
- Arbitrary schemes and a morphism are the explicit universe-polymorphic binders
  `{X S : Scheme.{u}} (f : X ⟶ S)`.
- An integer N ≥ 0 is the existential `n : ℕ` in `exists_closedImmersion`.
- Projective space with exactly N+1 homogeneous coordinates is
  `ProjectiveSpace (ULift.{u} (Fin (n + 1))) S`.
  `ULift` changes only the universe of the coordinate set, not its elements.
- The embedding is the existential morphism `i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)`;
  the first conjunct is exactly `IsClosedImmersion i`.
- The second conjunct `i ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = f`
  is the required equality with the structural projection, written in categorical
  composition order. The projective-space `CanonicallyOver` instance defines that
  projection as `pullback.fst`.
- For a field `k : Type u` with `[Field k]`, and the specified structure morphism
  `f : X ⟶ Spec (.of k)`, the field clause means `IsHProjective f`.
  It is a use of precisely the same predicate, so needs no additional declaration.
  This does not impose any field hypothesis on the general morphism predicate.
- The selected predicate has no additional quasi-compactness conjunct. The nearby
  `IsProjective` class is not selected, since its signature adds that clause.

Dependency declarations inspected:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Scheme.Hom`
  morphisms, and `AlgebraicGeometry.Spec` / `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, a closed embedding with surjective stalk maps.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace` and `ProjectiveSpace.over`, whose structural
  morphism is the first pullback projection. Read its complete definition and docstring.
- `Mathlib.Algebra.Field.Defs`: `Field`, extending `CommRing` and `DivisionRing`.
The reused module already publicly imports the closed-immersion and projective-space
modules. The latter supplies schemes and spectra. The field clause merely specializes
its predicate, without requiring a new module or copy of any dependency.

Edge cases checked: n = 0 has one homogeneous coordinate, not zero; n is always
nonnegative; no nonempty, separated, Noetherian, or field condition is imposed on
X or S. Empty schemes are allowed. The universe lift makes every finite coordinate
set fit the scheme universe. Every field characteristic is covered by Field.

Searches performed:
- msearch.py leanfinder: “A morphism of schemes is H-projective if it factors through
  a closed immersion into finite projective space over its base”: eight hits on
  absolute Proj and properness, no matching Mathlib predicate.
- msearch.py loogle: `AlgebraicGeometry.IsHProjective, AlgebraicGeometry.IsProjective`:
  zero hits, unknown identifier IsHProjective.
- msearch.py grep: `IsHProjective|class IsProjective`, AlgebraicGeometry: zero hits.
- msearch.py leansearch: “projective scheme morphism closed immersion into finite
  dimensional projective space”: service unavailable, Internal Server Error.
- rg in the pinned upstream WeilConjectures source for `IsHProjective`,
  `class IsProjective`, and `def-kun-projective`: no defining declaration there.
  The newer upstream module named by def-pc-projective-morphism is absent locally.
- rg in lean/Sheaf: found IsHProjective in Morphisms/Projective.lean, then read its
  complete signature, defining field, and docstring; exact match as detailed above.
- rg in dag/lean_names_upstream.json: IsHProjective and IsProjective are indexed.
- Read the blueprint source def-kun-projective.md: it gives exactly the finite-space
  embedding convention and the structure-morphism specialization over a field.

No STATEMENT-DISPUTED flag and no mathematical node fault.

## Second reading by NA

Independently read the complete node, its blueprint source
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-projective.md`,
Stacks `morphisms.tex`, Definition `definition-projective` (01W8), and
`Sheaf.AlgebraicGeometry.Morphisms.Projective`, especially lines 37–44.
Stacks begins with an arbitrary morphism of schemes and its second clause is
H-projectivity; there is no standing Noetherian, field, or finiteness hypothesis
on the base. The blueprint chooses this finite projective-space convention.

Object/hypothesis/conclusion inventory and comparison:

- Schemes X and Y, and their morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  Read `Scheme` and `Scheme.Hom` in Mathlib's Scheme module (lines 42 and 74):
  locally affine locally ringed spaces and their morphisms. Exact; S renames Y.
- A nonnegative integer N: `∃ (n : ℕ)`. Exact; no upper bound is imposed.
- Projective space over that same base with N+1 homogeneous coordinates:
  `ℙ(ULift.{u} (Fin (n + 1)); S)`. Read the dependency node
  `def-nagata-projective-space-base-change` and its recorded upstream module:
  `ProjectiveSpace (n : Type u) (S : Scheme.{u})` is the pullback of the
  integral polynomial Proj along the terminal map. Its `over` instance has
  `hom := pullback.fst _ _`. This is exactly the node's base-change construction
  and specified projection, not an alternative relative Proj object.
- An embedding i of X into that projective space: the existential binder
  `(i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); S))` and `IsClosedImmersion i`.
  Read the recorded Mathlib declaration at ClosedImmersion.lean:45: closed
  topological embedding with surjective stalk maps. Exact closed immersion.
- Factorization over Y: `i ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = f`.
  Exact composition with the structural projection, with the equality reversed
  from the prose and categorical composition order accounted for. The order
  is first n, then i, followed by both required properties.
- A field k and a specified structure morphism to Spec k: read `Field`
  (Algebra/Field/Defs.lean:180), `Spec` and `Spec.map`
  (Scheme.lean:470,479), against the corresponding dependency nodes. For
  `(k : Type u) [Field k]`, `(X : Scheme.{u})`, and the specified
  `f : X ⟶ Spec (.of k)`, the field clause is precisely `IsHProjective f`.
  A scheme with an Over instance instead uses `IsHProjective (X ↘ Spec (.of k))`.
  This is specialization of the same predicate and needs no second definition.

Edge cases: n=0 gives one coordinate, as required; the node never asks for an
empty coordinate set (that would mean dimension -1). Empty schemes and empty
bases remain allowed, with no Nonempty instances. No zero-object restriction
is introduced. The general base is a scheme, not a field; the field clause
covers every characteristic. The bound universe u is arbitrary, and ULift
places the finite coordinate type in that universe without changing its
cardinality. There are no unbound variables or extra typeclass hypotheses.

Independent searches, using different wording from the first worker:
`msearch.py ... loogle '"H-projective"'` found no matching declaration;
`leanfinder 'Scheme morphism admits closed embedding in projective n-space
relative to arbitrary base'` returned eight Proj/properness and closed-immersion
hits, none defining this predicate. `leansearch 'relative finite projective
space closed immersion morphism'` was unavailable (Internal Server Error).
Searched declaration lines for projectivity, HProjective, and projective-space
names throughout the pinned WeilConjectures source, Mathlib algebraic geometry,
and lean/Sheaf. The matching predicate is the existing side-project
`AlgebraicGeometry.IsHProjective`; alternatives include module projectivity,
quasi-projectivity and `IsProjective` with its extra quasi-compactness field.
Read the entire matching class and its docstring rather than relying on its
name. Reuse is required by H4.

Verdict: no mismatch found and no Lean or node change needed. The existing
module's prose about `IsProjective` is not the selected declaration; this
record intentionally selects `IsHProjective` and its exact defining field.
No new nodes, dependency modules, statement correction, hollow definition,
new proof, or disputed statement. The existing declaration has its original
source and blueprint docstring; no duplicate module/docstring is introduced.
The node's `lean.statement` is verbatim its class signature, excluding `where`.
Delivery checks run the existing-declaration server probe through scompile;
there are no delivered Lean files requiring separate compilation.
