## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine` states
`AlgebraicGeometry.Scheme.Modules.exists_affine_section_neighbourhood_of_finite`.
Its only proof is `sorry`, as required for stage 2. No definition is added and no node
statement is changed.

Hypotheses and conclusions, clause by clause:

- The scheme Y is `(Y : Scheme.{u})`, with arbitrary explicit universe `u`.
- The invertible O_Y-module is `(M : Y.Modules) [M.IsInvertible]`.
- Absolute ampleness is `(hM : IsAmple Y M)`; quasi-compactness is already part of this
  dependency definition, so no additional hypothesis is imposed.
- The finite set of points is `(E : Set Y) (hE : E.Finite)`.
- The open neighbourhood is `(W : Y.Opens) (hEW : E ⊆ (W : Set Y))`.
- The positive integer is `∃ n : ℕ, 0 < n ∧ ...`.
- The global section of M^{tensor n} is
  `s : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤)`.
- The open `U : Y.Opens` represents exactly Y_s: the final universal equivalence says
  membership in U is equivalent to the germ of s lying outside the maximal ideal times
  the whole stalk module. This is the precise nonvanishing condition in the ampleness node,
  not just nonzero as a stalk element. The extra existential open is a representation of
  the already open locus, not a new assumption or a different locus.
- E subset Y_s is `E ⊆ (U : Set Y)`; Y_s subset W is `U ≤ W`.
- Y_s affine is `IsAffineOpen U`, meaning its open subscheme is affine.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (locally ringed space locally
  affine), `Scheme.Hom` (morphisms of locally ringed spaces), and `Scheme.Opens`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (locally isomorphic to the structure sheaf)
  and `tensorPow` (zeroth power is the tensor unit; successor is tensor product).
- `Sheaf.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`, absolute
  ampleness on any scheme using compactness and affine section loci, as recorded by
  `def-weil-pbc-ample-invertible-module`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffineOpen`.
  These declarations are available through the single used import of the ample module.

Edge cases checked before writing: E may be empty, in which case n=1 and the zero section
have empty affine locus, for arbitrary W. The empty scheme is permitted without a Nonempty
binder. W may be empty (forcing E empty), equal to Y, or non-quasi-compact; nothing requires
W itself to carry an ample restriction. No separatedness, Noetherian, field, characteristic,
or projectivity hypothesis is added. n=0 is correctly excluded. On P^1 a finite set need not
lie in the nonvanishing locus of a degree-one section, which is why n is existential and
has no upper bound.

Searches made using `/home/ubuntu/weil-launcher/msearch.py` (recorded in searches.jsonl):

- LeanFinder: "An ample invertible sheaf has a positive tensor power section whose affine
  nonvanishing locus contains a finite set and lies in a prescribed open". Eight hits concern
  structure-sheaf basic opens and localization, not this ample-line-bundle theorem.
- Loogle: "IsAmple". No hits; unknown identifier.
- Mathlib grep: "IsAmple|ample.*finite|finite.*ample", AlgebraicGeometry.
  One unrelated hit in Morphisms/AffineAnd.lean, no matching statement.
- LeanSearch: "ample line bundle finite set affine section neighbourhood".
  Service unavailable (Internal Server Error); no verdict inferred.
- rg of the same concept and the node id in WeilConjectures, lean/Sheaf, and
  dag/lean_names_upstream.json: no exact statement. The upstream `AlgebraicGeometry.IsAmple`
  is the projective-over-a-field notion, whereas the dependency's landed absolute definition
  is the appropriate one. Explicit collision search for the chosen declaration name in
  Mathlib, WeilConjectures and lean/Sheaf produced no hits.

Source checked at https://stacks.math.columbia.edu/tag/09NV (local Stacks TeX is absent).
The source statement matches the node with no correction needed. The docstring includes
all three DAG proof steps and named proof dependencies, including the empty-set case and
the use of U' intersect W without assuming W quasi-compact.

## Second reading by K1

I read the node `lem-sc-ample-finite-principal-affine` and the Stacks source
Properties Lemma 09NV before checking the Lean file. The statement's objects and
clauses are rendered as follows, with no mismatch found:

- `Y` is `(Y : Scheme.{u})`, with no nonemptiness, separatedness, Noetherian, field,
  characteristic, or universe restriction beyond the explicit universe.
- `\mathcal M` is `(M : Y.Modules)` with `[M.IsInvertible]`, and ampleness is
  `(hM : IsAmple Y M)`, using the project's absolute `IsAmple` definition.
- `E ⊆ Y` and finiteness are `(E : Set Y) (hE : E.Finite)`.
- The prescribed open and containment are `(W : Y.Opens)` and
  `(hEW : E ⊆ (W : Set Y))`.
- The conclusion introduces `n : ℕ` with `0 < n`, a global section
  `s : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤)`, and an open `U : Y.Opens`.
  The clauses `E ⊆ U`, `U ≤ W`, and `IsAffineOpen U` render respectively
  `E ⊆ (U : Set Y)`, `U ≤ W`, and `IsAffineOpen U`.
- The final equivalence, for every `y : Y`, identifies `U` exactly with the section's
  nonvanishing locus: the germ of `s` is outside the maximal ideal times the whole
  stalk module. Thus `U` is the node's `Y_s`, rather than an arbitrary auxiliary open.

The source's empty-set clause is covered: `E` is allowed to be empty, `n = 0` is
excluded by `0 < n`, and the empty nonvanishing locus can be represented by the zero
section. Empty schemes and empty or non-quasi-compact `W` are not excluded. The zero
object and all characteristics remain permitted by the signature.

I repeated the existing-definition searches (LeanFinder/Loogle, LeanSearch, and grep
through Mathlib, `WeilConjectures`, `lean/Sheaf`, and upstream names). They found no
declaration of this theorem; the only related declaration is the dependency
`IsAmple`, whose locus formulation is used directly. No new definition or dependency
module is needed.

No mismatch was found, so no statement, node field, or Lean code was changed. The
module compiles cleanly with `scompile.py`; its only proof is the required `sorry`.
