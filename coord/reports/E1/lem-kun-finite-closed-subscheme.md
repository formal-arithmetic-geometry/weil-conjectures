## Worker report

The module states `AlgebraicGeometry.IsClosed.finite_of_finiteType_over_field_of_closed_points`
with a `sorry` proof. It asserts the finiteness of a closed subset of a scheme of finite type
over a field when all its points are closed.

Hypotheses and conclusion, clause by clause:

- `K : Type u` and `[Field K]` render the arbitrary base field; no restriction on its
  characteristic or cardinality is introduced.
- `X : Scheme.{u}` renders the scheme, using Mathlib's `AlgebraicGeometry.Scheme`.
- `f : X ⟶ Spec (.of K)` is the structure morphism to the field spectrum.
- `[LocallyOfFiniteType f] [QuasiCompact f]` together mean that `f` is of finite type.
- `E : Set X` and `hE : IsClosed E` render the given closed subset of the underlying space.
- `hclosed : ∀ x ∈ E, IsClosed {x}` renders that every point of `E` is closed in `X`.
- `E.Finite` is precisely the conclusion that this subset is a finite set of points.

Statement dependencies used: `def-pc-scheme` is `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` in `Mathlib.AlgebraicGeometry.Scheme`;
`def-weil-finite-type-morphism` is `AlgebraicGeometry.LocallyOfFiniteType` in
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `AlgebraicGeometry.QuasiCompact` in
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`. Their full signatures and docstrings
were checked in the Mathlib source. No private definition is introduced.

Edge cases: `E = ∅` is allowed, as is the empty scheme; no nonemptiness or positive
dimension assumption is made. `E = Set.univ` is allowed. All field characteristics and
all scheme universes at `u` are admitted. The field and scheme inhabit the same universe,
as required by Mathlib's `Spec (.of K)` and `Scheme.{u}` interface.

Searches for an exact declaration:

- `msearch leanfinder "a closed subset of a finite type scheme over a field all of whose
  points are closed is finite"`: eight related hits, none with this statement.
- `msearch loogle "NoetherianSpace, IsClosed, Set.Finite"`: no result; the service reported
  unknown identifier `NoetherianSpace`.
- `msearch grep "finite.*closed.*point|closed.*point.*finite" Topology`: four related
  results, none the statement.
- `rg` in `WeilConjectures` and `lean/Sheaf`, plus `rg` in Mathlib's AlgebraicGeometry and
  Topology trees: no exact statement. `grep -rn "lem-kun-finite-closed-subscheme"` in
  `WeilConjectures` also had no hit.
- A source theorem, `IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`
  in `WeilConjectures.Mathlib.Topology.KrullDimension`, requires a dimension bound, so it
  is not the same statement.

The Stacks Project source places were checked at tags 01T6 and 0BA8 online because the
`literature/stacks-project/` checkout is absent on this machine. The module docstring
follows the node's two proof steps: finite type over a field implies Noetherian, and a
Noetherian closed subset made of closed points has finitely many singleton components.

## Second reading by E1

I opened the node, its source place, the dependency records, and the module before
reviewing the statement. The node says: let `X` be a scheme of finite type over a field
`K`; let `E ⊆ X` be closed; if every point of `E` is closed in `X`, then `E` is finite.
The Lean renders each item as follows:

- The arbitrary field is `{K : Type u} [Field K]`. No characteristic, cardinality, or
  algebraic-closedness assumption is added, and the universe is unrestricted.
- The scheme is `{X : Scheme.{u}}`, using Mathlib's scheme and underlying topological
  space. It is in the same universe as `K`, as required by `Spec (.of K)`.
- The structure morphism is `(f : X ⟶ Spec (.of K))`.
- “Finite type over `K`” is exactly Mathlib's pair of typeclass hypotheses
  `[LocallyOfFiniteType f] [QuasiCompact f]`; the dependency record for
  `def-weil-finite-type-morphism` identifies this pair with the node's finite-type
  notion. No stronger finiteness or Noetherian assumption is present.
- The closed subset is `{E : Set X}` with `(hE : IsClosed E)`.
- “Every point is closed” is `(hclosed : ∀ x ∈ E, IsClosed {x})`, with the singleton
  taken in the topology of `X`, exactly as in the node.
- The conclusion is `E.Finite`, with no omitted quantifier or extra structure.

The node's proof has two clauses, both represented in the theorem docstring. First,
`lem-weil-pbc-finite-type-over-noetherian` applies because `Spec K` is Noetherian and
`f` is finite type, giving Noetherian `X`. Second,
`lem-sc-noetherian-closed-points-finite` applies to `hE` and `hclosed` and gives
`E.Finite`. The source places are Stacks Morphisms Lemma 01T6 and Properties Lemma
0BA8. The dependency declarations were checked against their records: the first uses
Mathlib's `LocallyOfFiniteType` and `QuasiCompact`, and the second is the exact
Noetherian closed-point finiteness statement.

Edge cases checked: `E = ∅` is permitted and the conclusion is immediate; a singleton
closed point is permitted; the empty scheme is permitted; no nonzero dimension or
nonemptiness is assumed; all field characteristics are admitted; and arbitrary scheme
universes are admitted through `Type u`/`Scheme.{u}`. The case `E = Set.univ` is also
included when every point of `X` is closed.

Existing-definition searches were rerun with `rg` over Mathlib and `WeilConjectures`,
the local `msearch.py` LeanFinder/Loogle/grep queries recorded in `searches.jsonl`,
and a direct search for the node id. They found no exact declaration. The nearby
`IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero` theorem has an
extra Krull-dimension hypothesis and is not this statement. The Lean file compiled
cleanly with `scompile.py`; no statement repair was needed. I changed only the theorem
docstring to enumerate the two proof steps and name their dependency nodes.
