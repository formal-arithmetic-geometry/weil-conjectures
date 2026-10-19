## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.GenericallyFiniteQuasiFiniteOverDimensionOne`
states `AlgebraicGeometry.quasiFiniteAtPoint_of_generic_algebraic_of_local_dim_le_one`.
Its conclusion is that a locally finite type morphism `g : Z ⟶ S` is
`Scheme.Hom.IsQuasiFiniteAtPoint g z` for every `z` over `s`, assuming the local
ring at `s` is Noetherian of Krull dimension at most one and all generic component
residue-field extensions are algebraic. The proof is `sorry`, as required at stage 2.

The Lean rendering of each clause is:

* The schemes and morphism are `{Z S : Scheme.{u}}` and
  `(g : Z ⟶ S)`, with `[LocallyOfFiniteType g]`; the point is `(s : S)`.
* The Noetherian local-ring hypothesis is
  `[IsNoetherianRing (S.presheaf.stalk s)]`.
* The dimension bound is
  `(hdim : ringKrullDim (S.presheaf.stalk s) ≤ 1)`.
* For every set `T` in `irreducibleComponents Z` and every
  `η : Z` with `IsGenericPoint η T`, the algebraicity hypothesis is
  `@Algebra.IsAlgebraic (S.residueField (g η)) (Z.residueField η) _ _
  (g.residueFieldMap η).hom.toAlgebra`.
* The conclusion is
  `∀ z : Z, g z = s → Scheme.Hom.IsQuasiFiniteAtPoint g z`, where
  `IsQuasiFiniteAtPoint` is the recorded declaration from
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`.

Dependencies used are `Mathlib.AlgebraicGeometry.Scheme` for `Scheme` and scheme
morphisms (`AlgebraicGeometry.Scheme`),
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` for
`AlgebraicGeometry.LocallyOfFiniteType`,
`Mathlib.RingTheory.Noetherian.Defs` for `IsNoetherianRing`,
`Mathlib.RingTheory.KrullDimension.Basic` for `ringKrullDim`,
`Mathlib.Topology.Sober` for `IsGenericPoint`,
`Mathlib.Topology.Irreducible` for `irreducibleComponents`,
`Mathlib.AlgebraicGeometry.ResidueField` for `Scheme.residueField` and
`Scheme.Hom.residueFieldMap`, and `Mathlib.RingTheory.Algebraic.Defs` for
`Algebra.IsAlgebraic`. The project dependency
`pqf-def-quasifinite` is imported as
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, declaration
`AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`; its recorded interface is
usable and no dependency repair is needed. The remaining definition-node
records are Mathlib matches and are used directly.

Edge cases checked against the statement and source: an empty scheme `Z` makes the
generic hypothesis and conclusion vacuous; an empty fibre over `s` is allowed; the
bound includes dimension zero; nilpotents do not alter the stalk or residue-field
formulation; and no properness, normality, or global Noetherian assumption was added.
The algebraicity hypothesis is pointwise at all generic points of all irreducible
components, including components whose generic point is not mapped to `s`.

Searches made with `msearch.py`:

* `leanfinder`: “A locally finite type morphism of schemes with algebraic residue
  field extensions at generic points is quasi-finite over points with Noetherian
  local ring of Krull dimension at most one”. It returned Mathlib's generic
  `LocallyQuasiFinite`, `LocallyOfFiniteType`, and ring quasi-finite criteria, but
  no theorem with the generic algebraicity and dimension-one hypotheses.
* `loogle`: “AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint,
  AlgebraicGeometry.LocallyOfFiniteType, Algebra.IsAlgebraic, ringKrullDim”. It
  returned 0 hits because the project predicate is not a Mathlib declaration.
* `grep`: “GenericallyFinite|generic.*algebraic.*quasiFinite|0AB6” in
  `WeilConjectures`. It returned 0 hits for this statement.

The existing sibling
`Sheaf.AlgebraicGeometry.Morphisms.GenericallyFiniteProperNearDimensionOne` was
read: its properness theorem uses the same explicit residue-field algebraicity
encoding, confirming the binder shape. It is a distinct stronger conclusion and
cannot replace this node.

## Second reading by N4

I reread the node JSON, every statement dependency, and the full declarations used
above. The morphism hypothesis is exactly local finite type; the only base
hypotheses are the single stalk's `IsNoetherianRing` instance and `≤ 1` bound; the
generic clause quantifies precisely over irreducible components and their generic
points; and the conclusion quantifies exactly over points mapping to `s`. The Lean
signature has no properness, normality, global Noetherian, or other extra hypothesis.
The module compiled cleanly with `scompile.py`; the only initial issue was a private
import of the project predicate, fixed by making that import public. No statement
change or new node was needed.
