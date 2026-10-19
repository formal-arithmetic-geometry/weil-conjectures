## Worker report

The module `Sheaf.AlgebraicGeometry.NodalContractionEulerDefect` states
`AlgebraicGeometry.nodal_contraction_euler_defect`. The only theorem has proof `by sorry`.
No definitions or helper theorems are introduced. The natural-language node statement and its
seven-step proof are unchanged. The declaration docstring contains all seven steps, including
the complementary subcurve, finite-birational comparison, closed-union exact sequence,
Euler additivity, nodal normalization formula and integer substitution.

Hypotheses and clauses, in the order of the natural-language statement:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field `k` | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Proper reduced `k`-schemes `C,D` | `C D : Scheme.{u}`, their `Over (Spec (.of k))` instances, `IsProper` on their structure maps, and `IsReduced C`, `IsReduced D` |
| Pure dimension one of both schemes | `hC : C.IsPureDimension 1` and `hD : D.IsPureDimension 1` |
| Proper morphism of the `k`-schemes | `f : D ⟶ C`, `[f.IsOver (Spec (.of k))]` and `[IsProper f]` |
| Smooth rational point `y` | `y : C`, `hy : IsClosed ({y} : Set C)` and `hysmooth : y ∈ (C ↘ Spec (.of k)).smoothLocus` |
| Reduced closed fibre `B` | `[IsReduced B]`, `i : B ⟶ D`, `[IsClosedImmersion i]`, `hB : Set.range i = f ⁻¹' {y}` |
| Nonempty connected curve, pure dimension one | `[ConnectedSpace B]` (includes nonemptiness) and `hBpure : B.IsPureDimension 1` |
| `f` is an isomorphism on the complement | `hoff : IsIso (f ∣_ (⟨{y}ᶜ, hy.isOpen_compl⟩ : C.Opens))` |
| Nodal on an open neighbourhood of `B` | `N : D.Opens`, `hN : Set.range i ⊆ N`, and `hnodal`, quantifying over every `x ∈ N` outside the smooth locus |
| Completed local ring `k[[u,v]]/(uv)` | `AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk x)) (D.presheaf.stalk x)`, a `Nonempty` ring equivalence to `MvPowerSeries (Fin 2) k ⧸ Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}` |
| Irreducible components `B_1,...,B_v` | `v : ℕ`, `components : Fin v ≃ irreducibleComponents B`, and the family `Z`, `j`, `hcomponents` |
| Reduced component structures | `[∀ a, IsIntegral (Z a)]`, `[∀ a, IsClosedImmersion (j a)]`, and `Set.range (j a) = (components a).1` |
| Component normalizations | `(Z a).normalization` with its canonical map `(Z a).fromNormalization` |
| Normalizations smooth, proper, connected curves over `k` | `hnormalizations` asserts `IsProper` and `Smooth` for the composite normalization/component/fibre/structure map and `ConnectedSpace (Z a).normalization` |
| `g_i = dim_k H^1` of the normalization | `.genus` of that composite, using the dependency's `Scheme.Hom.genus`; on these smooth proper curves this is exactly the cohomological genus by `Scheme.genus_eq_arithmeticGenus` |
| `χ(E)` of the structure sheaf | `Scheme.Modules.eulerChar k (SheafOfModules.unit E.ringCatSheaf)` for `E = C,D` |
| `e`, internal nodes, self-node once | `Nat.card {b : B // b ∉ (i ≫ D ↘ Spec (.of k)).smoothLocus}` |
| `r`, distinct boundary points, ambient closure in `D` | `Nat.card {x : D // x ∈ Set.range i ∩ closure (Set.range i)ᶜ}` |
| Difference identity | The displayed equality in `ℤ` with `(v : ℤ)`, the two cardinalities cast separately to `ℤ`, and `∑ a : Fin v, (...genus : ℤ)` |
| No equal-Euler, zero-genus or tree assumption/conclusion | None appears among the hypotheses or the conclusion |

The closed-point encoding is exact, not an extra condition: Mathlib's
`AlgebraicGeometry.pointEquivClosedPoint` identifies closed points of a locally finite-type
scheme over an algebraically closed field with its rational points. This declaration and its
full signature/docstring were read in `Mathlib.AlgebraicGeometry.AlgClosed.Basic`.
The restriction has domain the open complement of the fibre support by `hB`.
A reduced closed subscheme of a scheme is uniquely determined by its closed support, so
`i` and `hB` specify the reduced closed fibre, rather than an arbitrary replacement for it.
Similarly, integral closed immersions with the prescribed component supports give exactly
the reduced components. This is a parametrization of the objects the node names, with no
extra geometric hypothesis. The component dimension and normalization dimension are inherited
from `hBpure`; smooth/proper/connected normalizations therefore are curves of dimension one.
The equivalence with `Fin v` is precisely a finite enumeration, justified by proper finite type
and Noetherianity. No arbitrary larger index universe is used.

The recorded genus definition is via differential forms, not literally `H^1`. I read its full
source and the cohomological definition `Scheme.arithmeticGenus` in
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`, together with
`Scheme.genus_eq_arithmeticGenus` in `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`.
This equality identifies the dependency's genus with the node's formula on the stated smooth
proper normalizations (smooth curves have relative dimension one here). No second genus
definition is needed. In particular all coefficient actions come from the indicated composites
to `Spec k`; the arbitrary genus of a curve over a different field is not substituted.

Dependency declarations used, with full signatures and docstrings read in their source:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraic-closedness notion named
  by the `AlgebraicClosure`/`IsAlgClosure` Mathlib match of `def-weil-algebraic-closure`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper` (its universally
  closed instance supplies quasi-compactness, so this is proper finite type).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` and `IsIntegral`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, used by the shared pure-dimension
  definition; its value is `WithBot ℕ∞`, including the empty-space convention.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `Scheme.Hom.smoothLocus`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Mathlib.RingTheory.AdicCompletion.Basic`/`.Algebra`: `AdicCompletion` and its ring structure.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and `MvPowerSeries.X`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, the maximal irreducible subsets.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization` and `Scheme.fromNormalization`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.Scheme.Hom.genus`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar`, `Modules.finrankH`.

The item's `stmt_deps` gains the already recorded nodes `def-weil-pure-dimension`,
`def-weil-closed-immersion`, and `def-pc-integral-scheme` for the shared declarations above.
No new node or dependency repair is required.

Every already recorded project proof-dependency module is imported without `public`:
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`,
`WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`,
`WeilConjectures.AlgebraicGeometry.Regular`,
`Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`.
The finite-type/Noetherian and proper permanence Mathlib inputs are exposed by these imports.
The two genuine proof dependencies `lem-trf-nodal-curve-normalization-euler` and
`lem-trf-nodal-subcurve-boundary` have no recorded declaration on the inspected base, so no
module import can yet be added for them. They are not statement prerequisites: the current
statement uses only the existing completion, smooth locus, component and genus notions.
No import is omitted for an import cycle.

Edge cases checked before writing and rechecked against the file:

- `ConnectedSpace B` excludes an empty fibre; pure dimension one excludes a point fibre.
  No unnecessary nonemptiness assumptions on `C,D` are present; these follow from `y` and `B`.
- Disconnected `C,D` are allowed. There is no global smoothness or nodality requirement.
- An empty boundary has `Nat.card = 0`; no positive-`r` hypothesis is introduced.
- A one-component smooth exceptional curve contributes `1 - r - g`; a self-node subtracts
  one because the counted type consists of points, not branches. Distinct component nodes
  are also counted once. Boundary points are intrinsic smooth points of `B` and do not enter
  the internal-node count, by the stated nodal-neighbourhood assumption and Stacks 0E38.
- A rational tail attached once has `v=1,e=0,r=1,g=0`, hence defect zero. Replacing it by a
  smooth positive-genus tail gives defect `-g`, testing both the sign and absence of a
  zero-genus assumption. A self-nodal rational tail has defect `-1`. A reducible tree of
  rational components attached once has `v-e-r=0`, without asserting all fibres are trees.
- All node and boundary sets are finite by proper finite type and nodality near `B`;
  `Nat.card` consequently is their usual finite cardinality. It adds no finiteness hypothesis.
- The right side is evaluated in `ℤ`, avoiding truncating natural subtraction; arbitrary
  characteristic, including two, is allowed by the equation `uv=0` and all the hypotheses.
- The scheme and field share the scheme universe as in the recorded genus/cohomology APIs;
  any such geometric input has a representation in a common universe. There are no free
  auto-bound variables or universes.

Searches made before writing (the prescribed `msearch.py` wrapper, group NP and this item):

- `leanfinder`, query “Euler characteristic difference under contraction of a proper nodal
  subcurve to a smooth point equals components minus internal nodes minus boundary points
  minus normalization genera”: no matching theorem returned.
- `leanfinder`, query “coherent Euler characteristic of a nodal curve equals number of
  components minus nodes minus sum of genera”: eight hits, on `IncidenceAlgebra.eulerChar_prod`
  and Weierstrass division-polynomial/affine-curve lemmas. Their signatures concern incidence
  algebras or a single elliptic curve, not the coherent Euler characteristic of a contraction.
- `loogle`, query `Scheme.Modules.eulerChar, Scheme.Hom.genus, Scheme.normalization`: zero
  hits, unknown identifier `Scheme.Modules.eulerChar`; these are project, not Mathlib names.
- `grep`, query `nodal.*euler|euler.*nodal|nodal.*contraction`, Mathlib AlgebraicGeometry:
  zero hits.
- Direct `rg` with nodal/Euler/contraction patterns in the upstream `WeilConjectures` and
  project `lean/Sheaf` trees found no statement of this numerical identity. Related tree
  and normalization-adjunction modules were read and do not state it.
- Exact node-id and declaration-name searches in upstream source, project source and
  `dag/lean_names_upstream.json` found no existing declaration for this item.
- The existing pure-dimension node/module was found by project-source and DAG search, so it
  is reused; no private pure-dimension predicate is introduced.

Sources checked: the archived local Stacks text for Tags 0E38, 0CBW and 0C1R, and
[Temkin's paper](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf), Appendix B,
printed pp. 57--58. The numerical formula is the Euler version before imposing the equal-genus
hypothesis of Corollary B.2; the node's explicit proof supplies the complementary-subcurve
argument for a smooth target point and the possible disconnected ambient schemes.

Validation: `scompile.py NP lem-trf-nodal-contraction-euler-defect` compiled the module in
both sandbox and library paths, cleanly, with no errors or extra warnings. The required delivery
dry run passed preflight and per-file compilation (`OK (dry run)`, commit `b581212635`). No statement fault or
`STATEMENT-DISPUTED` finding remains.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
