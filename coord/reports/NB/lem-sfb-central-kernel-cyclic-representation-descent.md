## Worker report

The module states `AlgebraicGeometry.RationalRepresentation.centralKernel_cyclic_representation_descent`
with one `sorry`. It also supplies two real-data helpers belonging to the objects of this
node: `coordinatePullback` and `cyclicSubspace`. No new definition node or dependency repair
is needed. The mathematical statement, proof and proof dependencies are unchanged.
The statement dependencies instead cite the definition nodes
`def-sfb-hopf-action-module-data` and `def-sfb-affine-coordinate-hopf-algebra`.
The comodule subtype is written explicitly using their existing laws and Hopf instance.

Hypotheses, clause by clause:

- The field F is `{F : Type u} [Field F]`.
- H and G are `Scheme.{u}` with their given `Over (Spec (.of F))` structures,
  `GrpObj (H.asOver ...)`, `GrpObj (G.asOver ...)`, and `IsAffine` instances.
  Their coordinate Hopf structures are the existing canonical ones, not independently
  specified Hopf structures.
- q is a morphism of these schemes over F with `[IsMonHom q]`.
  `hq : (coordinatePullback q).toRingHom.FaithfullyFlat` is faithful flatness of the
  actual coordinate pullback. Mathlib's definition is faithfully flat scalar extension,
  hence tensor exactness and detection of zero modules as required.
- V is an F-module with `[FiniteDimensional F V]`; the explicit subtype `ρ : {c : V →ₗ[F] V ⊗[F] Γ(H, ⊤) //
  HopfAction.Coassociative F Γ(H, ⊤) V c ∧ HopfAction.Counital F Γ(H, ⊤) V c}`
  consists of its linear coaction and the existing coassociativity and counit identities.
- The vector v has `hv : v ≠ 0`.
- `hKv` states fixity after every commutative F-algebra extension. An R-point of H is
  an algebra map `x : Γ(H, ⊤) →ₐ[F] R`. It belongs to the scheme-theoretic kernel exactly
  when `x.comp (coordinatePullback q) = (Algebra.ofId F R).comp (Bialgebra.counitAlgHom F Γ(G, ⊤))`.
  Its action on the original vector is evaluation of its coaction,
  `x.toLinearMap.lTensor V (ρ.val v) = v ⊗ₜ[F] 1`.
  This is the node's explicit equivalent all-algebra formulation, not a test on rational
  points of reduced fields. In particular one may test on the coordinate algebra of K
  itself and its universal point.

Conclusions, clause by clause:

- `cyclicSubspace ρ v` is exactly `sInf` of the subspaces U containing v for which
  `ρ.val x` belongs to `LinearMap.range (U.subtype.rTensor Γ(H, ⊤))` for every x in U.
  Tensor injectivity over the field means this is precisely the family of subcomodules.
  The `sInf` is actual data, not a chosen object obtained from an unfinished existence proof.
- The first conjunct is `FiniteDimensional F (cyclicSubspace ρ v)`.
- The second gives `w` in that subspace with underlying vector v and `w ≠ 0`.
- The existential `ρW` in the explicit coassociative/counital coaction subtype on `cyclicSubspace ρ v` asserts stability
  of this actual intersection. Its displayed tensor-inclusion equality identifies it
  with the restriction of the original coaction, rather than an arbitrary coaction.
- The next conjunct says that every kernel point over every R fixes every vector of W,
  using the same canonical kernel equation as `hKv`. Applied to the universal K-point,
  this says that the restricted K-coaction itself is w mapped to w tensor 1.
- The final `∃! ρG` in the explicit G-coaction subtype on `cyclicSubspace ρ v` is unique descent.
  Its predicate is the exact equality `(1_W tensor q*) composed with ρG = ρW`.
  Thus both coaction identities and exact pullback agreement are retained.
- No centrality, reducedness, smoothness or finite-type assumption is made.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`, `IsMonHom`;
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents their precise scheme
  specializations; the upstream Cartesian.Grp module defines `GrpObj.ker`, `kerι` and
  their pullback diagram. The kernel is specified by its points in the statement,
  so no separate affine-kernel instance is assumed.
- Mathlib.LinearAlgebra.TensorProduct.Defs/Basic/Map: `TensorProduct`, `mk`, `lift`,
  `ext'`, `LinearMap.lTensor`, `LinearMap.rTensor`, and `LinearMap.range`.
- Mathlib.LinearAlgebra.FiniteDimensional.Defs: `FiniteDimensional = Module.Finite`.
- Sheaf.RingTheory.HopfActionModuleData (definition node
  `def-sfb-hopf-action-module-data`): `HopfAction.Coassociative` and `HopfAction.Counital`.
  The comodule subtypes are written out directly; no dictionary declaration is used.
- Sheaf.AlgebraicGeometry.HopfCoactionLinearization (definition node
  `def-sfb-affine-coordinate-hopf-algebra`): `HopfAction.coordinateHopfAlgebra` and its
  underlying `affineCoordinateHopfAlgebra`, the canonical structures without any
  theorem conclusion or finite-type assumption.
- Mathlib.AlgebraicGeometry.Group.Affine: `Spec.mapMulEquiv`. The helper uses its
  inverse function after conjugation by the canonical `isoSpec`, hence is the actual
  pullback of coordinates. This also avoids assuming an arbitrary map q*.
- Mathlib.RingTheory.RingHom.FaithfullyFlat: `RingHom.FaithfullyFlat`, defined as
  `Module.FaithfullyFlat` for the algebra structure of the ring map.
- Proof imports: `Module.Free.of_divisionRing` (Basis.VectorSpace), `Module.Free`
  (FreeModule.Basic), the algebra tensor-product maps (TensorProduct.Maps), and
  `Module.FaithfullyFlat.exact_amitsurComplex`
  (WeilConjectures.RingTheory.FaithfullyFlat.Amitsur). Its full signature and proof
  docstring give augmentation injectivity, degree-zero exactness and positive exactness.

Edge cases checked: the zero vector space has no nonzero v, so is excluded exactly
by the node's hypothesis, not by an extra assumption. A one-dimensional trivial
representation has W equal to its line and descends uniquely. For q an isomorphism,
K is trivial and cyclic W descends by coordinate identification. For G trivial,
K=H and a fixed v generates its trivial line. Frobenius of the additive group in
characteristic p has nonreduced kernel alpha_p: the coaction using t^p descends to
s under q*(s)=t^p; the all-algebra kernel equation includes this example. Infinite-type
affine H/G are included. Taking a common containing universe includes fields and
finite-dimensional spaces originally presented in different universes; no finite
cardinality of the coordinate algebra is assumed.

Searches performed (msearch.py and direct rg):

- LeanFinder query: `Rational coaction of an affine group scheme descends along a
  faithfully flat quotient if its kernel fixes a vector and its generated subcomodule`.
  Eight hits: faithfully flat ring descent, `comonadicExtendScalars`, affine faithful
  flatness, and related results; no match for the item.
- Loogle query `Coalgebra, Comodule`: zero hits, unknown identifier Comodule.
- Mathlib grep query `Comodule|coaction`, subdirectory Algebra: zero hits.
- LeanSearch query `A rational comodule over a group scheme has a smallest
  subcomodule containing a given vector`: eight hits, including `Submodule.span`,
  `LieSubmodule.lieSpan`, `Representation.invtSubmodule.coe_bot` and coinvariants;
  none is a rational group-scheme subcomodule construction or this theorem.
- Direct rg over Mathlib, WeilConjectures and Sheaf for `Subcomodule`, `subcomodule`,
  `IsSubcomodule`, cyclic-subcomodule/generated names, coaction and rational representation.
  Found and read the existing CoordinateComodule, HopfAction identities and RationalModule.
  The repaired statement expands the plain subtype using the existing HopfAction laws,
  as requested by H2; it introduces no competing comodule definition. RationalModule is the separately
  bundled finite-dimensional representation/Grothendieck-group interface, not needed here.
- Direct rg for `coordinatePullback`, `cyclicSubspace` and `centralKernelCyclic`
  found no existing exact helper names or item statement; unrelated
  `Abelian.Ext.coordinatePullbackIdentity` concerns boundary maps.
- Required rg/grep for the item id in WeilConjectures found no declaration.
- Read the node's recorded Milne source: Theorem 5.13, printed p.101, and Lemma 5.15,
  printed p.102. Their quotient and all-test-algebra invariance arguments are reproduced
  in the theorem docstring along with the node's coordinate/Amitsur extension to arbitrary
  affine groups. Read the current blueprint's finite-Tor stability statement/proof for
  context; this auxiliary algebraic-group input does not change the unit statement.

No statement correction, disputed claim or missing dependency interface remains.
Compilation uses scompile.py only; the compiler's expected sorry warning is permitted.
The maintainer supplies the independent review under the direct-delivery workflow.

## Repair of returned head a5d2bd3cef55

H2 is repaired by option (a) of the return. Removed the statement dependency
`lem-sfb-rational-representation-comodule-dictionary` and its public import. Added the
two existing definition nodes `def-sfb-hopf-action-module-data` and
`def-sfb-affine-coordinate-hopf-algebra`, after reading their current records and the
full law/instance definitions. Imported their recorded modules directly.
Expanded the comodule subtype at the parameter of `cyclicSubspace`, the input coaction,
the restricted coaction and the descended coaction. Every occurrence uses the original
`HopfAction.Coassociative` and `HopfAction.Counital` definitions. Added the direct
finite-dimensional import previously reached through the dictionary.

Compared the sandbox statement and dependency list with current main: the natural-language
statement remains identical, and main has the four original statement dependencies. The
new packet adds only the two definition nodes to those four. The returned theorem-node
dependency is absent. The Lean signature record is regenerated verbatim from the repaired
module. No dependency nodes are edited. The reviewer accepted all mathematical clauses;
expanding the subtype preserves each of them definitionally, including all-algebra
kernel fixity, the actual intersection and restricted coaction, and unique exact descent.
The two real-data helper constructions and the proof docstring are preserved.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
