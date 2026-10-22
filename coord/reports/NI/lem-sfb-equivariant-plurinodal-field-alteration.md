## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantMarkedPlurinodalFieldAlteration` states
`AlgebraicGeometry.exists_equivariant_marked_plurinodal_field_alteration`, with `sorry`
as its only proof. It defines no new notion. The source read was ILO, Travaux de Gabber,
Expose X, Lemma 2.2 proof, printed pp. 149--150 (PDF pp. 155--156), specifically its
application of Vidal 2004b Proposition 4.4.3 before the subsequent modifications.
The fourteen-step proof of the current DAG node is reproduced in the theorem docstring.
There is no statement correction and no disputed clause.

The sandbox was empty on resumption. The earlier “stale assignment; NK's delivery was
already merged” message concerns a split, not a Lean statement: the current node has no
Lean binding. The stage-2 packet here supplies its missing statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`. The k-scheme is `(X : Scheme.{u})` with
  structure morphism `(p : X ⟶ Spec (.of k))`. `[IsIntegral X]`, `[IsProper p]`, and
  `[GeometricallyIntegral p]` express the integral, proper, geometrically integral
  assumptions. Finite type is already implied by properness: `IsProper` supplies
  locally finite type, and universal closedness supplies quasi-compactness. The
  first compile warned about a duplicate locally-finite-type instance parameter;
  that redundant binder was removed, without changing the hypotheses.
- `hnormal` says at every x that the stalk is a domain and integrally closed.
- `(H : Type u) [Group H] [Finite H]` is the finite group. `α : H →* Aut X`
  and `β : H →* (k ≃+* k)` give its scheme and field automorphisms, including their
  group laws. `hfaithful : Function.Injective α` is faithfulness on X.
  `hsemilinear` is compatibility with p. The inverse on β is required by the
  contravariance of Spec, following the convention of EquivariantSmoothGaloisModel.
- `Z : Closeds X`, `hZ`, and `hstable` express closedness, nowhere density, and
  invariance of the specified subset.
- The output `(F : Type u) (_ : Field F) (_ : Algebra k F)` and `Module.Finite k F`
  give the finite extension, with the actual algebraMap used in the diagram.
- `(J : Type u) (_ : Group J) (_ : Finite J)`, `ρ : J →* H` and
  `Function.Surjective ρ` are the finite covering group and surjection.
  `γ : J →* (F ≃+* F)` is its field action; the equation on all c : k says
  precisely that γ extends β through ρ.
- `K : IntermediateField k F` is characterized by `c ∈ K ↔ ∀ g : ρ.ker,
  γ g.val c = c`. Thus it is exactly F^kerρ, not an unspecified fixed subfield.
  `IsPurelyInseparable k K` is the radicial constant-field assertion. This does
  not require the full J-action to fix k pointwise.
- `d : ℕ` and `topologicalKrullDim X = (d : WithBot ℕ∞)` fix the length.
  `T : Fin (d+1) → Scheme`, `f i : T i.succ ⟶ T i.castSucc`, and
  `∀ i, IsIntegral (T i)` give all integral stages. The isomorphism `e₀` and
  `q 0 = e₀.hom` identify the bottom with Spec F. The maps q, together with
  `f i ≫ q i.castSucc = q i.succ`, are the actual structural maps of this tower.
- `a : T (Fin.last d) ⟶ X`, `IsProjectiveBundle a`, and `Surjective a` give
  the top alteration. The equation `a ≫ p = q (Fin.last d) ≫ Spec.map ...`
  makes it a morphism over k. Its finite-over-a-dense-open assertion appears
  together with the stronger required orbit condition at the end.
- For each i, `IsProjectiveBundle (f i)` and `Flat (f i)` give projectivity and
  flatness. `hfp : LocallyOfFinitePresentation (f i)` gives local finite
  presentation; projectivity also gives quasi-compactness and separatedness,
  so this is finite presentation. `HasNodalGeometricFibres` states nonempty
  connected dimension-one geometric fibres and the prescribed completed
  ordinary-double-point local rings at all nonsmooth geometric points.
  `GeometricallyReduced (f i)` supplies reducedness after every field base change.
- The generic-fibre clause explicitly supplies a generic point y, smoothness of
  `(f i).fiberToSpecResidueField y`, and geometric integrality of that morphism.
- `m i : ℕ` and `s i : Fin (m i) → (T i.castSucc ⟶ T i.succ)` give finitely
  many sections. Their composites with f i are identities, `Pairwise Disjoint`
  gives disjoint images, and each image is contained in the actual relative
  `Scheme.Hom.smoothLocus`, using the same hfp instance.
- `B : ∀ i, Closeds (T i)` are the closed boundary sets. `B 0 = ∅` and the
  displayed recursive set equality say exactly that B_(i+1) is the inverse
  image of B_i union the images of all sections. The restricted morphism
  over the complement of B_i is required to be `Smooth`. The inverse image
  of Z under a is explicitly contained in the top boundary.
- `τ : ∀ i, J →* Aut (T i)` gives all tower actions. Its three compatibility
  clauses express semilinearity over F, equivariance of every f i, and
  equivariance of a through ρ. The image equality for the union of the
  section images gives stability of that union, allowing permutations.
  Together with the recursion, these equations imply stability of all B_i.
- Quasi-splitness is expressed for every residue-field fibre `(f i).fiber y`.
  A nonsmooth x has its structural residue-field map surjective, so its
  residue field is exactly κ(y). Its fibre under `fromReducedNormalization`
  has `Nat.card = 2`, and the structural residue-field maps at both those
  normalization points are surjective as well. These are precisely the two
  rational branches. No normalization of an integral total space is substituted
  for normalization of the possibly reducible fibre.
- Finally `U : X.Opens` is dense and `a ∣_ U` is finite and surjective. Every
  geometric point x of U has a lift, and every two lifts are related by an
  element of `ρ.ker` through the given τ action. Thus each geometric fibre
  is a single N-orbit. The same U witnesses generic finiteness as defined
  in the node. This formulation uses Ω-valued points, equivalently the points
  of the finite Ω-fibre over an algebraically closed field.

Dependency declarations and source files inspected:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`,
  together with the recorded geometric reducedness and irreducibility interfaces.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  the recorded finite-type notion is that class and `QuasiCompact`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`; Mathlib `Field`.
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree` and its docstring's
  identification of finite extensions with `Module.Finite` and pure inseparability
  with Mathlib `IsPurelyInseparable`. The theorem uses those existing predicates.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`;
  its actual finite-type quasi-coherent projective-bundle construction is retained.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, as
  used in the geometric-fibre predicate. `Mathlib.AlgebraicGeometry.Fiber`:
  `Scheme.Hom.fiber`, `fiberToSpecResidueField` use that actual pullback.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  used by the recorded projective-bundle construction; the section closedness
  follows from separatedness and is not replaced by an arbitrary immersion.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- Added the already-landed `def-trf-nodal-geometric-fibres` to stmt_deps and used
  its `Sheaf.AlgebraicGeometry.NodalGeometricFibres.HasNodalGeometricFibres`
  (namespace AlgebraicGeometry). The full declaration and docstring were read.
- Added the already-landed `def-weil-pbc-reduced-normalization` to stmt_deps and
  used `AlgebraicGeometry.Scheme.reducedNormalization` and
  `fromReducedNormalization` from `Sheaf.AlgebraicGeometry.ReducedNormalization`.
  Its full construction is the disjoint union of the integral-component normalizations.

No new definition nodes or dependency replacement modules are needed. Imports of all
recorded proof dependencies with modules are included as non-public imports. Proof
nodes without a recorded declaration remain the existing named stages of the proof;
this delivery does not introduce sorries for those other nodes.

Edge cases checked:

- d = 0: Fin d is empty, so there are no curve maps or markings; Fin (d+1)
  has its one bottom/top stage isomorphic to Spec F. The boundary is empty.
  The dense-open condition still includes the identity case.
- Empty marking families are allowed by m i = 0, with empty unions and vacuous
  pairwise disjointness. Z may be empty.
- X cannot be empty because it is integral. There is no illicit positive-dimension
  or positive-characteristic assumption. Purely inseparable is Mathlib's predicate
  in characteristic zero as well as positive characteristic.
- A trivial group and a nonfaithful action on the constant field are allowed.
  Only the given action on X is required faithful; the output action need not be.
- Smooth fibres have no nonsmooth points, so the quasi-split branch clause is
  vacuous there. A nodal reducible fibre uses componentwise normalization.
- Group permutations of sections and branches are allowed; no stabilizer-leg
  triviality or pointwise stability of individual markings was added.
- The first f_i is smooth because the initial boundary is empty, exactly as in
  the node, while no smoothness of the higher total spaces is asserted.

Searches for an existing statement:

- msearch.py leanfinder: “equivariant marked plurinodal alteration over a field
  finite group nodal curves”: eight hits, only unrelated elliptic/Weierstrass
  and affine-space statements, no alteration theorem.
- msearch.py loogle: “AlgebraicGeometry.IsProjectiveNodalTower,
  AlgebraicGeometry.IsGeometricOrdinaryDoublePoint”: no hit (unknown identifier
  in Mathlib); these are project declarations, not a Mathlib alteration theorem.
- msearch.py grep: “Plurinodal|quasiSplit|QuasiSplit” in Mathlib/AlgebraicGeometry:
  zero hits.
- rg of lean/WeilConjectures for plurinodal and the exact node id: no match;
  rg of lean/Sheaf finds PlurinodalAlteration (non-equivariant trait/field
  statements), ProjectiveNodalTower (a different unmarked tower predicate),
  and EquivariantSmoothGaloisModel (a downstream theorem using this node).
  Their statements were inspected; none states the requested marked equivariant
  tower. The exact proposed theorem name has no upstream/project match.
- Live-source lookup via scompile.py --source for the anticipated older name
  Sheaf.AlgebraicGeometry.EquivariantPlurinodalFieldAlteration: unavailable.

Validation: scompile.py compiled the first version in sandbox and library modes;
its only warning was the redundant locally-finite-type instance binder, now removed.
The final version compiles cleanly. deliver2.py --no-push reported OK: the packet
passes the server preflight and per-file compilation (dry-run commit b0c764e7148).

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
