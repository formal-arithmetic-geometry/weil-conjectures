## Worker report

The module `lean/Sheaf/AlgebraicGeometry/NodalSpecialCliffordSubcurve.lean` states
`AlgebraicGeometry.exists_nodal_special_clifford_subcurve`, with exactly one postponed
proof (`sorry`). It introduces no definition, axiom or auxiliary theorem. The node's
accepted stage-1 statement and proof plan are unchanged. The old BLOCKED ending was
about a stage-1 unchanged-split rejection: the current item has no Lean attachment and
is explicitly a stage-2 queue item. The stage handoff in brief-stage2 §0 applies.
No released repair note exists for this item.

Hypothesis and conclusion correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- A projective k-scheme: `(D : Scheme.{u}) (f : D ⟶ Spec (.of k))
  [IsHProjective f]`, using the dependency's finite-projective-space convention.
  The explicit structure morphism is needed by the recorded very-ampleness API and
  by the induced scalar action on cohomology; it is not additional geometric data.
- Nonempty and connected: `[ConnectedSpace D]`; Mathlib's class includes nonemptiness.
- Reduced: `[IsReduced D]`.
- Pure dimension one: `hpure : D.IsPureDimension 1`, the recorded predicate testing
  every irreducible component with its subspace topology.
- Every singular point is nodal: `hnodal` quantifies over points outside
  `f.smoothLocus` and requires a ring isomorphism between the maximal-ideal adic
  completion of the stalk and `MvPowerSeries (Fin 2) k` modulo the ideal generated
  by `X 0 * X 1`. Over the algebraically closed field and for a projective reduced
  pure curve, the nonsmooth points are exactly its singular closed points.
  There is no restriction on characteristic, no assumed choice of branches and no
  additional residue-field or coefficient-field datum.
- Invertible module: `(L : D.Modules) [L.IsInvertible]` uses the canonical scheme
  module class, not the different generic sheaf-of-modules invertibility predicate.
- Very ample: `hvery : IsVeryAmple f L`, whose existing definition is precisely a
  closed immersion into projective space over the base with its hyperplane twist
  isomorphic to L. It quantifies over finite coordinate types, equivalently over
  dimensions n. No complete-linear-system or linear-normality assumption is added.
- H¹ is nonzero: `hspecial : Nontrivial
  ((RingedSpace.moduleCohomology D.toRingedSpace 1).obj L)`, the right-derived
  global-sections cohomology of Zariski module sheaves from the dependency.
- The support subcurve: existential `(Y : Scheme.{u}) (i : Y ⟶ D)` with
  `IsClosedImmersion i ∧ IsReduced Y ∧ ConnectedSpace Y`. A reduced closed
  immersion has the reduced induced structure on its image; ConnectedSpace
  guarantees Y is nonempty.
- Union of components: `∃ S : Set (Set D), S ⊆ irreducibleComponents D ∧
  Set.range i = ⋃₀ S`. No proper-subset condition excludes Y = D. Nonemptiness
  of Y forces S to be nonempty. Finite type makes the set of components finite,
  so this also describes the usual finite component unions.
- Degree measured on normalized components: the finite family `Z : Fin m → Scheme`
  has `hZ : ∀ a, IsIntegral (Z a)` and closed immersions `j a : Z a ⟶ Y`.
  Injectivity of `a ↦ Set.range (j a)` and the following component-image iff say
  that this family enumerates every reduced component exactly once. There is no
  multiple counting and no missing component. Reduced integral closed immersions
  with those images are the canonical reduced components up to unique isomorphism.
  The integer e is explicitly the sum of `Scheme.Modules.degree` of the pullback
  of L along `Z[a].fromNormalization ≫ j[a] ≫ i`, using the structure map obtained
  by further composing with f. This uses actual canonical normalizations and
  their canonical maps, with explicit `hZ a` instances. Neither a chosen degree
  function nor an arbitrary normalization or scalar action occurs.
- The two inequalities are `2 ≤ e` and `2 * (Module.finrank k (...) : ℤ) ≤ e + 2`.
  The latter is exactly h⁰ ≤ e/2 + 1, rewritten by multiplication by positive 2
  over the integers; there is no natural-number subtraction or division.
  The h⁰ object is the recorded `RingedSpace.moduleCohomology` in degree zero on
  `(Scheme.Modules.tensorPullback i).obj L`, restricted to k along
  `((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop).hom`. This is the canonical
  k-action through global functions, not an arbitrary Module instance.
- No GIT, Hilbert-polynomial, rational-tail, smoothness, integrality, genus or
  stability hypothesis is assumed on D. In particular D may be reducible.

The finite component enumeration only exposes the indexing of the sum already in
the node's degree convention. It adds no geometric requirement: Y is a closed
subscheme of a projective scheme over a field, hence Noetherian with finitely many
components. Each reduced component is integral. Distinct component images can be
indexed by `Fin m`, and all isomorphic presentations give the same degree sum.

Dependency declarations read and used:

- Mathlib: `Field` (`Mathlib.Algebra.Field.Defs`), `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (`Mathlib.AlgebraicGeometry.Scheme`), `IsClosedImmersion`
  (`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`), `IsReduced`
  (`Mathlib.AlgebraicGeometry.Properties`), `irreducibleComponents`
  (`Mathlib.Topology.Irreducible`), `ConnectedSpace`
  (`Mathlib.Topology.Connected.Basic`), `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`), `AdicCompletion`
  (`Mathlib.RingTheory.AdicCompletion.Basic`, ring structure from `.Algebra`), and
  `MvPowerSeries` (`Mathlib.RingTheory.MvPowerSeries.Basic`). The algebraic-closure
  node's mathlib_match expressly names `IsAlgClosed` for its algebraic-closedness clause.
- `AlgebraicGeometry.ProjectiveSpace.twist` and `twistRestrict`,
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, used through the existing
  `IsVeryAmple` definition in
  `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`.
- `AlgebraicGeometry.IsHProjective`,
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `AlgebraicGeometry.RingedSpace.moduleCohomology`,
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`.
- `AlgebraicGeometry.Scheme.Modules.degree`,
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`.
- `AlgebraicGeometry.Scheme.normalization` and `fromNormalization`,
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`.
- `AlgebraicGeometry.Scheme.IsPureDimension`,
  `Sheaf.AlgebraicGeometry.PureDimension`.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`,
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, publicly supplied by the
  recorded dependency module `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`.
- The existing DAG notions `def-pc-module-pullback` and `def-sc-ample` are added to
  stmt_deps to record the restriction and existing very-ampleness predicate used
  by this signature. No existing definition is copied or replaced.

Proof dependencies were read. `lem-sfb-nodal-line-serre-riemann-roch`,
`lem-sfb-nodal-subcurve-dualizing-annihilator` and `lem-sfb-hopf-bilinear-image-dimension`
have no Lean record yet. Their eventual modules therefore cannot yet be imported;
there is no need to restate these proof-only prerequisites to type this theorem.
The existing proof-dependency interfaces are `IsHProjective.isProper` in the
publicly imported projective module (the audit for lem-pc-projective-proper records
this general declaration as well as the projective-space instance),
`LocallyOfFiniteType.isLocallyNoetherian` and
`finite_irreducibleComponents_of_isNoetherian` in
`Mathlib.AlgebraicGeometry.Noetherian`,
`QuasiCompact.compactSpace_of_compactSpace` in
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, and `IsClosedImmersion.comp` in
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`. The last three modules are
explicit non-public proof imports. The theorem docstring gives all four steps of
the accepted proof, including the minimum-support argument and dimension elimination.

Edge cases checked before writing: the empty D is excluded exactly by ConnectedSpace;
a zero H¹ is excluded by Nontrivial; a zero or one-dimensional H⁰ cannot generate a
very ample line on a nonempty pure curve. Y = D is allowed, including the irreducible
case. Empty component enumeration cannot satisfy coverage for a nonempty connected
curve. A reducible Y is covered by the exact-once enumeration. Self-nodes and nodes
joining different components are allowed by the completion formula. Smooth curves
satisfy the nodal hypothesis vacuously; projective lines have no special very ample
lines, whereas a canonical embedding of a smooth nonhyperelliptic curve gives the
expected equality case with Y = D. Characteristic two is included. All schemes and
the field live in the same arbitrary universe u, with no smallness or countability
restriction. All universes and variables are explicitly bound; autoImplicit and
relaxedAutoImplicit are false.

Searches made:

- msearch.py leanfinder: "A special very ample line bundle on a nodal curve has a
  connected subcurve with Clifford inequality" returned eight unrelated elliptic
  Weierstrass-curve declarations; no match.
- msearch.py loogle: `"Clifford", "degree"` returned zero hits.
- msearch.py grep: `Clifford|nodal` in AlgebraicGeometry returned zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for Clifford, nodal/special, normalized
  component degrees, normalization, veryAmple/VeryAmple, and the exact node id.
  The broad Clifford results concern Clifford algebras or representation theory.
  `Curve/RiemannRoch.lean` treats the smooth-curve framework, not this reducible
  nodal support lemma; no existing exact theorem was found. The exact item id has
  no upstream occurrence. `dag/lean_names_upstream.json` has no matching name.
- Related declarations read: nodal geometric fibres/source locality, nodal point
  etale locality, normalizedFibreComponentDegree and markedNodalComponentDegree,
  and Mathlib's component subscheme. These carry extra family/fibre data or are
  only component constructions, so none states this support theorem. Their
  normalized-degree terms confirmed the existing canonical normalization API;
  no helper definition was needed.
- Source: read local Stacks curves.tex Tags 0BS2 (duality), 0BS6 (Riemann--Roch),
  0E33 (closed-immersion dualizing sheaf), and the minimal-support argument near
  lines 5470 onward. Also read the current latest blueprint's direct-image statement
  and proof. Morrison/Gieseker PDFs remain marked WANTED in the node's source;
  this delivery follows the accepted reconstructed auxiliary proof and the local
  Stacks texts, without changing their route or claiming a direct PDF reading.

No statement dispute, node correction, new node or dependency-module repair.
The first scompile.py run passed in 2.5 s (sandbox) and 2.1 s (library). After
finalizing the explicit proof imports and recorded pullback module, deliver2.py
--no-push passed server compilation and preflight: OK (dry run), commit
87a60e84fdc. No compiler warnings or errors were reported.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
