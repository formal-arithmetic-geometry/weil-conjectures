## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RelativeSemisimpleAffineness` states
`AlgebraicGeometry.isAffineHom_of_semisimple_geometricFibres`, with its sole proof `sorry`.
No definitions or other theorems are introduced. The mathematical statement is unchanged.
The item gains two already landed statement dependencies, `def-sc-group-scheme` and
`def-sfb-semisimple-group-scheme`, to record the group and semisimplicity interfaces reused.
No new node or dependency repair is needed.

Hypotheses and conclusion, clause by clause:

- The commutative base ring is `B : Type u` with `[CommRing B]`.
- Domain, Noetherianity, and integral closedness are respectively `[IsDomain B]`,
  `[IsNoetherianRing B]`, and `[IsIntegrallyClosed B]`. In particular B is nonzero.
- Dimension exactly one is `hdim : ringKrullDim B = 1`. This is not a dimension-at-most-one
  condition and does not silently include fields.
- The base scheme S is `Spec (.of B)` throughout. The group is
  `H : Grp (Over (Spec (.of B)))`; its underlying scheme and structure morphism are
  `H.X.left` and `H.X.hom`. `Grp` packages an actual `GrpObj`, whose multiplication,
  identity, inverse and group diagrams are the Mathlib group-object structure.
- Smoothness is `[Smooth H.X.hom]`.
- Separatedness is `[IsSeparated H.X.hom]`, whose defining field says the diagonal is a
  closed immersion.
- Finite presentation is `[LocallyOfFinitePresentation H.X.hom]`,
  `[QuasiCompact H.X.hom]`, and `[QuasiSeparated H.X.hom]`, exactly the comparison clause
  in `def-sbc-locally-finite-presentation`. The quasi-separatedness component also follows
  from separatedness; retaining it spells out finite presentation without restricting H.
- Every algebraically closed field and ring homomorphism is rendered by
  `∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : B →+* k)`.
  The universe u is arbitrary and shared with B and the schemes. These are all small
  geometric points of Spec B, including algebraic closures of its generic residue field;
  the test-field universe is not below the base-ring universe. Small representatives
  suffice to test geometric fibres, and no characteristic or injectivity condition on φ
  is imposed.
- The geometric fibre is `((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj H).X`.
  Its scheme is the actual pullback `H.X.left ×_(Spec B) Spec k`, with second projection
  to Spec k. `mapGrp` gives the base-changed operations of H, not a chosen group law.
- Connected, affine, and semisimple fibres are exactly `IsSemisimpleGroupScheme` of that
  group. This landed definition includes `ConnectedSpace`, `IsAffine`, and triviality of
  every smooth connected solvable normal closed subgroup. `IsSolvableGroupScheme` means
  termination of the scheme-theoretic derived series, with terminality over Spec k as
  the trivial group. Its smoothness and finite-type components follow already from
  the globally assumed smooth finite-presentation morphism, so add no hypotheses.
- The conclusion is precisely `IsAffineHom H.X.hom`. Its definition requires that the
  inverse image of each affine open of Spec B is an affine open of H.
- No splitness, maximal torus, root datum, generic-fibre identification, dimension/rank
  positivity, or assumption that H is affine occurs among the binders.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (`def-sbc-smooth-morphisms`), including its affine-local ring-map definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`
  (`def-sbc-locally-finite-presentation`), with quasi-compact and quasi-separated for
  global finite presentation.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`
  (`def-weil-affine-spectrum`).
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`
  (`pqf-def-affine-morphism`), and its composition instance
  (`lem-weil-pbc-affine-composition`).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`
  (`def-weil-connected-scheme`, recorded as mathlib_match, without needing a lean record).
  It explicitly includes nonemptiness.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and
  `CategoryTheory.Grp` (`def-sc-group-scheme`); also
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`: the product-preserving pullback
  functor used with `mapGrp`. Read its `grpObjMkPullbackSnd` description and implementation.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `AlgebraicGeometry.IsSemisimpleGroupScheme` and its definitions
  `groupSchemeCommutator`, `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`,
  `IsSolvableGroupScheme` (`def-sfb-semisimple-group-scheme`), read in full.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`.
- Proof-only import `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`:
  `AlgebraicGeometry.Smooth.flat_and_locallyOfFinitePresentation`
  (`lem-pc-smooth-flat`, closed upstream). The affine-composition proof dependency
  already lives in the publicly imported Affine module.
- The three remaining proof dependencies `lem-sfb-smooth-group-relative-adjoint`,
  `lem-sfb-semisimple-adjoint-kernel-finite`, and
  `lem-sfb-dedekind-finite-kernel-hom-affine` have no recorded Lean declaration yet.
  Their complete statements were read, and the four-step proof docstring follows the
  node's proof using those inputs; there is no module to import for them yet.

Source checked online: Brian Conrad, *Reductive Group Schemes*,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
proof of Proposition 6.3.16, printed p.229 (PDF page index 228).
The argument uses the adjoint action, finite geometric kernels, the affineness of
quasi-finite homomorphisms over a Dedekind base, and composition with GL's affine
structure map. This supports precisely the node's adjoint-kernel route without any
split torus or root-chart hypothesis. The proof docstring records all four steps and
preserves scheme-theoretic finiteness in positive characteristic.

Searches for an existing theorem:

- `msearch.py ... leanfinder "A smooth separated group scheme of finite presentation
  over a Dedekind domain with semisimple geometric fibres is affine"`: eight hits,
  including `IsAffine`, affine schemes, and general scheme morphism properties;
  none states the group-scheme theorem.
- `msearch.py ... loogle '"IsAffineHom", "GrpObj"'`: zero hits.
- `msearch.py ... grep 'semisimple|Semisimple' AlgebraicGeometry`: zero Mathlib hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for group schemes, semisimplicity,
  and affineness found the reusable `GroupScheme/Semisimple.lean`, but no theorem
  asserting this relative affineness statement. A focused upstream search for the
  item id found no match. A search of `dag/lean_names_upstream.json` for relative
  semisimple/affineness names also found no theorem.
- DAG search identified the already landed `def-sfb-semisimple-group-scheme` and
  `def-sc-group-scheme`; their existing declarations are used, with no duplicate notion.
  Search service records are retained in the sandbox `searches.jsonl`.

Edge cases checked before writing: the trivial group is allowed (terminal fibres,
empty derived series, zero tangent module); an empty scheme cannot carry these
geometric group fibres, and `ConnectedSpace` correctly excludes emptiness; fields
as bases are excluded only by the expressly required dimension-one hypothesis;
geometric generic and all closed fibres are included; arbitrary positive characteristic
is included, with no reducedness or etaleness imposed on adjoint kernels; nonsplit
families require no additional data. A torus or a nontrivial connected solvable group
is not incorrectly deemed semisimple by the reused predicate, since it itself is a
nontrivial smooth connected solvable normal closed subgroup.

Validation: `scompile.py Q100 lem-sfb-relative-semisimple-affineness` compiled the
module cleanly in sandbox mode and at its final library module name (10.5 s and
2.4 s respectively). All binders are explicit and `autoImplicit` is false. The only
postponed proof is the named item theorem. No statement dispute or correction.

## Second reading by Q100

In-thread self-review only: the dispatcher explicitly forbids starting other agents;
the delivery receives an independent review from the maintainer. Reread the node,
its five original dependency interfaces, the two added landed definitions, and the
finished module. The ring hypotheses and exact dimension equality match; H is a
fully specified group object over exactly Spec B; smooth, separated and all three
finite-presentation components match. Every algebraically closed field map is tested,
and `mapGrp` fixes the actual inherited fibre group structure. Unfolding the recorded
semisimple predicate gives connectedness, affineness, smoothness and finite type,
with exactly the solvable-normal-subgroup condition. Smoothness and finite type are
already inherited from H, so the packaged predicate does not strengthen the fibre
hypothesis. The conclusion is exactly the recorded affine-morphism definition.
No missing clause, new assumption, arbitrary map, hollow definition, or changed
statement was found. No Lean changes were needed after the clean compile.
