## Worker report

The module `Sheaf.AlgebraicGeometry.TraitGroupFiniteSmoothCover` states
`AlgebraicGeometry.exists_trait_group_finite_smooth_cover`, with exactly one `sorry`
and no definitions or additional theorems. The node is unchanged except for `lean`.
The declaration's docstring gives all seven steps of the accepted DAG proof and
names the supporting nodes. No statement correction or disputed statement is needed.

Source checked: Prasad--Yu, *On quasi-reductive group schemes*,
https://math.stanford.edu/~conrad/papers/qrg.pdf, Proposition 3.1 first paragraph
(printed p.5), Conrad's Appendix Theorem A.2, Remark A.3 and Corollary A.4 and its
proof (printed pp.28--29), Remark A.1, and the residue-field extension after A.9
(printed pp.31--32). In particular A.4 applies to separated flat finite-type groups,
without requiring affine or smooth generic fibre. The finite morphism is the
normalization of the reduced base change followed by the reduction inclusion.
The requested local PDF is still marked WANTED in the node; the online source was read.

The statement is rendered clause by clause as follows.

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| R is a discrete valuation ring, including the non-field condition | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`; the last class extends local and principal-ideal-ring structures and requires a nonzero maximal ideal |
| S is Spec R | `Spec (.of R)` |
| G is an S-group scheme with multiplication, identity, inverse, and group diagrams | `G : Grp (Over (Spec (.of R)))`; `G.X` is the S-scheme, `G.grp` its `GrpObj` structure |
| G is flat | `[Flat G.X.hom]` |
| G is separated | `[IsSeparated G.X.hom]` |
| G is of finite type | `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]` |
| There exists a DVR R' | Existential `R' : Type u`, `CommRing R'`, `IsDomain R'`, `IsDiscreteValuationRing R'` |
| The extension is a ring homomorphism R -> R' | Existential `Algebra R R'`, with the map `algebraMap R R'`; any ring homomorphism gives precisely such an algebra structure |
| The map is injective | `Function.Injective (algebraMap R R')` |
| The map is local, in the node's maximal-ideal sense | `IsLocalHom (algebraMap R R')`; `IsLocalRing.local_hom_TFAE` identifies this with the inclusion of maximal-ideal images |
| The map is faithfully flat in the recorded module sense | `Module.FaithfullyFlat R R'` using the existential algebra structure, as required by STATE's faithfully-flat convention |
| R' can be chosen strictly henselian | `IsStrictlyHenselianLocalRing R'` |
| Its residue field is algebraically closed | `IsAlgClosed (IsLocalRing.ResidueField R')` |
| The induced spectrum morphism is flat and surjective | `Flat (Spec.map (CommRingCat.ofHom (algebraMap R R')))` and the corresponding `Surjective` conjunct |
| Its singleton is an fpqc cover | `Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∈ Scheme.fpqcPrecoverage (Spec (.of R))` |
| There exists an R'-group scheme N | `N : Grp (Over (Spec (.of R')))` |
| N is separated, finite type, and smooth over R' | `IsSeparated N.X.hom`, `LocallyOfFiniteType N.X.hom`, `QuasiCompact N.X.hom`, `Smooth N.X.hom` |
| The target is G base changed along this very ring map | `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).mapGrp.obj G`; `Over.pullback.obj` has underlying scheme `pullback G.X.hom (Spec.map ...)` and structure map `pullback.snd` |
| q is an R'-group homomorphism | The existential `q : N ⟶ (...).mapGrp.obj G` is a morphism in `Grp (Over (Spec R'))`; its underlying scheme morphism is `q.hom.hom.left` |
| q is finite and surjective | `IsFinite q.hom.hom.left ∧ Surjective q.hom.hom.left` |
| No affine, generic-smoothness, connectedness, or excellence hypotheses | None appears in the binders or in the group-scheme representation; `Over` includes arbitrary schemes |

`Functor.mapGrp` transports the actual group operations using the monoidal pullback
functor. It is not an arbitrary chosen group structure on the fibre product.
Morphisms in `Grp` preserve multiplication and identity; `Grp.inv_hom` then gives
inverse compatibility, so the use of this bundled morphism loses no group clause.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, lines 56--61.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 469--481 (available through the public imports).
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, lines 37--46; stalkwise characterization
  recorded on the node identifies it with the requested notion.
- `def-weil-proper-morphism`: its separated component `AlgebraicGeometry.IsSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, lines 42--46, imported through
  the recorded `Mathlib.AlgebraicGeometry.Morphisms.Proper`. No `IsProper` is assumed.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, lines 39--48, and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  lines 38--46. Both are included, as the dependency's record specifies.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, lines 57--65. The source/node's
  local-finite-presentation plus formal-smoothness convention is identified with
  this class by Stacks 02H6, as already recorded by this dependency.
- `def-pc-base-change`: the convention documented in
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, module docstring:
  `Over.pullback`, underlying `Limits.pullback`, projections `fst`/`snd`.
  `Scheme.Modules.moduleBaseChange` is its separate module-sheaf clause, not used
  in this scheme statement. The recorded module is publicly imported.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, lines 34--40.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, lines 57--60.
- `def-weil-pbc-henselian-terminology`: `IsStrictlyHenselianLocalRing`,
  `WeilConjectures.Mathlib.RingTheory.Henselian`, lines 121--124.
- `def-weil-algebraic-closure`: the algebraically-closed component `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, lines 58--63, publicly imported via
  the matched `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` module.
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat`,
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, lines 59--65. This is the
  recorded module formulation of faithful flatness for the extension algebra.
- `def-weil-pbc-fpqc-covering`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`, lines 59--65. The singleton form is
  directly documented by `Scheme.Hom.singleton_mem_fpqcPrecoverage`, lines 107--111.

Additional existing component APIs: `CategoryTheory.GrpObj`, `Grp`, `Grp.inv_hom`
and `Functor.mapGrp` in `Mathlib.CategoryTheory.Monoidal.Grp`;
`CategoryTheory.Over.pullback` in `Mathlib.CategoryTheory.Comma.Over.Pullback`;
its monoidal structure in `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`;
`IsLocalRing.local_hom_TFAE` in `Mathlib.RingTheory.LocalRing.RingHom.Basic`.
The group diagrams are explicitly introduced by the item's own statement; the
existing general `GrpObj`/`Grp` APIs render them without a new notion or node.
The familiar field-only `def-sc-group-scheme` record was also read as an API example;
this declaration does not impose a field base or introduce another group-scheme definition.

The available proof-dependency modules are imported privately, including
`Sheaf.RingTheory.PrincipalRegularLocalCompletionDVR`,
`WeilConjectures.RingTheory.FlatLocalExtensionGivenResidueField`,
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`.
The Mathlib proof leaves use the corresponding finite, finite-type, separated,
flat, geometrically-reduced-group smoothness, finite-presentation, henselian,
faithful-flat, and torsion-free-flat modules. Two proof dependencies have no
recorded declaration yet: `lem-sfb-complete-trait-normalized-reduced-fibres` and
`lem-sfb-trait-normalization-group-structure`. They are named in the complete proof
docstring; neither is needed for elaborating this stage-2 statement, so no module
is invented or imported for them. Their future proof imports remain the maintainer's task.

Edge cases checked before writing:

- A field or the zero ring is excluded exactly by the genuine DVR conditions.
- The identity group is permitted. The empty scheme cannot carry a unit section
  over the nonempty spectrum of a DVR, so excluding it is inherent in being a group.
- Nonreduced groups such as alpha_p or mu_p in characteristic p are permitted.
  A finite surjective morphism here means surjective on scheme points and need
  not be faithfully flat or an epimorphism on sections: a reduced point can cover
  a finite connected infinitesimal group topologically. Thus smoothness of N
  does not inadvertently require G to be smooth.
- Disconnected constant groups and non-affine groups (for example abelian schemes)
  remain allowed. No `IsAffine` or connectedness class occurs.
- Imperfect residue fields and positive or mixed characteristic remain allowed;
  algebraic closedness is required only for the existential extension's residue field.
- No completeness or excellence hypothesis occurs on R. Completing an auxiliary
  flat local extension is part of the postponed proof, not a hidden input hypothesis.
- The single explicit universe `u` permits every DVR and its finite-type schemes.
  Residue algebraic closure, the auxiliary local extension, adic completion and the
  finite fraction-field extension can all be constructed in the same universe.
  There is no independent smaller universe for a test-object quantification.

Searches performed (logged by msearch in the sandbox's `searches.jsonl`):

1. LeanFinder: `A separated flat finite type group scheme over a discrete valuation ring admits a finite surjective smooth group cover after faithfully flat local extension`.
   Eight hits: smooth-algebra noetherian descent, smoothness/flatness facts and
   flat-descent permanence; none states this group-scheme cover theorem.
2. Loogle: `"IsDiscreteValuationRing", "Smooth"`: zero hits.
3. Mathlib grep via msearch: `group.*smooth.*cover|smooth.*group.*finite|GroupScheme`
   under `AlgebraicGeometry`: zero hits.
4. LeanSearch: `A flat group scheme over a discrete valuation ring has a finite surjective smooth cover after extending the base discrete valuation ring`.
   Eight hits, including `Algebra.Smooth.flat`,
   `AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`,
   and affine/stalk flatness; none gives the cover theorem.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `finite.*smooth.*cover|smooth.*finite.*cover|potential.*smooth|trait-group-finite`
   found curve-resolution and smooth-coordinate covers, and proof references in
   `QuasiReductiveSpecialConnectedness`, but no declaration of the assigned statement.
   `rg` for `exists.*[Ff]inite.*[Ss]mooth|exists.*[Ss]mooth.*[Cc]over|exists.*[Ss]mooth.*[Ff]inite`
   likewise found unrelated curve and local-chart results.
6. Exact item-id search in `lean/WeilConjectures` and exact proposed declaration-name
   searches in both source roots returned no existing declaration. Group-object
   searches found and reused the `Grp`, `GrpObj`, and `mapGrp` APIs above.

Validation: the prescribed `scompile.py NJ lem-sfb-trait-group-finite-smooth-cover`
compiled this module on the server, both as sandbox and library module, in 2.2 s
and 2.3 s respectively, with no errors or warnings. `autoImplicit` is false and
universe `u` and all variables are explicitly bound. The maximum Lean line width
is 94 characters. Delivery dry-run and final push results are recorded below.

## Second reading by NJ

A fresh clause-by-clause self-reading was made with the original node, dependency
records, source declarations and final module open. The dispatcher explicitly
forbids starting other agents and directs this worker to deliver itself; this is
not represented as an independent agent review. The maintainer supplies the
independent review of the delivery.

The four input hypotheses are precisely DVR, flatness, separatedness and finite
type, besides the group structure. In particular finite type has both local finite
type and quasi-compactness. Every output clause uses one shared existential R',
one shared algebra structure and its `algebraMap`. Strict henselianity and
algebraically closed residue field are simultaneous, and flatness/surjectivity and
fpqc membership concern the spectrum map of that same algebraMap. The output N
has both finite-type components, separatedness and smoothness. The morphism q
lands in the canonical `mapGrp` base change of the given G, and both finiteness
and surjectivity concern its underlying scheme morphism. Bundling q in `Grp`
includes multiplication, unit and inverse compatibility. No clause is replaced
by an arbitrary map, an affine specialization, or an unconstrained group law.
No mismatch was found and no node correction was necessary. The theorem remains
`sorry` as required for stage 2; its full proof plan is in its docstring.

Delivery validation: `deliver2.py NJ lem-sfb-trait-group-finite-smooth-cover --no-push`
printed `OK (dry run): commit 2a0f84c0ffa passes the preflight and compiles; nothing pushed`.

Final delivery infrastructure failure: the prescribed push wrapper was run twice.
Both runs passed compilation and preflight but the remote rejected the push.
The first attempt reported `remote unpack failed: unable to create temporary object directory`.
The retry reported `remote: error: unable to create temporary file: No space left on device`
and `remote: fatal: failed to write object`, followed by `unpacker error`.
The retry's locally built commit was `569503ab8497711a4966eb0588e33fccee0936ec`.
No successful DELIVERED result was printed. All deliverable files remain in this sandbox;
no launcher files or shared repository files were edited directly.
