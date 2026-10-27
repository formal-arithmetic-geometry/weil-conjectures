## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSourceAdjunctionLine` states
`AlgebraicGeometry.exists_flatLCIEtaleAdjunctionSystem`, with exactly one postponed
proof. It constructs, in the conclusion, a coherent system of normalized adjunction
lines and étale source comparisons; no comparison map or additional geometric
hypothesis is supplied by the caller. All auxiliary definitions have real data.
The node statement, proof and proof dependencies are unchanged. Its statement
dependencies gain the already landed `def-a1-relative-differentials-pullback-map`,
as permitted by brief-stage2 §5 for existing landed notions. Its recorded canonical
map is used directly in the presentation comparison rather than reconstructed.

The final system has a `data` field of type `FlatLCIEtaleAdjunctionData p` and
a `coherent : data.IsCoherent` proof. The data fields are `adjunction`, `smooth`,
and `comparison`. The fourteen conjuncts of `IsCoherent`, in order, are:
normalization; flatness; local finite presentation; quasi-compactness;
quasi-separatedness; pure fibres; local presentations; smooth normalization;
determinant normalization; identity; composition; open restriction; preservation
of smoothness; differential normalization. The descriptive clause names below
refer to these conjuncts, not to additional assumptions or data supplied by the caller.

Hypothesis and clause correspondence:

- Schemes and sizes: `{X S : Scheme.{u}} (p : X ⟶ S)`, with explicit universe `u`.
- Noetherian base: `[IsNoetherian S]`, Mathlib's conjunction of locally Noetherian
  and compact, exactly `pqf-def-locnoeth` and `def-weil-pbc-quasi-compact-scheme`.
- Flatness: `[Flat p]`.
- Finite presentation: `[LocallyOfFinitePresentation p] [QuasiCompact p]
  `[QuasiSeparated p]`, in precisely the three-part sense of the node.
- Pure dimension one of every nonempty geometric fibre:
  `hpure : HasPureFlatLCIGeometricFibres p 1`. This is the dependency's componentwise
  `topologicalKrullDim` condition on the pullback to the algebraic closure of each
  residue field; empty fibres contribute no components.
- Local regular lci presentations: `hlci` quantifies over every point and an open
  neighbourhood admitting `FlatLCIPresentation p 1 U`. Its `rank_eq : n = c + 1`,
  closed immersion, open ambient affine-space map, and local regular sequence are
  exactly the node's `n-1` equations in `n` variables. No positivity or global
  embedding is added.
- Étale finitely presented `e : V ⟶ X`: the index `FlatLCIEtaleSource X` packages
  `scheme`, `map`, `Etale map`, `QuasiCompact map`, and `QuasiSeparated map`.
  Local finite presentation follows from étaleness. This is an index package for
  the existing notions, not a replacement definition of étaleness.
- Preservation for every `e`: the flatness, local-finite-presentation, quasi-compactness,
  quasi-separatedness, pure-fibre and local-presentation conjuncts of `IsCoherent` give exactly the claimed properties of `e ≫ p`.
- The adjunction line: `adjunction E : FlatLCIAdjunctionSystem (E.map ≫ p) 1`
  uses the recorded dependency's actual lines, invertibility, local exterior-model
  identifications, and base-change system. normalization is the first conjunct of `IsCoherent`, using its `IsNormalized`.
  The original family is the allowed index with map `𝟙 X`; its line is the line
  at `FlatLCIBaseChange.identity ((𝟙 X) ≫ p)`, transported along `Category.id_comp`
  when writing it with base map `p`.
- The line isomorphism: `comparison` gives tensor pullback of the line at `E` to
  the line at `D`, for every finitely presented étale map `a` over `X`.
  Taking `E` to be the identity source and `D` to be `e` gives the stated
  `e* K_{X/S} ≅ K_{V/S}`. The over-equality witnesses record equal structural
  maps; they impose no extra geometry.
- Canonicity on nonsmooth charts: the determinant-normalization conjunct requires
  `IsFlatLCIEtaleLineComparison`. For any map of polynomial presentations it
  uses the actual normalized ideal map and universal differential map. After
  the dependency's normalized determinant-pullback comparison `ρ`, the line
  comparison is its exact-cone determinant comparison. Ambient dimensions can
  differ; in particular a standard-étale monic-equation chart is included.
  This is not a choice of an unconstrained line isomorphism, nor a normalization
  only on a possibly nondense smooth locus.
- Composition (including identity): the composition conjunct is the explicit formula
  `Phi_(b a) = tensorPullbackSectionComp b a ; b*Phi_a ; Phi_b`.
  The identity conjunct uses `tensorPullbackSectionId`, not an unspecified identity comparison.
- Open restriction: the open-restriction conjunct gives the commutative square for arbitrary
  open immersions on the source and target and their restricted étale map.
  All four maps have their existing finite-presentation witnesses. This loses
  no open: all the source schemes are Noetherian under the theorem's hypotheses,
  so open immersions into them are quasi-compact, and are étale and
  quasi-separated. No affine-intersection hypothesis is used.
- Smooth identification: `data.smooth` and its normalization conjunct provide the dependency's
  conormal-normalized identifications on every smooth open. They retain exterior
  degree one, canonically the differential module, as in the dependency's API.
  The smooth-preservation conjunct proves that the corresponding source open is smooth.
  The differential conjunct then sends `1 ⊗ wedge(da)` to `wedge(d(h♯a))` under these
  identifications. Because all morphisms are module morphisms, this also says
  `r ⊗ da ↦ r d(h♯a)`. Differential sections locally generate the sheaf, so the
  formula specifies precisely the usual differential pullback isomorphism.
- No properness, nodal condition, marking, modification map, normality,
  separatedness, surjectivity, or nonempty smooth locus is required anywhere.

Auxiliary declarations, all belonging to this node's comparison interface and
listed in `lean.declarations`: `FlatLCIEtaleSource` (index package),
`FlatLCIEtalePresentationMap` (maps between the existing polynomial presentations
with ideal-section normalization), its `sourceComparison`, `conormalMap` and
`differentialsMap`, `flatLCIEtaleLocalComparison` (restriction and association of
the specified global map), `IsFlatLCIEtaleLineComparison` (its determinant
normalization), `FlatLCIEtaleAdjunctionData`, its `IsCoherent` predicate, and
`FlatLCIEtaleAdjunctionSystem` (the coherent conclusion).
These are helpers of the owning notion, not independent additional prerequisites.
None contains a postponed theorem or chooses data from a mere existence theorem.
The canonical differential pullback found in the existing project is reused and
its already landed definition node is added to `stmt_deps`; no new definition node
or dependency repair module is needed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`:
  `FlatLCIPresentation`, `FlatLCIPresentation.conormal`, `.differentials`, `.line`,
  `.IsConormalDifferential`; `FlatLCIBaseChange.identity`;
  `FlatLCIAdjunctionSystem`, `.IsNormalized`, `.IsSmoothComparison`;
  `flatLCITwoTermLine`, `IsFlatLCIDeterminantComparison`,
  `IsFlatLCIPullbackDeterminantComparison`, `HasPureFlatLCIGeometricFibres`,
  `flatLCIGeometricFibre`, and `exists_flatLCICanonicalAdjunction`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` (publicly imported by
  that module): `Scheme.Modules.tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionComp`, `tensorPullbackSectionId`, `tensorPullbackSection`;
  the actual `tensorPullback` is upstream `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `Scheme.Hom.relativeDifferentialsPullbackMap`. Read its complete unique-existence
  characterization and real definition (choice from that unique characterization).
  The new presentation map uses it verbatim, followed only by equality transport.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `.relativeDifferentialsHomEquiv`,
  `.relativeDifferentialsCongr`, and
  `.relativeDifferentialsDerivation`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, in the existing adjunction system's line field.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`:
  `Scheme.Modules.exteriorSheaf` and `exteriorSheafSection`.
- Mathlib: `AlgebraicGeometry.IsLocallyNoetherian` and `IsNoetherian`
  (`Mathlib.AlgebraicGeometry.Noetherian`), `CompactSpace`
  (`Mathlib.Topology.Defs.Filter`), `Flat` (`Morphisms.Flat`),
  `LocallyOfFinitePresentation` (`Morphisms.FinitePresentation`),
  `QuasiCompact` (`Morphisms.QuasiCompact`/`FiniteType`),
  `QuasiSeparated` (`Morphisms.QuasiSeparated`), `Etale` (`Morphisms.Etale`),
  `Smooth` (`Morphisms.Smooth`), `CategoryTheory.Limits.pullback`
  (`Limits.Shapes.Pullback.HasPullback`), `topologicalKrullDim`
  (`Mathlib.Topology.KrullDimension`), `RingTheory.Sequence.IsRegular`
  (`Mathlib.RingTheory.Regular.RegularSequence`), and `KaehlerDifferential`
  (`Mathlib.RingTheory.Kaehler.Basic`). These are reused through the public
  adjunction dependency, not redefined.

Available proof dependencies are imported, including the dimension lemmas,
étale cotangent vanishing, étale relative dimension zero, formal étaleness,
determinant, and regular sequence modules. The proof-only nodes
`lem-sfb-adjunction-cotangent-determinant-normalization`,
`lem-sfb-scheme-cotangent-transitivity`, and `lem-trf-lci-cotangent-presentation`
currently have no Lean record or Mathlib match, hence have no module to import.
They are not statement prerequisites: the comparison is specified directly by
its conormal determinant normalization. Their mathematical proof roles are
retained in the theorem docstring.

Edge cases checked: the empty scheme/source and empty geometric fibres; identity
and composite étale maps; nonsurjective and disconnected étale sources; empty
smooth locus (normalization still uses conormal charts); nonreduced bases;
nonseparated lci sources; arbitrary opens without a global polynomial presentation;
charts with different ambient dimensions; characteristic arbitrary. No independent
universe is imposed on the source or coefficients, and no auto-implicit is enabled.
The smooth identifications are supplied coherently in the conclusion, not
universally quantified over potentially arbitrary isomorphisms on an open with no
global presentation.

Searches (2026-10-22):

- `msearch.py ... leanfinder "Canonical adjunction line of a flat local complete
  intersection curve commutes with etale source morphisms"`: eight hits, on étale
  morphisms and standard smooth charts; none states the line comparison.
- `msearch.py ... loogle "AlgebraicGeometry.FlatLCIAdjunctionSystem,
  AlgebraicGeometry.Etale"`: no hits (the project-specific name is not indexed).
- `msearch.py ... grep "adjunction.*[Ee]tale|[Ee]tale.*[Aa]djunction|FlatLCI"
  AlgebraicGeometry`: no Mathlib hits.
- `msearch.py ... leansearch "Canonical adjunction line bundle etale source
  pullback local complete intersection"`: eight hits on ordinary pullback
  adjunctions and the étale category; none gives this theorem.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `FlatLCIAdjunction|EtaleSourceAdjunction|etale-source-adjunction-line` found the
  recorded adjunction module and its two consumers (formal-plane lattices and
  nodal normalization), but no source-locality statement. The exact node-id
  search in upstream has no match. Broader adjunction/étale searches found
  unrelated étale sheaf adjunctions, not coherent-module adjunction lines.
- Read the local Stacks sources at `lemma-lci-shriek`, `lemma-shriek-etale`, and
  `lemma-fundamental-class-lci` in `literature/stacks-project/duality.tex`.
  The node already distinguishes the intrinsic cotangent/determinant construction
  from the compactifiable-shriek setting; no separatedness assumption is imported.

Validation: the full module passed `scompile.py` in sandbox mode (7.2 seconds)
and library-module mode (6.9 seconds), with no errors or unexpected warnings.
An earlier monolithic data-and-laws structure timed out; moving its identical
laws into `FlatLCIEtaleAdjunctionData.IsCoherent` resolved the elaboration cost,
without splitting the delivered module or raising the 60-second limit.
The final `deliver2.py --no-push` printed OK: dry-run commit `349f06326d2`
passed the server preflight and both compilation modes. The final module reuses
the already landed canonical differential pullback map directly.

## Second reading by N0

A separate rereading of the node and the resulting module was done in this worker
session; no independent reviewer or sub-agent is claimed. The maintainer supplies
the independent delivery review required by the dispatch brief.

Checked every hypothesis and conclusion against the correspondence above. The
rereading retained the three separate finite-presentation conditions, componentwise
geometric-fibre purity with the empty case, the actual dependency's polynomial
presentations, the determinant normalization beyond smooth points, and explicit
identity, composition, open-square, and differential formulas. A first draft
universally quantified over all `IsSmoothComparison` witnesses on an arbitrary
open; this was replaced by coherently supplied normalized smooth comparisons in
the system. This avoids treating a chart-only predicate as globally unique when
an entire open has no single polynomial presentation. The final local differential
compatibilities include further open restrictions, so they fix these smooth
comparisons from their presentation-chart normalizations. No mathematical change
to the node was required.


## Returned-delivery repair: signed cone normalization (2026-10-22)

The retained packet first passed `deliver2.py --no-push` at dry-run commit
`b501e583609`. The current base now contains the Q33 repair requested in the
return: `lem-trf-flat-lci-canonical-adjunction.lean.by` is `Q33`, dated 2026-10-22,
and its `lean.note` identifies the accepted Q131 repair
`b944131f76f4f5dc01fa55f7e9fe154ab7662b2f`. I read that landed record and read the
current server module with `scompile.py --source
Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`. Its
`IsFlatLCIDeterminantComparison` now requires
`M.det • e(orientation) = (-1)^(a*(b+1)) • targetOrientation` for exactly the
ordered cone `(f,-dA),(dB,g)` used by this item. The formerly contradictory
unsigned predicate is no longer imported. This delivery retains the item's Lean
source and does not supply or overwrite the dependency node or module. Its Lean
record now explicitly records reliance on the landed repair.

For the returned affine-line test over Q, use presentations C_k with equations
`t1,...,tk`, ambient differential basis `dx,dt1,...,dtk`, and conormal basis
`t1,...,tk`. Thus `(c,n)=(k,k+1)`. I computed the following exact integer cone
matrices using the predicate's row order `(B,V)` and column order `(A,W)`, choosing
lifts of `dx` through V and of each `dti` through B:

- C_0 to C_1: `[[0,1],[1,0]]`, determinant -1, cone sign +1,
  hence comparison scalar -1.
- C_1 to C_2:
  `[[1,0,1,0],[0,0,0,1],[0,1,0,0],[-1,0,0,0]]`, determinant +1,
  cone sign `(-1)^(1*(2+1)) = -1`, hence comparison scalar -1.
- C_0 to C_2: `[[0,1,0],[0,0,1],[1,0,0]]`, determinant +1, cone sign +1,
  hence comparison scalar +1.
- C_1 to C_0: `[[0,1],[-1,0]]`, determinant +1, cone sign -1,
  hence comparison scalar -1, inverse to the first comparison.

An exact permutation-expansion calculation checked each determinant and checked
`(-1)*(-1)=+1` for both composition and insertion/deletion. Thus the return's
1+1=2 counterexample now agrees with direct stabilization. The smooth conormal
normalization agrees as well: the ordered wedges
`dt1,...,dtk,dx` relative to `dx,dt1,...,dtk` have sign `(-1)^k`. Identity complexes
have determinant +1 and sign `(-1)^(a*(a+1))=+1`. These are checks of the repaired
normalization, not claims of a completed general proof.

I also reread the item's `IsFlatLCIEtaleLineComparison` inputs:

- The line `C.line` is the existing dual-conormal determinant tensor ambient
  determinant. The normalized pullback comparison rho uses precisely
  `C.conormal`, `C.differentials`, ranks `C.c,C.n`, equalities `rfl,rfl`, and
  identity maps on their actual tensor pullbacks. There is no extra sign in rho.
  The determinant predicate receives `rho.symm` followed by the pulled-back
  C-local identification, the restricted global comparison, and the inverse
  D-local identification. Its domain and codomain are exactly the two-term
  determinant lines required by the signed predicate. For the identity source,
  normalized `tensorPullbackSectionId` cancels the local restriction transports;
  the chart comparison is therefore subject to the same corrected cone signs.
- `r.conormalMap` is the normalized tensor source comparison followed by pullback
  of `r.idealMap`, whose `ideal_normal` fixes it on actual ideal sections.
  `r.differentialsMap` uses the landed
  `Scheme.Hom.relativeDifferentialsPullbackMap` verbatim, followed by
  `relativeDifferentialsCongr` for `r.base_eq`, and then tensor pullback along
  `D.i`. It sends actual universal differentials to their pullbacks.
- The cone differential inputs are exactly the pullback of `deltaC` and `deltaD`,
  constrained by `C.IsConormalDifferential` and `D.IsConormalDifferential`.
  Hence the conormal generators map to the corresponding differential generators
  and give the chain-map equality required by the predicate. They are not
  arbitrary differential or ideal maps. The rank equality is
  `C.c + D.n = D.c + C.n`, including the 1- and 2-variable presentations.

No hypothesis, preservation clause, identity/composition/open-restriction formula,
or smooth differential clause changed. No statement correction or new node is
needed: the defect was precisely the dependency normalization, now repaired on
the base. `scompile.py N0 lem-sfb-etale-source-adjunction-line
lean/Sheaf/AlgebraicGeometry/EtaleSourceAdjunctionLine.lean` passed both sandbox
(10.8 seconds) and library (11.7 seconds) modes with no errors or unexpected
warnings against that live dependency. The maintainer's independent review still
supplies the independent reading; this worker's checks above are self-checks.
