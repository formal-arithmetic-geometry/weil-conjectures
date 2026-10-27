## Worker report

The item is stated by `AlgebraicGeometry.GabberModification.exists_absolute_equivariant_modification`
in `Sheaf.AlgebraicGeometry.GabberAbsoluteEquivariantModification`. It has one `sorry`, and no proof
has been attempted. Its conclusion existentially chooses one shared fourth-stage procedure and a
four-stage modification for every input triple. The original node statement, source, proof and
proof dependencies are unchanged. `stmt_deps` gains the construction-data definition and the
published procedure definition whose module interface is repaired below.

The source was read in the local ILO PDF, converted to text in the sandbox: VIII Theorem 1.1,
4.1.1--4.1.9, 4.2.11--4.2.13, 5.3.5--5.3.11, 5.4.4, 5.5.2--5.5.5, 5.6.1. The node is a proof
helper, not the blueprint unit statement. Its blueprint ancestor is
`lem-per-artin-gabber-affine-curve`; the current blueprint directory was searched. No statement
correction or STATEMENT-DISPUTED flag is needed.

The clause matching is as follows; all short names below are in
`AlgebraicGeometry.GabberModification`.

- An integral Noetherian quasi-excellent separated fs log regular scheme is the quantified
  `X : FineSaturatedLogScheme.{u}` and `Input a`. The fs and locally Noetherian data are fields of
  the recorded `FineSaturatedLogScheme`, not replacement predicates. `Input` explicitly conjoins
  `IsIntegral`, `IsNoetherian`, `QuasiExcellent`, `Scheme.IsSeparated`, and `X.IsLogRegular`.
  `QuasiExcellent` tests `IsQuasiExcellent Γ(X,U)` for every affine open. Mathlib scheme separatedness
  is the closed absolute diagonal condition; its terminal base is Spec Z.
- A finite group acting by log automorphisms is `G : Type v`, `[Group G]`, `[Finite G]`, and the
  recorded `a : FSLogGroupAction G X`. Tameness and generic freeness are exactly the recorded
  `a.IsTame` and `a.IsGenericallyFree` in `Input`. These test geometric stabilizers; no invertibility
  of the order of the entire group is imposed.
- The original boundary Z is `X.logStructure.trivialityLocusᶜ`. The free locus is the explicitly
  constructed union `freeLocus a` of every invariant geometric-point-free open; F is its complement.
  Thus the node's complement of Z union F is the intersection appearing in `FourStage.Output`.
- Simultaneous choice is the single existential `P` and dependent function `choice`, quantified over
  every finite group, fs log scheme and action, with only `Input a` as input hypothesis. The
  shared `FourthProcedure` includes disconnected charts and its common quotient resolution.
- `Tower` has finite natural length, fs log levels, original log action and identity projection,
  ordered ring ideal centers and log arrows. Each arrow is the existing
  `Monoscheme.IsNormalizedBlowup` with that center, which is an isomorphism over the target to the
  ordinary blowup followed by the componentwise function-field normalization. Nowhere dense
  centers are encoded by `denseCenterComplement`; `invariantCenter` and `equivariant` retain the
  actual centers and actions. The composite realization by such a tower is the existential
  `T,e` in `FourStage.Output`, with its map equation, not an unrelated modification map.
- Projectivity in the projective-bundle sense is the recorded `IsProjectiveBundle F.map.base`.
  The unchanged open is an `Opens X` equal as a set to the intersection of the triviality locus
  and largest free open, with `Dense` and `IsIso (F.map.base ∣_ U)` explicitly asserted.
- Integral fs log regular source, very tame action and equivariance are the first four conjuncts
  of `FourStage.Output`. Very tameness is the recorded `FSLogGroupAction.IsVeryTame`, with tame
  geometric inertia, associated characteristic germs and equality modulo the actual nonunit
  ideal in strict local rings. The triviality-locus equation is precisely the complement form
  of boundary equal to the inverse image of Z union F.
- The first stage is `FirstStage F.first`: each step is a saturated log blowup, and its final
  scheme is regular and log regular. Its tower is normalized and equivariant by the shared
  `Tower` fields.
- The second stage is `SecondStage F.second`: it has actual boundary ideals and tracks their
  OLD strict transform. `stratum` specifies a positive maximal geometric branch number and the
  reduced closed center with exactly that locus; it is nonempty. `ordinary` and `saturated`
  assert both descriptions of every step. `regular`, `finished`, `snc` and `gStrict` assert the
  regular stages, disappearance of the old strict transform, strict normal crossings final
  boundary and G-strictness. `GStrict` says that each component and any translate are equal or
  disjoint, which is equivalent to distinct translates being disjoint.
- The third stage is `ThirdStage F.third`: it consists of finitely many complete `FixedRound`s
  along the monotone cut indices, starting at zero and ending at the last level. `FixedIdeal`
  characterizes each nontrivial subgroup fixed subscheme on ALL scheme-valued test points,
  including nonreduced tests. Each round blows the union of ALL nonempty minimal fixed members,
  strictly transforms the whole family and ends with empty members. Each stage has a nonempty
  permissible center, ordinary blowup map and boundary equal to strict transform union
  exceptional divisor, using the meet of their ideals followed by radical. Regularity, strict
  normal crossings and G-strictness persist. `abelian` and `free` assert exactly the two output
  clauses of this stage.
- `Permissible` gives the unrestricted coordinate definition in the item: after an etale
  localization, one full regular parameter system simultaneously supplies distinct boundary
  factors and a nonempty subset cutting out the center. It does NOT add containment in the old
  boundary: that would exclude the node's fixed centers outside that boundary. The existing
  `IsPermissibleCenter` expressly encodes the boundary-CONTAINED specialization and hence cannot
  be substituted here. Nothing in that existing node is changed.
- The fourth stage is `F.fourth`, definitionally the shared `P.tower` on the third-stage source
  and boundary. `FourthProcedure.localCover` gives an affine surjective quasi-compact strict
  inertia-preserving etale rigidified cover. A `Rigidification` is an actual boundary enlargement
  with a scheme-isomorphism forgetful log map, very tame action and enlarged SNC boundary.
  `RigidifiedQuotient` is the actual finite surjective invariant log quotient and its input to
  the fixed resolution. `RigidifiedConstruction` identifies, in order, every scheme and arrow
  of the assigned fourth tower with the fs pullback of the quotient's saturated resolution.
  Its `ringCenter` identifies the ordered ring centers on geometric strict-local stalks with
  the ideals generated by pulled log sections. Thus maps or unrelated isomorphic objects are
  not substituted for the specified construction.
- `FourthProcedure.localConstruction` holds for EVERY rigidification and quotient presentation
  of every admissible input, all against the SAME assigned tower. It expresses independence
  from the auxiliary boundary, including the ordered ideal centers. The original boundary is
  retained by `result`'s triviality-locus inverse-image equation.
- `Inert` explicitly states log equivariance through a group homomorphism and bijectivity on
  actual geometric stabilizers. For every strict inert morphism, `comparison` is an ordered
  contracted scheme pullback of the chosen towers. Every repeated step has its scheme Cartesian
  square and log commuting square; the center equations retain every nonunit center, including
  proper principal centers. `identity` and `composition` impose both index and log-map laws.
  Together with `localCover` and `localConstruction`, this is the local-gluing clause of the node.
- The final refinement quantifies over EVERY `B : Scheme.{u}` with `[IsAffine B]` and
  `[IsNoetherian B]`, and every structural map `p` of finite type
  (`LocallyOfFiniteType p` and `QuasiCompact p`) with relative `QuasiProjective p`. The conclusion
  is the recorded `IsHProjective F.map.base`, and relative quasi-projectivity and finite type
  of `F.map.base ≫ p`. `QuasiProjective` is exactly an immersion into some projective space
  with N+1 coordinates, whose projection is the given map. `ULift.{u} (Fin (n+1))` puts the finite
  coordinate type in the scheme universe without excluding any finite projective space.

Dependency declarations used: Mathlib `AlgebraicGeometry.IsIntegral` in
`Mathlib.AlgebraicGeometry.Properties`; `IsQuasiExcellent` in `Sheaf.RingTheory.ExcellentRing`;
`FineSaturatedLogScheme`, `EtaleLogHom`, `IsSaturatedLogBlowup`, `IsLogRegular`, `trivialityLocus`,
`idealStalk` and log stalk maps in `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`;
`FSLogGroupAction`, its tame/free/equivariant/quotient predicates in
`Sheaf.AlgebraicGeometry.FSLogGroupAction`; `FSLogGroupAction.IsVeryTame` in
`Sheaf.AlgebraicGeometry.VeryTameFSLogAction`; strictness in
`Sheaf.AlgebraicGeometry.FSStrictLogMorphism`; log identities and composition in
`Sheaf.AlgebraicGeometry.LogMorphismOperations`; normalized blowup property in
`Sheaf.AlgebraicGeometry.MonoschemeToricRealization`, using the canonical normalized construction
of `Sheaf.AlgebraicGeometry.NormalizedBlowup`; `IsStrictNormalCrossingsBoundary`,
`IsRegularScheme` and `ncBranchCount` in their like-named Sheaf modules; `IsProjectiveBundle`
in `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`; `IsHProjective` and projective space in
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective`; regular parameter systems in
`WeilConjectures.RingTheory.IsRegularSystemOfParameters`; strict transforms in
`WeilConjectures.Compactification.StrictTransform`. The procedure and comparison definitions
are reused from `Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure`; their only repair is
listed below. All recorded original statement-dependency signatures and docstrings were read.
The server's current normalized-tower source was read with `scompile.py --source`, since that
interface has changed since the local clone snapshot.

The theorem privately imports every currently present recorded proof-dependency module.
Several proof nodes have no Lean record yet; they need no invented theorem here. The old
`lem-per-very-tame-log-quotient` record explicitly says its module was deleted on 2026-10-20;
that absent module is not imported. Its underlying invariant quotient DEFINITION is present and
is reused directly, as needed to state this item.

Edge cases checked before and during writing: the original empty scheme is excluded by the
node's integrality, not by a new hypothesis; disconnected and empty local covers remain allowed.
Length-zero towers have one level, no arrows and no centers. The empty boundary is represented
by the unit ideal and an empty SNC component family. If old boundary is empty, second stage
can have length zero; otherwise its stratum center has a positive attained maximum. Trivial
or already free actions admit zero third-stage rounds. Empty fixed schemes are never blown;
nonempty minimal families are taken as a whole, preserving equivariance. Fixed subschemes are
not replaced by their point sets. Proper principal centers are retained in fourth-stage
comparisons, while consecutive unit centers are deleted. Tame inertia includes characteristic
zero and permits residue characteristic dividing the order of G away from stabilizers. The base
B is not assumed excellent. Scheme universe u and finite-group universe v stay independent; a
scoped checkUnivs suppression on FourthProcedure only addresses the linter's unavoidable
maximum in the sort of a structure quantifying over all such groups and schemes.

Searches: `msearch.py leanfinder` for Gabber absolute equivariant very tame modification and for
normalized blowup towers found only relative-normalization API (eight hits each); `loogle`
`AlgebraicGeometry.Scheme, MulAction` had no hits; `msearch.py grep`
`VeryTame|NormalizedBlowupTower|IsSaturatedLogBlowup` in AlgebraicGeometry had no hits.
`leansearch` for finite-group minimal-fixed-locus blowups found set-theoretic action lemmas,
not scheme-theoretic fixed families. The final LeanSearch query for four-stage Gabber data
found generic gluing/normalization API; LeanFinder for rigidification-independent very tame
log towers again found only relative normalization. Direct rg of Mathlib/AlgebraicGeometry,
WeilConjectures and Sheaf found no FourStage, FourthProcedure, FixedRound or
RigidifiedConstruction interface. It found and led to reuse of FSLogGroupAction, IsVeryTame,
IsStrictNormalCrossingsBoundary, canonical normalized blowups and Monoscheme.IsNormalizedBlowup.
Upstream IsQuasiProjective is only over a field, so cannot express the affine-base refinement.
DAG search found theorem nodes for the proof steps, but no definition node for these combined
construction data. `blueprint_refs.py search four-stage` found zero, and search rigidification
found only two unrelated Picard units. All msearch results are also recorded in the new node's
mathlib_searches without replacing them by a claim of success.

Validation: all three delivered Lean files compiled separately, in dependency order, with
`scompile.py` against the live published project. No errors or warnings remain. The sole
postponed theorem is the item's main theorem; definitions contain concrete expressions and
structures with explicit fields, never sorry data. The theorem docstring contains all ten
original proof steps and their dependency ids. No statement, proof or source correction was
made. The first delivery dry run compiled all files and requested the current new-node schema key
`import_flags`; the new definition node now supplies the empty list. The dry run is repeated.

## New nodes

`def-per-gabber-modification-data` defines the genuinely missing construction data described
above, in `Sheaf.AlgebraicGeometry.GabberModificationData`. It supplies finite equivariant
centered towers, subgroup fixed-family rounds, the specific four-stage procedure, the
rigidified quotient pullback diagrams, independence and strict inert compatibility, and the
relative-base output predicate. Source: ILO VIII 1.1, 3.3.15, 4.1.1--4.2.13,
5.3.5--5.5.5, 5.6.1; X 1.4--1.7. Its search records contain all three required search kinds
and DAG/blueprint searches. Existing primitive notions are imported and reused. There is no
new theorem, assumption of arbitrary maps, or Nonempty choice defining undetermined data.

## Dependency modules

`def-trf-strict-etale-log-blowup-procedure`: the exact current server source was obtained using
`scompile.py --source`. Its legacy file format makes the new module-mode consumer fail with
`cannot import non-module Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure from module`.
The delivered repair adds only `module`, changes the existing import to `public import`, and
adds `@[expose] public section`. All definitions, structures, signatures, docstrings and
mathematical bodies are preserved verbatim. Only the dependency node's lean record changes,
with this diagnostic in lean.note. Both its separate compile and the new construction-data
consumer compile pass. This is an interface repair under brief-stage2 §1(B).

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
