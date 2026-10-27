## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitIntegralRadicalCover` states
`AlgebraicGeometry.splitIntegral_radical_cover`, with its sole proof `by sorry`.
The companion definition module supplies eight real Prop-valued definitions; no
object is chosen from an unproved existence theorem. The item's statement, proof,
proof dependencies and all other mathematical fields are unchanged. Its statement
dependencies gain the new terminology node and three existing constituent nodes.
No statement correction or mathematical dispute was needed.

Source checked online: Conrad, Reductive group schemes,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Definition 3.1.1,
Example 5.1.4, Example 5.1.7, Corollary 5.3.3, Theorem 6.1.16 and
Exercise 6.5.2(i). The latter explicitly defines simply connected semisimple
schemes fibrewise and gives their central covering. The theorem docstring includes
all eight natural-language proof steps from the DAG. The extra equivalence used
to spell out finite local freeness is Stacks Lemma 29.49.2, in Tag 02K9:
https://stacks.math.columbia.edu/tag/02K9.

Hypothesis and clause correspondence:

- Integral group schemes: `H T₀ B : Grp (Over (Spec (.of (ULift.{u} ℤ))))`.
  The ring isomorphism `ULift.ringEquiv` makes this exactly Z in the schemes'
  universe, and allows all later ring base changes in that universe.
- H reductive: `hH : RelativeReductiveCover.IsReductive H`. Its body is
  `Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧ LocallyOfFinitePresentation H.X.hom`
  and the existing reductive field predicate on every algebraically closed
  geometric pullback. An affine morphism is quasi-compact and separated, hence
  this is the required finite presentation. Connectedness and smooth faithful
  matrix unipotence are the recorded field predicates, not new substitutes.
- Chosen split maximal torus: `iT : T₀ ⟶ H` and `hT : IsSplitMaximalTorus iT`.
  This requires a closed immersion, an isomorphism with `relativeSplitTorus`
  of some natural-number rank, and the existing maximal-torus predicate on
  every geometric fibre. Over Z a reductive group with this torus is split by
  Conrad Example 5.1.4; no additional pinning or root datum is assumed.
- Chosen Borel containing that torus: `iB : B ⟶ H`, `j : T₀ ⟶ B`,
  `hB : IsBorel iB`, and `hTB : j ≫ iB = iT`. The fibre Borel condition uses
  `IsBorelGroupScheme`, including closedness, smoothness, connectedness,
  scheme-theoretic derived-series solvability and maximality.
- Existence of T,Q,S,F and the sequence maps is the existential binder with
  `i : T ⟶ H`, `p : H ⟶ Q`, `a : F ⟶ S`, and `π : S ⟶ Q`.
- T is a split torus: `r : ℕ` and
  `Nonempty (T ≅ relativeSplitTorus (Spec (.of (ULift.{u} ℤ))) r)`.
  This is an isomorphism of group objects, with the existing Hopf group law.
- T is closed central: `IsClosedImmersion i.hom.hom.left ∧ IsCentral i.hom.hom`.
  Centrality quantifies over every scheme V over the base and every pair of
  V-points, thus includes arbitrary extensions and nonreduced test rings.
- Q split semisimple: `IsSemisimple Q ∧ HasSplitMaximalTorus Q`. The former
  requires smooth affine finite presentation and the existing semisimple predicate
  on every geometric fibre; the latter supplies a split maximal torus. Over Z
  this is the splitness criterion of Example 5.1.4, not an assertion that every
  reductive group over an arbitrary disconnected base is split from that test.
- S split semisimple and simply connected: the same two predicates for S, and
  `HasSimplyConnectedFibres S`. The latter tests every semisimple central isogeny
  onto every geometric fibre. It uses `GrpObj.ker`, finite kernel, surjectivity,
  centrality on all test schemes, and `IsIso`, so infinitesimal kernels are seen.
- F is closed central: `IsClosedImmersion a.hom.hom.left ∧ IsCentral a.hom.hom`.
- F finite locally free: `IsFinite F.X.hom ∧ Flat F.X.hom ∧
  LocallyOfFinitePresentation F.X.hom`. Stacks Lemma 29.49.2 identifies precisely
  these three conditions with finite local freeness. On the affine base Spec Z
  this means that the coordinate algebra is a finite projective Z-module.
- Both exact sequences: `IsFppfGroupQuotient i p` and
  `IsFppfGroupQuotient a π`, together with flatness, surjectivity, and local
  finite presentation of p and π. The reused quotient predicate gives the
  scheme-theoretic kernel square, the canonical torsor projections, local
  surjectivity in the actual big fppf topology, and the universal property of
  sheafification of the coset presheaf. It is not surjectivity on field points.
- Arbitrary ring base change: `∀ (R : Type u) [CommRing R]
  (f : Spec (.of R) ⟶ Spec (.of (ULift.{u} ℤ))), ...`. Every such morphism is
  the spectrum of the unique integer ring map. Every object and map in the
  conclusion is the actual `(Over.pullback f).mapGrp` image of the object or
  map already chosen, not an unrelated new exact sequence.
- This final conjunction repeats T's rank-r splitting and closed centrality,
  H's reductivity and the supplied split torus, Q's and S's split semisimplicity,
  S's simple connectedness, F's closed centrality and finite local freeness,
  and both fppf quotient/kernel/faithfully-flat locally-finitely-presented
  assertions. Thus both displayed sequences and all listed properties persist.
- Trivial cases: no positive-rank, nontrivial-group, characteristic, smooth-kernel,
  invertibility-of-order, reduced-ring or nonzero-ring hypothesis is present.

Dependencies used (full declarations and modules read):

- `CategoryTheory.GrpObj`, `Grp`, in `Mathlib.CategoryTheory.Monoidal.Grp`;
  `GrpObj.ker` and `kerι` from the upstream
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, reexported
  by `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `AlgebraicGeometry.Spec`, `Spec.map`, in `Mathlib.AlgebraicGeometry.Scheme`.
- `IsAffineHom`, `LocallyOfFinitePresentation`, `Smooth`, `IsClosedImmersion`,
  `Flat`, and `IsFinite`, in their Mathlib AlgebraicGeometry.Morphisms modules
  `Affine`, `FinitePresentation`, `Smooth`, `ClosedImmersion`, `Flat`, and `Finite`.
- `ConnectedSpace`, in `Mathlib.Topology.Connected.Basic`, reused through the
  field reductive, semisimple and Borel predicates.
- `ReductiveTorusCentralizer.IsReductive` and `IsMaximalTorus`, from
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`.
- `IsSemisimpleGroupScheme` and `IsSolvableGroupScheme`, from
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`; `IsBorelGroupScheme`, from
  `Sheaf.AlgebraicGeometry.GroupScheme.Borel`.
- The existing reductive predicate uses `SolvableGroupStructure.IsUnipotent`
  from `Sheaf.AlgebraicGeometry.SolvableGroupStructure`, with a faithful closed
  matrix representation and `(u-1)^N = 0`, `N > 0`, over algebraically closed fields.
- `relativeSplitTorus`, from `Sheaf.AlgebraicGeometry.RelativeSplitTorus`.
- `AlgebraicGeometry.IsFppfGroupQuotient`, owned by definition node
  `def-sfb-fppf-group-quotient-presentation` (Q95, `existing: true`), from
  `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`. Its full
  signature allows arbitrary scheme bases; the affine normal quotient theorem
  in the same module is not a statement dependency.
- The actual base-change functor is Mathlib `Over.pullback`, followed by `mapGrp`.
- Proof-only imports are `RootDatumLatticeEmbedding`, `RingDiagonalizableGroup`,
  `FiniteAbelian.Basic`, `FreeModule.PID`, and `Sites.Precoverage`: these are the
  recorded modules/matches for the available proof dependencies. The remaining
  integral root-datum, relative centre/duality/quotient and field radical nodes
  have no Lean records yet; no import was invented for them.

Edge cases checked mathematically before writing:

- H a torus (including the trivial torus): T=H, Q=S=1, F=1; empty roots allowed.
- H semisimple: r=0 and T=1; F need not be trivial.
- H=PGL2: S=SL2, F=μ2, which is finite locally free and nonreduced in
  characteristic 2. The scheme kernel and fppf conditions retain this case.
- R=0 and Spec R empty: geometric-fibre conditions are vacuous, but the group
  schemes and base-change sequence remain the actual pullbacks; relative split
  tori and quotient assertions continue to make sense.
- Nonreduced R and characteristics dividing |F| impose no extra conditions.
- Geometric test fields, rings and schemes all use the same object universe u,
  never an independent smaller universe that could make a fibre test vacuous.

Searches made:

The prescribed `msearch.py` searches were run under NI and this item; every response
is in `searches.jsonl`, and the new node carries the final search responses verbatim
as JSON. Queries included:

- LeanFinder: "split reductive group scheme over integers quotient central torus
  semisimple simply connected central isogeny" (eight unrelated abstract SL/centre
  and Lie algebra hits).
- Loogle: `AlgebraicGeometry.IsReductiveGroupScheme, CategoryTheory.GrpObj.ker`
  (no hits; unknown first identifier), and `CategoryTheory.GrpObj.ker` (no Mathlib
  hit; the kernel is the upstream extension, which is used).
- Mathlib grep: `ReductiveGroup|SemisimpleGroup|SimplyConnectedGroup|central.*isogeny`
  (zero hits), and `IsRelativeReductive|HasSimplyConnectedFibres|IsSplitMaximalTorus|IsCentral.*Grp`
  (zero hits).
- LeanSearch: "relative reductive and semisimple group schemes geometric fibres
  split maximal torus simply connected central covers" (eight reducedness or
  Lie algebra results, none a group-scheme notion).
- LeanFinder: "central homomorphism group schemes simply connected semisimple
  group geometric fibre maximal torus" (eight abstract linear-group and Galois
  results, none this relative interface).
- LeanSearch and LeanFinder for fppf quotients (scheme finiteness and ordinary
  group exact-sequence hits); project rg found `IsFppfGroupQuotient`, which is
  reused rather than redefining sheaf quotients.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` found no declaration for
  the item identifier. Concept searches found precisely the constituent field
  predicates and relative split torus listed above. The DAG searches found their
  existing nodes. `tools/blueprint_refs.py search 'relative reductive cover'`
  returned zero nodes; the ancestor command returns `None` for this imported
  support chain, which is retained in the new node's provenance.

Verification: both modules compiled separately, in dependency order, through the
prescribed `scompile.py`, with no errors and no non-sorry warnings. No live source
or build was edited. The final delivery dry run is recorded below after execution.

## New nodes

`def-sfb-relative-reductive-cover-terminology` owns the eight predicates in
`Sheaf.AlgebraicGeometry.GroupScheme.RelativeReductiveCoverTerminology`:
`IsCentral`, `IsSimplyConnected`, `IsReductive`, `IsSemisimple`,
`HasSimplyConnectedFibres`, `IsSplitMaximalTorus`, `IsBorel`, and
`HasSplitMaximalTorus`, in namespace `AlgebraicGeometry.RelativeReductiveCover`.
These are the missing relative fibre/central-cover terminology of Conrad 3.1.1,
3.2.1, 5.1.7 and 6.5.2(i). Their definitions are direct Prop expressions and
reuse all field predicates, the relative split torus, group object operations,
and canonical pullbacks. Searches above and in its `mathlib_searches` found no
existing relative covering interface. The unstated pinned-split-root-realization
node contains reductivity as part of a larger pinned root-datum realization,
not a recorded standalone interface for the fibre and covering predicates.
No pinned realization or root datum is replaced or copied here. The quotient
notion was already available and is imported from its owning node.

## Return repairs

The returned immutable head was `13a010508840`. Compared with current main,
the sandbox retains the original mathematical statement, the helper definition
node, and both Lean modules. Both Lean files are byte-identical to the returned
delivery; no mathematical change was requested.

- H2: replaced statement dependency `lem-sfb-affine-normal-quotient-geometry`
  with `def-sfb-fppf-group-quotient-presentation`, the live definition node that
  registers the imported `AlgebraicGeometry.IsFppfGroupQuotient` as existing.
  The dependency declaration and its full signature/docstring were read.
- H11: the worker's own rereading is withdrawn as a second reading. The
  independent reader's review follows in a separately authored section.

## Second reading by NI

Author: independent reader `/root/independent_second_reader`, a separately
spawned agent for this repair. I did not write the statement or its helper
module. I opened the item's full node statement and eight-step proof, both
sandbox Lean modules, the new terminology node, the live quotient definition
node and the full `IsFppfGroupQuotient` declaration/docstring. I also opened
the reused field reductive, semisimple, Borel, unipotence and relative split
torus declarations rather than relying on the worker's account.

The Lean states the node clause by clause. Its input is a reductive group
object over `Spec (ULift ℤ)`, with the chosen split maximal torus and chosen
Borel, and `j ≫ iB = iT` expresses containment. The real definitions require
smooth affine local finite presentation and the specified geometric-fibre
predicates. Affineness makes this finite presentation. The field reductive
predicate includes geometric connectedness and excludes smooth connected
normal unipotent subgroups, with faithful matrix unipotence; the semisimple
predicate excludes smooth connected solvable normal subgroups. The Borel
predicate uses the scheme-theoretic derived series and maximality. Thus these
hypotheses do not merely assert properties of rational points.

The conclusion chooses the same four group objects and four arrows as the
two sequences. `r : ℕ` and the group-object isomorphism to
`relativeSplitTorus` express T's splitting, including rank zero. Closedness
and `IsCentral` express the two central subgroup inclusions; the latter tests
all schemes over the base, including nonreduced ones. Q and S have both the
semisimple predicate and a split maximal torus. S additionally has simply
connected geometric fibres: every surjective homomorphism from a semisimple
group with finite central scheme kernel is an isomorphism. F's structural
morphism is finite, flat and locally finitely presented, equivalently finite
locally free, so no smoothness or reducedness of F is imposed.

For both sequences, `IsFppfGroupQuotient` supplies the actual cartesian kernel
square, fppf local surjectivity, represented sheaf, torsor isomorphism with
its prescribed projections, and coset-presheaf sheafification universal
property. The theorem separately requires flatness, surjectivity and local
finite presentation of p and π. The final universal quantifier ranges over
every commutative ring R and every `Spec R → Spec (ULift ℤ)`; each object and
arrow is the actual image under `(Over.pullback f).mapGrp`. It repeats both
exactness assertions and the split, semisimple, simply connected, central,
closed and finite locally free conditions for those same choices. It does
not choose unrelated witnesses after scalar extension.

I checked the edge cases independently against the predicates: r=0 and
trivial semisimple groups are permitted; for a torus H one can have T=H and
Q=S=1, and for semisimple H one can have T=1. The SL2-to-PGL2 kernel μ2 in
characteristic 2 remains covered because neither finite local freeness nor
scheme-theoretic kernel or centrality requires reducedness. The zero ring
and nonreduced base rings are not excluded. `ULift.{u} ℤ` puts the integer
base in the same explicitly bound universe as the test rings and geometric
fields. Both implicit-variable options are disabled, and the theorem's
recorded signature equals the source signature exactly.

The new definition node owns eight genuine Prop-valued definitions, all
written out with no `sorry` and no data chosen from an existence assertion.
They extend the reused field predicates to the required relative setting;
the only `sorry` in the delivery is the named theorem, whose docstring
contains its source and all eight DAG proof steps. I found no mathematical
statement mismatch requiring a Lean edit.

For H2, the repaired item cites
`def-sfb-fppf-group-quotient-presentation`, whose live `existing: true` record
owns precisely `AlgebraicGeometry.IsFppfGroupQuotient`. Its arbitrary-scheme
base signature is usable here without the affine normal quotient theorem's
hypotheses. The former theorem-node statement dependency has been removed.
For H11, this section is my independent review, replacing the worker's own
rereading. I made no Lean or node changes; my only edit is this report section.

## Repair validation

Both delivered Lean modules passed `scompile.py NI
lem-sfb-split-integral-radical-cover` separately in dependency order against
the live published build, with no errors or non-sorry warnings. The repair
dry run `deliver2.py NI lem-sfb-split-integral-radical-cover --no-push`
returned `OK (dry run): commit 3cf4349d084 passes the preflight and compiles;
nothing pushed`. The independent reader's review above was included in that
validated delivery.
