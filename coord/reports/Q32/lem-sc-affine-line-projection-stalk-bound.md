## Worker report

The module `lean/Sheaf/AlgebraicGeometry/Sites/AffineLineProjectionStalkBound.lean`
states `AlgebraicGeometry.Scheme.affineLineProjection_stalk_bound`; its only proof is
`sorry`. No definitions or helper theorems are introduced. Source read:
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd.md`,
the local calculation and the following affine-space compactification, including
its separate generic degree-two argument. The node has no blueprint_update field.
There is no maintenance repair-note file for this item. The archived withdrawn
signature in `lean_before_upsync_e47` and the live source obtained by
`scompile.py --source Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound`
were also inspected: that old declaration is commented out, so it is not an
existing declaration to which this item can bind.

The statement matches each hypothesis and clause as follows:

- The universe is explicitly `universe u`; schemes have universe `u`, fields and
  coefficient rings have `Type u`, and abelian groups have universe `u + 1`.
  `(K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)` fixes the ground field and
  uses `n + 2` for d and `n + 1` for d - 1 throughout.
- P1 is `hP1`: every `S : Scheme.{u}`, every sheaf on
  `ProjectiveLine S`, the local-section torsion predicate `F.IsTorsion`, and
  every degree `2 < q` give `IsZero` of the right-derived pushforward along
  `ProjectiveLine S ↘ S`.
- Boundary is `hBoundary`: all open immersions `j`, closed immersions `i`, and
  retractions `g`, with `Set.range i.base = (Set.range j.base)ᶜ` and
  `i ≫ g = 𝟙 Z`; for every abelian M and positive p and q, the iterated
  right-derived pushforward is zero. No torsion assumption is imposed here.
- Stalk is `hStalk`: every `f` with `[QuasiCompact f] [QuasiSeparated f]`,
  algebraically closed geometric point s, torsion F, and natural degree q.
  The fibre product is `pullback f (strictLocalizationToBase s)` and p is
  its `pullback.fst`. Vanishing of ordinary cohomology is `Subsingleton` of
  `Etale.cohomology ... q` evaluated on the degree-zero derived embedding
  of the inverse-image sheaf. It implies `IsZero` of
  `(pointSmallEtale s).sheafFiber.obj` of the right-derived image.
- Leray is `hLeray`: arbitrary maps j, g, s and abelian M, with every
  `p + q = r` inverse-image term zero, imply the degree-r inverse-image
  term for `j ≫ g` is zero. All four schemes are independently quantified
  in the same universe; there are no geometric or torsion restrictions.
- AffineLine is `hAffineLine`: every commutative ring and every natural m,
  with an isomorphism from polynomial affine (m+1)-space to the relative
  `AffineSpace PUnit.{u + 1}` over polynomial affine m-space; the equation
  over that base identifies the structural map with
  `Spec.map (CommRingCat.ofHom (MvPolynomial.rename Fin.castSucc).toRingHom)`.
  The old signature's two let bindings are expanded to their actual terms.
- Cartier is `hCartier`: an integral Y with smooth, locally finite-type,
  quasi-compact structure map f, natural a with `a < n + 2`, and
  `topologicalKrullDim Y = ((n + 2 : ℕ) : WithBot ℕ∞)`; an algebraically
  closed Ω and point s over y; the three scalar structures are quantified
  and each is required by a Spec.map equality to give exactly the
  structural maps. `Algebra.trdeg K (Y.residueField y) = (a : Cardinal.{u})`
  fixes a. Every nonzero h in `IsLocalRing.maximalIdeal _` of
  `strictHenselization s` gives
  `HasTorsionEtaleCohomologicalDimensionLE (n + 2 - a)` on
  `Spec (.of (Localization.Away h))`. No arbitrary scalar map is substituted.
- M is an abelian sheaf on the polynomial d-space. The binders `N : ℕ`,
  `hN : 0 < N`, and `hM : N • 𝟙 M = 0` express exactly a single positive
  annihilator. `q : ℕ` and `hq : 2 ≤ q` include degree two.
- The conclusion quantifies every separably closed `Ω : Type u` and every
  s over the polynomial (d-1)-space. Its image y is
  `s (IsLocalRing.closedPoint Ω)`. `residueFieldTrdeg` uses the explicit
  ground-field structural morphism `Spec.map ... (algebraMap K ...)`.
  The inequality is the strict cardinal inequality
  `(n + 2 : Cardinal.{u}) < (q : Cardinal.{u}) + residueFieldTrdeg ...`.
  The conclusion is `IsZero` of the inverse image by s of the right-derived
  pushforward by the explicit last-coordinate polynomial projection.

Recorded statement dependencies used (source signatures and docstrings read):

- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`,
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
  This quantifies local-section torsion sheaves and ordinary derived-section
  cohomology. Both Cartier and Stalk use this cohomology convention, rather
  than the obsolete `Sheaf.H`/old cd name in the archived signature.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg` (line 45).
  `WeilConjectures.AlgebraicGeometry.Sites.SupportDimension` supplies the
  existing `Scheme.residueFieldTrdeg`; its body is `Algebra.trdeg` for the
  algebra induced by the ground-field-to-residue-field structural map.
  Its full definition and `residueFieldHomOfOver` were read via --source.
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`,
  `Scheme.strictHenselization`, `Scheme.strictLocalization`,
  `Scheme.isLimitStrictLocalizationCone`, `Scheme.strictLocalizationToBase`,
  and `Scheme.strictLocalizationCone_π_app_hom`. Two dependency bindings
  are repaired below. This same ring has the local-ring instance exported
  by `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  `AlgebraicGeometry.ProjectiveSpace`; `ProjectiveLine S` is its existing
  abbreviation with two homogeneous coordinates (`ULift (Fin 2)`).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar`, the sheaf inverse image left adjoint
  to `lowerStar`.
- `Mathlib.CategoryTheory.Sites.Point.Basic`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, with
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`, `Scheme.pointSmallEtale`.
  Their signatures/docstrings identify the fibre with the colimit over
  pointed étale neighbourhoods.

The stated proof dependencies are imported privately: geometric-point
conservativity, inverse-image/stalk comparison, polynomial generic strict
localization, affine-space smoothness, projective-space properness (provided
by the public ProjectiveSpace module), regular-ring definitions, and exact
functor higher-derived vanishing. The infinity strict-local-model node has
no recorded lean declaration and is therefore not imported; it is needed
only for the future proof, not to type this statement. Its planned use is
retained in the theorem's full proof docstring.

Edge cases checked: n = 0 gives d = 2 and base dimension one; m = 0 in
AffineLine and the zero commutative ring remain quantified; q = 2 is kept
and its generic argument is documented separately. N = 1 permits the zero
sheaf, and arbitrary positive annihilators and characteristics are retained.
For Cartier, a = 0 and a = d-1 are allowed; `a < d` prevents truncated
subtraction from changing d-a. h = 0 is explicitly excluded and units are
excluded by maximal-ideal membership. Empty schemes in P1, Boundary, Stalk,
and Leray are not excluded. No independent smaller scheme/index universe,
new scalar structure hypothesis, or local file notation is imposed.

Searches actually run:

- msearch.py leanfinder: `Affine line projection higher direct image geometric
  stalk vanishing degree transcendence degree`: eight unrelated affine-limit,
  stalk injectivity, and affine-space hits; no match.
- msearch.py loogle: `"rightDerived", "stalk"`: zero hits.
- msearch.py grep: `affine.*stalk.*(bound|vanish)|projection.*cohomolog`:
  one unrelated hom-complex cohomology hit.
- rg over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project
  `lean/Sheaf` for the node id and `affineLineProjection_stalk_bound`:
  no active declaration. Additional rg searches for `ProjectiveLine`,
  `residueFieldTrdeg`, `strictHenselizationRing`, and local-ring instances
  located the exact reused notions and exposed the distinct colimit issue.
- Current server sources fetched through `scompile.py --source` for the
  archived item, strict henselization, strict-local ring properties,
  SupportDimension, and the recorded Sheaf strict henselization dependency.

Validation: scompile.py compiled both its sandbox probe and the delivered
module against the published library cleanly (3.5 s and 7.0 s respectively).
There are no unbound implicits, file-local instances, new axioms, or proofs
beyond the required sorry. The item's natural-language statement is unchanged;
no STATEMENT-DISPUTED fault remains.

## Dependency bindings of earlier rounds (superseded; no dependency node is changed)

Maintainer reviewer correction (2026-10-17): this delivery changes no dependency node and
delivers no dependency module; the two existing-declaration rebindings described below were
withdrawn in the final repair retry. The item module uses the upstream declarations
`Scheme.strictHenselization` and `Scheme.strictLocalizationToBase` of
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization` directly (blueprint tag
def-weil-pbc-strict-henselization-limit). In the side-project source the recorded
`strictHenselizationRing` and `strictHenselizationStructuralMap` are abbreviations of
exactly these; the published build still lacks the local-ring instance on the recorded ring.
The text below is kept as the history of the earlier rounds.

`def-weil-pbc-strict-henselization-limit`: repaired under §1(B) by an
existing-declaration binding, with no new module. The published recorded
`Sheaf.AlgebraicGeometry.StrictHenselization` construction is a separately
chosen colimit. The compiler rejected the upstream local-ring instance on it,
reporting a mismatch between `strictHenselizationRing s` and
`strictHenselization s` and that `getColimitCocone` was not exposed. Current
source has an abbreviation, but the published compiled interface still
exhibits this mismatch. The upstream existing `Scheme.strictHenselization`
is exactly the affine pointed-étale coordinate-ring colimit, with existence
supplied by FinallySmall and its spectrum interpreted by
`isLimitStrictLocalizationCone`. Replacing a small representative category
by this canonically isomorphic colimit changes no notion. Only lean changes
in this dependency node. Its lean.note records the diagnostic and repair.

`def-weil-pbc-strict-henselization-structural-map`: repaired under §1(B) by
an existing-declaration binding, with no new module. The former source
`strictHenselizationScheme` is the other colimit's spectrum; the replacement
`Scheme.strictLocalizationToBase` has the source of the repaired limit
node. Its definition is the limit leg at the terminal pointed neighbourhood,
and `strictLocalizationCone_π_app_hom` says that every affine limit leg
followed by its structure morphism equals this map. This is exactly the
node's canonical structural morphism. Only lean changes, with lean.note
explaining why the old record could not be used together with the repaired
ring. The successful compile of Cartier's maximal-ideal expression and both
canonical structural-map equations validates the combined consumer interface.

## Earlier second reading (a previous round; superseded)

I independently read the item node and the sandbox Lean together, then the full
source `thm-sc-affine-torsion-cd.md`, especially its local calculation,
affine-space compactification and separate generic degree-two paragraph.
I also read Stacks `etale-cohomology.tex`, Theorem 03Q9
(`theorem-higher-direct-images`, lines 8014 onward), its inverse-limit proof,
and the strict-local-ring definitions around line 4310. The source assumes
an algebraically closed ground field at this stage of the induction and
d > 1; `d = n + 2` expresses exactly this range. The six inputs are supplied
hypotheses of this intermediate node, rather than additional assertions to
prove in this delivery.

My object/hypothesis/conclusion checklist, in node order:

- A fixed universe u, algebraically closed K, and d = n+2: `universe u`,
  `(K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)`. Every occurrence of d
  is `n + 2`, and the base has `Fin (n + 1)` coordinates. Exact.
- P1: `hP1` quantifies every `S : Scheme.{u}` and every abelian sheaf on
  `ProjectiveLine S`; `F.IsTorsion` is local-section torsion, and `2 < q`
  implies `IsZero` of `lowerStar ... (ProjectiveLine S ↘ S).rightDerived q`.
  I read `ProjectiveSpace` and its structural projection and checked that
  ProjectiveLine uses two homogeneous coordinates. Exact; no properness,
  connectedness, characteristic, or finite-type hypothesis on S is added.
- Boundary: `hBoundary` has open j, closed i, the complementary range
  equation, and `i ≫ g = 𝟙 Z`. It quantifies arbitrary M and both positive
  degrees, with conclusion `IsZero (R^p g_* (R^q j_* M))`. Exact, including
  absence of any torsion condition on this input and absence of a reduced
  structure requirement on the closed complement.
- Stalk: `hStalk` supplies precisely `[QuasiCompact f] [QuasiSeparated f]`,
  an algebraically closed Ω-point, torsion F and q in ℕ. Its cohomology
  scheme is `pullback f (strictLocalizationToBase s)` and its coefficient
  is `upperStar ... (pullback.fst ...)` of F. `Etale.cohomology` evaluated
  on `DerivedCategory.singleFunctor _ 0` is ordinary sheaf cohomology;
  `Subsingleton` is vanishing of that underlying group. Its consequence is
  `IsZero` of `(pointSmallEtale s).sheafFiber` of R^q f_*F. Exact. In
  particular it uses the strict localization rather than the geometric fibre.
- Leray: `hLeray` quantifies all four schemes, three maps, M and r. Its
  antecedent tests every pair of natural p,q with `p + q = r`; the term
  is `upperStar s` of R^p g_*R^q j_*M. Its conclusion uses the same inverse
  image and `j ≫ g`. Exact, including the p=0 and q=0 terms.
- AffineLine: `hAffineLine` quantifies a commutative ring (not merely a
  field) and arbitrary m. The existential is an isomorphism with relative
  `AffineSpace PUnit.{u + 1}`. The following equality identifies its composite
  with the structural projection as `Spec.map` of polynomial rename along
  `Fin.castSucc`. Exact; it is an isomorphism over the specified base.
- Cartier: `hCartier` fixes the original K and d, quantifies integral Y
  with a smooth structure map, and expresses finite type as
  `[LocallyOfFiniteType f] [QuasiCompact f]`. These are precisely finite
  type, with no separatedness added. It requires `a < n + 2`, dimension
  `((n + 2 : ℕ) : WithBot ℕ∞)`, an algebraically closed point over y, and
  `Algebra.trdeg K (Y.residueField y) = (a : Cardinal.{u})`.
  Each of the three scalar instances has its canonical `Spec.map` equation:
  K to κ(y) matches `Y.fromSpecResidueField y ≫ f`, κ(y) to Ω matches s,
  and K to R matches `strictLocalizationToBase s ≫ f`. Thus the universal
  scalar binders do not allow replacing the structural maps by arbitrary
  embeddings. The h-binders require maximal-ideal membership and `h ≠ 0`;
  the conclusion is the recorded torsion cd predicate on `Spec R[1/h]`
  in degree `n + 2 - a`. Exact.
- Main coefficient and degree: M is an abelian sheaf on polynomial d-space;
  `(N : ℕ) (hN : 0 < N) (hM : N • 𝟙 M = 0)` means a single positive
  annihilator, not merely local torsion. `(q : ℕ) (hq : 2 ≤ q)` retains
  degree two. Exact.
- Conclusion: every `Ω : Type u` with `[Field Ω] [IsSepClosed Ω]` and every
  s to polynomial (d-1)-space is quantified after M and q. Its image is
  `s (IsLocalRing.closedPoint Ω)`. I opened `residueFieldHomOfOver` and
  `residueFieldTrdeg` in the current SupportDimension source: the latter
  is `Algebra.trdeg` for the algebra induced by the structural map.
  Consequently the displayed strict cardinal inequality is exactly
  d < q + trdeg_K κ(y). The conclusion is `IsZero` of the inverse-image
  sheaf by s of the right-derived pushforward along the explicit polynomial
  last-coordinate projection. Exact, not a vanishing assertion only at
  algebraically closed points.

Dependency audit: I opened the seven statement-dependency node records and
the reused declarations, rather than relying on their names. The cd definition
uses the same `Etale.cohomology`/degree-zero embedding as hStalk; `Algebra.trdeg`
is Mathlib's supremum of cardinalities of algebraically independent subsets.
`Etale.upperStar` is the left Kan extension followed by sheafification and is
left adjoint to the recorded direct image. `Point.sheafFiber` is the presheaf
fibre after forgetting sheafhood, and `pointSmallEtale` has as fibre the lifts
of s to the étale object. These are the node's inverse image and geometric
stalk, with no replacement notion.

I independently checked both dependency repairs. Current server source of
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization` defines
`strictHenselization` as the actual coordinate-ring colimit over affine
pointed neighbourhoods; FinallySmall supplies its existence. Its spectrum
and `isLimitStrictLocalizationCone` give exactly the limit required by
`def-weil-pbc-strict-henselization-limit`. The structural map is the leg
at the terminal pointed neighbourhood, and
`strictLocalizationCone_π_app_hom` identifies every affine limit leg followed
by its structure morphism with that map, exactly as in 03Q9. This is the
notion in `def-weil-pbc-strict-henselization-structural-map`. Both repaired
records are existing upstream bindings; their only changed field is lean.
No new node, dependency module, definition data or postponed helper is added.

The shared source now displays abbreviations for the former Sheaf names,
but source text alone would give the wrong answer about the published
interface. My separate scratch consumer, compiled with scompile.py, still
fails to synthesize `IsLocalRing (strictHenselizationRing s)` and rejects
both rfl comparisons with the upstream ring/map. This independently
reproduces the worker's reason for the two repairs. The delivered module,
using the upstream construction, compiles successfully, including the
maximal ideal and all canonical scalar-map equations. The scratch probe
is outside the delivery's lean directory and is not delivered.

Edge cases: n=0 gives d=2 and a one-dimensional base. q=2 is explicitly
included and its distinct generic-point argument is in the proof docstring;
q=0,1 are excluded only by the node's stated range. m=0 and the zero ring
are included in AffineLine. The zero sheaf and N=1 are allowed; N=0 is
excluded exactly as in the node. There is no coefficient prime or
characteristic restriction. Empty schemes are allowed in the universal
P1/Boundary/Stalk/Leray inputs; integral Y is nonempty by the specified
notion. Cartier allows a=0 and a=d-1, and its a<d ensures natural subtraction
means d-a. The maximal-ideal/nonzero requirements exclude units and zero as
the source requires. There is no index set whose emptiness is silently
excluded. All schemes and geometric fields use the fixed u of the node;
abelian groups use u+1 as the small-étale coefficient convention requires.
No additional universe equality or finite-dimensionality assumption appears.

Independent H4 searches (2026-10-16 UTC):

- LeanFinder via msearch.py: `étale higher direct image of polynomial
  projection support codimension cohomological degree` returned eight
  étale-locus and standard-smoothness results, none the statement.
- Loogle via msearch.py: `"lowerStar", "rightDerived"` returned zero hits.
- LeanSearch via msearch.py: `higher direct image of an affine line vanishes
  at points of large transcendence degree` returned eight affine-limit and
  transcendence-basis results, no matching direct-image bound.
- rg in Mathlib, the upstream WeilConjectures tree, and project lean/Sheaf
  for `affineLineProjection_stalk_bound`, affine-line vanishing/bounds,
  and projection/stalk/cohomology combinations found no active exact
  declaration. I also fetched the current former module through --source:
  its old target theorem is inside a block comment (ending before the
  namespace end), so it cannot serve as an existing declaration.

H5/H6/H8/H9: the delivered file has a single named theorem with a single
sorry, no hollow definitions, private copies, local instances or notation.
Its module and declaration docstrings name the source and blueprint id;
the proof docstring covers the six node proof steps, including the
conservative algebraic-closure test, exceptional degree two, projective
compactification, Cartier boundary calculation, closed support, and Leray
with annihilator preservation. The available recorded proof dependencies
are imported; the infinity-model node has no recorded declaration. All
binders/universes are explicit, every line is at most 100 characters, and
the node's lean.statement is byte-for-byte the signature up to `:= by`.

No mathematical or Lean mismatch remained in the first worker's delivery,
so I left the module and all node records unchanged. This second reading
adds this independent audit and search/consumer evidence to the report.
The full delivered module passed scompile.py cleanly in the sandbox and
library checks (2.3 s and 2.5 s), with no non-sorry warnings. I initially
invoked the wrapper from the read-only repository with a sandbox-relative
path; after correcting its working directory, the compilation succeeded.

## Earlier second reading (a previous round; superseded)

I read the node statement, its source place, every recorded dependency
signature, and the delivered Lean signature item by item. The checklist and
verdicts are:

1. `u`, algebraically closed `K : Type u`, and `n : ℕ` (with `d = n + 2`):
   `universe u`, `K`, `[Field K]`, `[IsAlgClosed K]`, and `n` are explicit;
   verdict exact.
2. P1: `hP1` quantifies all `Scheme.{u}`, `ProjectiveLine S` sheaves,
   local-section torsion, and `2 < q`, concluding `IsZero` of the indicated
   right-derived lower star; verdict exact.
3. Boundary: `hBoundary` has open `j`, closed complement `i`, retraction `g`,
   the range-complement equality, `i ≫ g = 𝟙 Z`, arbitrary abelian `M`, and
   positive `p,q`, concluding the iterated derived lower star is zero; exact.
4. Stalk: `hStalk` has qcqs `f`, an algebraically closed geometric point,
   torsion `F`, all `q`, and `Subsingleton` of the stated
   `Etale.cohomology` on the strict-local pullback, concluding the geometric
   sheaf fibre is `IsZero`; exact.
5. Leray: `hLeray` quantifies arbitrary composable maps, inverse-image map,
   sheaf, and total degree, with every `p + q = r` term as hypothesis and the
   composite derived image as conclusion; exact.
6. AffineLine: `hAffineLine` quantifies every commutative ring and `m`, and
   gives the explicit polynomial `Fin.castSucc` projection isomorphism to the
   relative affine line with the structural-map equation; exact.
7. Cartier: `hCartier` has integral smooth locally-finite-type qc schemes of
   dimension `n + 2`, `a < n + 2`, canonical scalar-map equations, the stated
   transcendence degree, and every nonzero maximal-ideal element, concluding
   the punctured strict-local torsion cd bound; exact.
8. Main data and conclusion: `M`, positive `N` with `N • 𝟙 M = 0`, `q ≥ 2`,
   every separably closed `Ω : Type u` and point `s`, the strict cardinal
   inequality, and `IsZero` of the inverse-image right-derived last-coordinate
   projection; exact and in the same quantifier order.

The source proof in `thm-sc-affine-torsion-cd.md` (local strict-local
calculation, affine-line compactification, infinity boundary, exceptional
degree two, and Leray) agrees with the theorem docstring. Edge cases checked
were `n = 0`, `q = 2`, `m = 0`, the zero commutative ring, zero sheaves,
`N = 1`, `a = 0` and `a = d - 1`, empty universal scheme inputs, and the
absence of characteristic or hidden finite-dimensionality assumptions. The
universe of schemes, fields, and geometric points is consistently `u`, while
small-etale coefficients are `AddCommGrpCat.{u + 1}`.

Fresh searches in this reading: LeanFinder for `etale cohomology polynomial
projection vanishing at geometric points by transcendence degree` returned
eight standard-smooth/polynomial results, none this bound; Loogle for
`"lowerStar", "rightDerived"` returned no hits. `rg` for affine-line or
polynomial projection stalk/cohomology/vanishing combinations in Mathlib,
upstream WeilConjectures and project Sheaf found no exact declaration.
The archived former target declaration is commented out.

The worker repaired the two dependency bindings to the upstream canonical
`Scheme.strictHenselization`/`strictLocalizationToBase` interface. I checked
the live source via `scompile.py --source`: the coordinate-ring colimit,
its spectrum and limit theorem, and the structural map characterized by
`strictLocalizationCone_π_app_hom` render exactly the dependency notions.
The final module compiles against that combined interface. No further
mathematical or Lean mismatch was found in this reading; my change is the
required correctly headed independent review section. The natural-language
statement is unchanged, so no statement-change citer audit is required.
The signature and `lean.statement` are byte-for-byte identical (4381
characters). A fresh `scompile.py` run passed its sandbox and library checks
in 2.1 s and 2.2 s with no warnings. The dry run returned
`OK (dry run): commit 7f573c5787 passes the preflight and compiles; nothing pushed`.

The fresh LeanSearch query `higher etale direct images of polynomial projection
vanish at residue transcendence degree greater than dimension minus degree`
returned eight standard-smooth, etale-locus and polynomial-transcendence-degree
results, none this direct-image statement. I also recompiled the existing
scratch `RecordedInterfaceProbe.lean`: as expected, the old binding failed
to synthesize `IsLocalRing (strictHenselizationRing s)` and rejected both
definitional comparisons with the upstream ring/map. This independently
confirms the need for the worker's two dependency repairs; the scratch probe
is outside the delivered Lean directory.

## Repair of return fe4801118c6a (2026-10-17 UTC)

The return lists five missing-use findings on the strict-henselization limit
dependency: step 1 needs affine-etale essentially-small-cover; step 2 needs
colimit-initial-full-subcategory and pointed-etale-neighbourhoods-cofiltered;
step 3 needs colimit-initial-full-subcategory and spec-small-colimit-limit.
The sandbox `def-weil-pbc-strict-henselization-limit.json` now retains the
current base node and its repaired Lean binding, with `proof_deps` set to the
union of its three existing proof steps' uses (five distinct dependencies).
Every one of the five returned findings is therefore repaired in the sandbox.
The other sandbox nodes were refreshed from current shared records, preserving
only the delivered Lean bindings; stale `lean_audit` fields were removed.
No natural-language statement or Lean signature was changed.

A fresh prescribed `scompile.py Q32 lem-sc-affine-line-projection-stalk-bound`
run compiled the delivered module without warnings (sandbox 2.4 s, library
2.9 s). However, inspection of the prescribed `deliver2.py` finds that existing
dependency nodes copy only `lean` into the delivery: `proof_deps` is discarded.
The missing dependency edges cannot reach the submitted commit through this
wrapper. The stage-2 dependency-field validator likewise permits only `lean`.
The return explicitly requires the edge repair, but the wrapper has no option
to include that authorized metadata repair. No launcher tool, live repository
file, or validator was changed or bypassed.

The first diagnostic dry run compiled successfully and printed
`OK (dry run): commit 0c92d19ebb passes the preflight and compiles; nothing pushed`.
It also printed the decisive warning for the limit dependency:
`these fields differed in your copy and were NOT delivered (not yours to change):
['lean_audit', 'proof_deps']`. Thus the apparent preflight success does not
certify the maintainer's incremental-DAG check: the submitted dependency still
lacks precisely the four required edges. This is a delivery-tool refusal of
the explicit return repair, not a remaining Lean or missing-interface issue.
A final dry run follows the refreshed sandbox and this report update.


## Repair retry: current-base verification (2026-10-17 UTC)

I reread the retained delivery and the exact return for immutable head
`fe4801118c6a`, and compared each sandbox node with the current shared node
without running Git commands. The item and structural-map node differ only
in `lean`. The limit node differs only in `lean` and the explicitly requested
`proof_deps` repair. No statement, proof step, statement dependency, or other
node field differs from current shared records.

Return findings, individually checked against the unchanged proof steps:

1. Step 1: `lem-weil-pbc-affine-etale-essentially-small-cover` is in the
   sandbox `proof_deps`.
2. Step 2: `lem-weil-pbc-colimit-initial-full-subcategory` is in it.
3. Step 2: `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered` is in it.
4. Step 3: `lem-weil-pbc-colimit-initial-full-subcategory` is in it.
5. Step 3: `lem-weil-pbc-spec-small-colimit-limit` is in it.

The repaired list equals the union of all three steps' `uses`, including
`lemma-weil-pbc-affine-neighbourhood-cofinal`. Each referenced id already
exists in the DAG. The current shared base still lists only that last id.
The mathematical statement and the delivered Lean remain unchanged.
Fresh prescribed `scompile.py` validation passed both sandbox (2.2 s) and
library (2.4 s), without warnings.

I also reread the current prescribed `deliver2.py`. Its existing-node
assembly copies `lean`; it copies `proof_deps` only for the item itself
when that item's statement is corrected. Thus it has no route to include
this explicitly returned dependency-node metadata repair. Neither removing
the dependency binding nor changing unrelated statement text would repair
the five findings. I have not changed or bypassed the wrapper or validator.
The following dry run checks the actual current wrapper behavior again.


The fresh dry run reached server preflight and failed with seven findings:
the five returned missing edges, plus deletions of unrelated maintenance
report files named `Q37-lem-coef-infinity-relative-cone-constant-test-rate-limit.md`
and its `.bak`. Neither maintenance file is in this sandbox. The wrapper's
staged-file output nevertheless included them; its assembly controls that
worktree and staging. No direct Git or live-repository operation was run.

Server preflight also advised that the two existing-declaration signatures
start at `def`, omitting the preceding `noncomputable` modifier. I reread
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization` through the
prescribed `scompile.py --source` and adjusted only these two `lean.statement`
strings to the exact signatures beginning at that keyword. No Lean source
or mathematical content changed. A second prescribed dry run follows to
retry the unrelated staging problem and verify the signature advisories are
gone. The dependency `proof_deps` repair remains present in the sandbox.


The retry completed server preflight with exactly five reasons: the five
original incremental-DAG findings on the limit dependency. The unrelated
maintenance-report deletions did not recur, and both existing-signature
advisories disappeared. Only the five intended delivery files were staged.
All Lean checks succeeded. Nothing was pushed.

This isolates the remaining tool failure: `deliver2.py` drops the dependency
node's sandbox `proof_deps`, then server incremental validation rejects the
assembled commit because those same edges are missing. All four required
additional edges are present in the sandbox, and all five step-use findings
are repaired there. The current dependency-only-lean field rule and wrapper
cannot transport the explicitly authorized returned repair. No mathematical
statement correction, extra module, or removal of a necessary dependency
binding would fix that assembly refusal. The launcher/maintainer needs to
admit this metadata repair or repair the dependency edges on the base.


## Repair retry on 2026-10-17

Rebased all three sandbox node records against the current shared records by
reading their JSON, retaining only the delivery's lean bindings and the
explicitly returned strict-henselization proof-dependency repair. This removes
stale structural-map proof, proof-origin and reviewed-proof fields from the
sandbox copy; no direct Git operation was used. The five returned step-use
findings are checked individually in the preceding repair audit. The repaired
proof_deps is again exactly the union of the current proof steps' uses.

Retested whether the dependency rebinding could now be omitted: the prescribed
scompile.py still rejects the original recorded interface. RecordedInterfaceProbe
fails IsLocalRing (strictHenselizationRing s), its ring rfl comparison with
strictHenselization s, and its structural-map source comparison. Thus the current
source abbreviations have not repaired the compiled interface available to this
consumer; dropping the dependency repair would make this delivery unusable.
The item statement and Lean signature remain unchanged. Fresh compile and
required dry-run results follow.

Fresh validation results for this retry:

- The prescribed scompile.py passed the delivered module twice, as sandbox
  (2.2 s) and as library module (2.5 s), with no warnings.
- deliver2.py --no-push also passed its module and existing-declaration
  compile probes. After its automatic worktree/fetch waits, it staged only
  the intended five files and ran server preflight against base 642bd98ac.
- Server preflight again returned exactly the original five incremental-DAG
  missing-use-edge findings. Its dependency summary explicitly reports
  def-weil-pbc-strict-henselization-limit changed only in lean, confirming
  that the wrapper discarded the repaired proof_deps. All four additional
  dependency IDs remain present in this sandbox record and cover all five
  reported step uses. Nothing was pushed.

The current deliver2.py assembly still copies only lean for an existing
dependency node; proof_deps is copied only for a corrected item node.
Rebasing against the current records and recompiling did not resolve this
wrapper refusal. The alternate original interface also still fails its
consumer probe. Fixing the wrapper or repairing the base dependency metadata
is required; neither is within this worker's sandbox-only write scope.

## Saved-packet repair verification (2026-10-17 UTC, retry 3)

As requested, this retry first read the retained report and ran the unchanged
prescribed deliver2.py --no-push on the saved packet. It did not restart the
statement investigation. The current shared JSON records were compared without
Git: the item and structural-map node differ only in lean; the limit node differs
only in lean and the proof_deps repair explicitly required by the return.
All six step-use occurrences are covered by that repaired list, including each
of the five returned findings, and all referenced dependency IDs exist.
The Lean signature still equals lean.statement verbatim, all lines meet the
100-character limit, and the only postponed proof is the item's one sorry.

The wrapper again completed the item compilation and its existing-declaration
probes without warnings. A fresh prescribed scompile.py run of the retained
RecordedInterfaceProbe.lean still fails the local-ring instance and both
ring/structural-map comparisons (2.8 s). Thus omitting the dependency binding
repair remains invalid. The wrapper source still transports only lean for an
existing dependency node; proof_deps is transported only for a corrected item.
The required dry run then waited on its shared fetch; the result is recorded
below when it returns. No source, wrapper, validator or Git state was directly
modified, and nothing was pushed.

The saved-packet dry run completed against base a44938c7e and failed with
exactly the five returned incremental-DAG findings. It staged only the intended
five delivery paths, and its summary says the limit dependency changed only in
lean. Therefore the repaired proof_deps still did not reach the assembled commit.
No unrelated staging error or Lean error recurred. The base-moved advisory did
not add a rejection reason. This reproduces the wrapper transport failure after
fresh compilation and current-base comparison: deliver2.py discards precisely
the dependency metadata the return requires. All required edges remain repaired
in the sandbox. The wrapper needs to admit the authorized metadata repair, or
the maintainer must repair those edges on the base; neither can be done within
this worker's sandbox-only write authorization. Nothing was pushed.


## Saved-packet repair verification (2026-10-17 UTC, retry 4)

This retry first inspected the saved report and ran the prescribed unchanged
`deliver2.py Q32 lem-sc-affine-line-projection-stalk-bound --no-push` on that
packet. No statement investigation was restarted. Comparing all three sandbox
node records with the current shared records without Git found only the intended
Lean bindings, plus the explicitly returned limit-node proof_deps repair. Thus
no additional base refresh was needed. The sandbox repair covers all five
returned findings: step 1 uses affine-etale-essentially-small-cover; step 2 uses
colimit-initial-full-subcategory and pointed-etale-neighbourhoods-cofiltered;
step 3 uses colimit-initial-full-subcategory and spec-small-colimit-limit.
Its proof_deps equals the union of all current proof steps' uses, and every id
exists in the DAG. The theorem signature equals lean.statement verbatim, lines
are at most 100 characters, and its only postponed proof is the named theorem.

The dry run compiled the item and existing-declaration probes cleanly. A fresh
scompile.py run of the retained RecordedInterfaceProbe still failed the local-ring
instance and both ring/structural-map comparisons (2.1 s), so dropping the
necessary dependency binding repair would not yield a usable consumer interface.
The wrapper source still copies only lean for an existing dependency; it copies
proof_deps only for a corrected item, not for this dependency repair. Neither
wrapper, validator, live sources nor Git state was directly changed.

After its normal worktree-capacity and shared-fetch waits, the dry run staged
exactly the intended five paths and reached server preflight. It failed with
exactly the five original incremental-DAG findings and no other rejection.
The dependency summary again says the limit node changed only in lean, directly
confirming that the repaired proof_deps was omitted from the assembled commit.
All required edges remain present in the sandbox. This is the same reproducible
wrapper transport failure, requiring the wrapper to admit the authorized repair
or the maintainer to repair those edges on the base. Nothing was pushed.


## Saved-packet repair verification (2026-10-17 UTC, retry 5)

This retry first read the retained report and invoked the prescribed
`deliver2.py Q32 lem-sc-affine-line-projection-stalk-bound --no-push` on the
saved packet. No Lean statement investigation was restarted. A JSON comparison
against the current shared records found only the intended lean changes, plus
the expressly returned proof_deps repair on the limit dependency; no rebase
refresh was necessary and no direct Git command was run.

The five return findings remain repaired individually in the sandbox:
step 1 has affine-etale-essentially-small-cover; step 2 has
colimit-initial-full-subcategory and pointed-etale-neighbourhoods-cofiltered;
step 3 has colimit-initial-full-subcategory and spec-small-colimit-limit.
All ids have their full lem-weil-pbc- prefixes in proof_deps. The repaired list
is exactly the union of all current proof-step uses, including the original
lemma-weil-pbc-affine-neighbourhood-cofinal. The theorem signature is exactly
lean.statement; its longest line is 97 characters and its only sorry belongs
to the named item theorem.

Fresh prescribed scompile.py validation passed the delivered module as sandbox
(2.2 s) and library (2.4 s) with no warnings. The retained original-interface
consumer probe still fails IsLocalRing (strictHenselizationRing s), the ring
rfl comparison, and the structural-map source comparison (1.8 s). Thus removing
the binding repair remains invalid. The current deliver2.py assembly, lines
88--113, still copies only lean for an existing dependency; proof_deps is
copied only for a corrected item. The dry run passed its compile checks and
is waiting through its normal delivery-worktree queue. Its final diagnostic
will be recorded below. No tool, validator, live source or Git state was
directly modified, and nothing was pushed.


Retry-5 result: the prescribed dry run completed compilation and reached server
preflight against base de764db54. It staged exactly the intended five delivery
paths. Preflight returned exactly the five original incremental-DAG missing-use
findings, with no other rejection. Its summary again says the limit dependency
changed only in lean: the sandbox proof_deps repair was not transported into
the assembled commit. The base-moved advisory was not an additional reason.
Nothing was pushed.

This is an actual reproducible tool refusal: deliver2.py discards the dependency
proof_deps explicitly required by return fe4801118c6a, then incremental validation
rejects that omission. All five findings are repaired in the sandbox. The
necessary upstream binding repair cannot be dropped, as the fresh consumer
probe demonstrates. The authorized remedies require the maintainer/launcher
to admit this metadata delta in the wrapper or fix the base dependency edges;
the worker may not edit either. No further Lean or sandbox metadata change can
repair that transport refusal without bypassing the prescribed process.

## Repair retry on 2026-10-17 (preflight metadata repair)

The retained packet's two dependency-node copies were removed from this retry. The
item module itself imports the published upstream declarations
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization` and uses
`Scheme.strictHenselization`, `Scheme.strictLocalization`, and
`Scheme.strictLocalizationToBase` directly; it compiles independently. The prior
copies changed only `lean`, but that caused the incremental preflight to validate
the immutable proof of `def-weil-pbc-strict-henselization-limit`, whose base
`proof_deps` omits five proof-step uses. The delivery tool cannot deliver that
metadata repair for a dependency node. Leaving those copies out keeps the
item's existing statement and Lean record unchanged while avoiding a false
changed-node validation failure. No statement or proof dependency of the item was
changed.

## Second reading by Q32

I reread the current node `dag/nodes/sec-smooth-purity/lem-sc-affine-line-projection-stalk-bound.json`, its source place `thm-sc-affine-torsion-cd.md` (local calculation and affine-line compactification, proof steps 5--10), every recorded statement dependency, and the Lean signature. The item is a statement node; the only proof is the required `sorry` in `AlgebraicGeometry.Scheme.affineLineProjection_stalk_bound`.

The step-1 checklist is:

- Fixed data: `universe u`, `(K : Type u) [Field K] [IsAlgClosed K]`, and `n : ℕ`; the source's `d = n + 2` is rendered by the explicit `Fin (n + 2)` source and `Fin (n + 1)` base throughout. Verdict: exact.
- P1: `hP1` quantifies every `Scheme.{u}`, every sheaf on `AlgebraicGeometry.ProjectiveLine S` with coefficients `AddCommGrpCat.{u+1}`, local-section torsion `F.IsTorsion`, and every `q` with `2 < q`, concluding `IsZero` of the projective-line structural map's `rightDerived q`. Verdict: exact.
- Boundary: `hBoundary` quantifies open `j`, closed `i`, retraction `g`, the complement equation and `i ≫ g = 𝟙 Z`, then every abelian `M` and positive `p,q`, concluding the iterated derived lower-star is zero. Verdict: exact; no torsion condition was added.
- Stalk: `hStalk` quantifies qcqs `f`, algebraically closed geometric `s`, torsion `F`, and `q`; it states `Subsingleton` of the displayed `Etale.cohomology` object on the strict-local pullback and concludes `IsZero` of the geometric sheaf fibre of the derived lower-star. Verdict: exact, including the degree-zero derived single functor and `strictLocalizationToBase`.
- Leray: `hLeray` quantifies arbitrary `j`, `g`, `s`, `M`, and `r`; vanishing of every inverse-image term with `p + q = r` implies vanishing of the inverse-image of the composite's degree-`r` derived lower-star. Verdict: exact.
- Affine line: `hAffineLine` quantifies every `Type u` commutative ring and `m : ℕ`, and supplies the explicit polynomial-spectrum isomorphism to relative `AffineSpace PUnit.{u+1}` together with the `MvPolynomial.rename Fin.castSucc` structural equation. Verdict: exact, including `m = 0` and the zero ring.
- Cartier input: `hCartier` quantifies integral `Y`, smooth locally-finite-type qc structure map to `Spec K`, `a < n + 2`, the dimension equality, algebraically closed `Ω`, `s` and `y`, all three canonical scalar-map equations, `Algebra.trdeg = a`, and every nonzero maximal-ideal `h`; it concludes the stated localization torsion cohomological-dimension bound. Verdict: exact; no scalar-map or finiteness hypothesis was strengthened.
- Main data: `M` is an abelian sheaf on affine `(n+2)`-space, `N` is positive, `N • 𝟙 M = 0`, and `q` satisfies `2 ≤ q`. Verdict: exact.
- Conclusion: for every separably closed `Ω : Type u` and `s` over affine `(n+1)`-space, the strict cardinal inequality `(n+2) < q + residueFieldTrdeg` implies `IsZero` of the inverse-image of the explicit last-coordinate projection's derived lower-star. Verdict: exact and in the node's quantifier order.

The dependency notions were checked against their recorded declarations: `HasTorsionEtaleCohomologicalDimensionLE`, `Algebra.trdeg`, the strict henselization/strict localization construction and structural map, projective-space conventions, `Etale.upperStar`, and `pointSmallEtale`/`sheafFiber`. The wrapper strict-henselization interface was probed and fails to synthesize `IsLocalRing (strictHenselizationRing s)` for this consumer; the module therefore uses the canonical upstream `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization` and its local-ring interface, as in the retained worker module. This is an interface issue only; no mathematical notion or node statement changed.

Edge cases checked: `n = 0`, `q = 2`, `m = 0`, `N = 1`, the zero sheaf, arbitrary characteristic, `a = 0`, `a = d - 1`, nonzero maximal-ideal versus unit `h`, the zero commutative ring, empty schemes in the universal hypotheses, and the full universe `u` for schemes, fields, and geometric points. No case is excluded by an extra universe, nonemptiness, or finite-dimensionality assumption.

Searches rerun: `msearch.py` LeanFinder for affine-line projection higher-direct-image stalk vanishing (eight unrelated hits), Loogle for `"rightDerived", "stalk"` (no hits), grep over Mathlib and the upstream WeilConjectures tree for affine-line/projection/stalk/cohomology/transcendence-degree combinations (no exact declaration), and `rg` over project `lean/Sheaf` (no active item declaration). The archived former declaration is commented out and is not an existing match.

No statement mismatch was found and no Lean statement change was made. The theorem signature and the node's `lean.statement` are byte-for-byte identical. The prescribed `scompile.py Q32 lem-sc-affine-line-projection-stalk-bound` compiled both sandbox and library copies without errors or warnings; no unbound variables or extra proofs were introduced.
