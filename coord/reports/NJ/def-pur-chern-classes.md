## Worker report

Repaired the returned H3 and H5 faults in `Sheaf.Paper.PurityChernClasses`.
The previous packet chose an arbitrary family from bare `Nonempty`, used an
extra shift on an already shifted Tate object, used étale Hom groups, and did
not encode either the defining projective-bundle equation or the unit in degree
zero. The initial prescribed dry run of that saved packet passed mechanically
(commit d7a4e4b580); the substantive self-check still found those returned faults,
so this delivery repairs the declarations rather than re-pushing that packet.

The construction now selects the unique family satisfying
`IsOrdinaryFiniteChernClasses`. Its existence-and-uniqueness theorem is exactly
the coefficient-extraction obligation implicit in this definition node: its
predicate determines every component, and its docstring gives the complete
projective-bundle argument. It is the only postponed theorem in this module.
There is no data chosen from bare existence of an arbitrary map or family.
There are no new nodes, dependency repairs, or changes to the natural statement.

Clause-by-clause correspondence:

- The fixed coefficient datum and positive finite level are carried by
  `P : PurityFiniteSetting.{u}`. `P.Coefficient` is the prescribed finite quotient
  (with its published size lift). `P.diagonalExponent` kills it at every positive
  level; no ramification divisibility assumption is added.
- `T : Scheme.{u}` and `a : T ⟶ Spec (.of P.field.k)` give the k-scheme;
  `[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]` mean separated and
  finite type. `F : T.Modules`, `r : ℕ`, and `[F.IsFiniteLocallyFreeOfRank r]`
  give the locally free module of constant nonnegative rank.
- `ordinaryFiniteCohomology P T i` is the Hom from
  `P.projectiveBundleUnit T` to `P.diagonalTwist T i` in the ordinary small
  pro-etale module derived category. The latter is already A(i)[2i]; there is
  no additional shift. The source is the constant coefficient in degree zero.
  This is the full-support derived-Hom presentation of the supported groups,
  rather than a new topology or a different cohomology theory.
- For positive rank, `D : ProjectiveBundleRealization T F` is the recorded
  quotient-convention relative Proj of the actual symmetric algebra, with its
  normalized degree-one twisting module. `hL : D.L.IsInvertible` is its
  established invertibility, not an additional hypothesis of the definition.
  The predicate quantifies over all such normalized presentations. Their
  existence is supplied by the recorded tautological-geometry dependency.
- `P.projectiveBundleChern a D hL` is precisely the étale representative of
  c_1(O(1)) used by the projective-bundle formula. Its image by the exact
  comparison functor is the recorded pro-etale Kummer class.
- `ordinaryFiniteCohomologyPullback` uses the actual inverse image and the
  canonical unit and root-normalized Tate comparisons from
  `projectiveBundlePositivePullback` and `kummerCoefficientPullback`.
- `ordinaryFiniteHyperplaneStep` tensors the pro-etale class with the image of
  that Kummer class, using the unit diagonal and the strong monoidal comparison
  of the existing derived tensor. `ordinaryFiniteHyperplaneProduct` repeats
  this step, with zero repetitions equal to the original class. These are the
  full-support cup products in the ordered shifted coordinates already used
  by `projectiveBundleCupPower`; no arbitrary multiplication or pairing is
  a parameter. The coefficient diagonal is the inverse unit multiplication,
  and the even shifts have the full-support cup convention of SupportedCup.
- `ordinaryFiniteProjectiveRelation` states
  sum over 1<=i<=r of (-1)^(i-1) q*c_i cup h^(r-i) = h^r.
  Its `Fin r` index is shifted by one. The cast is only
  `(i+1)+(r-(i+1))=r`. This is exactly the node's displayed relation and its
  inverse-coordinate definition: write j=r-i to obtain
  a_j=(-1)^(i+1)c_i, hence c_i=(-1)^(i+1)a_(r-i). The uniqueness theorem uses
  the specified projective-bundle isomorphism to ensure these are its inverse
  coordinates, rather than merely some solutions of an unproved relation.
- `IsOrdinaryFiniteChernClasses` explicitly imposes c_0=1, where the unit is
  `ordinaryFiniteCohomologyOne = 𝟙 _`, and c_i=0 for every i>r. Its last clause
  imposes the relation only if 0<r, on every normalized geometry and canonical
  transport. Those quantifiers are not vacuous: geometry is supplied by
  `exists_projectiveBundleTautologicalGeometry`, and the normalized root
  transport exists in the imported finite Kummer/projective-line interface.
- `ordinaryFiniteChernClasses` chooses the family from `∃!`, whose uniqueness
  is equality of the entire dependent function. `ordinaryFiniteChernClass`
  evaluates this family. No section, Euler class, or purity isomorphism is used.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its
  coefficient ring, unit, and constant coefficient conventions; the published
  `FixedFinitePositiveCoefficientTwist` presentation supplies
  `diagonalExponent`, `diagonalTwistEtale`, and `diagonalTwist`.
- `Sheaf.Paper.ProjectiveBundleFormula`: `projectiveBundleUnit`,
  `projectiveBundleChern`, `projectiveBundleCupPower`,
  `projectiveBundlePositivePullback`, `projectiveBundleUnitDiagonal`,
  `projectiveBundleMap` and `projectiveBundleFormula`. The last two are the
  source of the unique coefficient extraction described in the proof plan.
- `Sheaf.Paper.KummerAdditivity`: `AlgebraicGeometry.ProEtale.kummerFirstChern`,
  `kummerCoefficientPullback` and its comparison square; the global Kummer
  representative is the one already used by `projectiveBundleChern`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, specialized to `T.Modules`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`:
  `ProjectiveBundleRealization`, `ProjectiveBundleTautologicalGeometry`, and
  `exists_projectiveBundleTautologicalGeometry`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: the pro-etale derived supported
  sections convention; `Sheaf.Paper.SupportedCup`: `cupComposite` and
  `supportedCup`, whose full-support tensor formula is expressed above in
  the published ordered shifted Tate coordinates.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal`:
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`; its full
  current source was read with `scompile.py --source`. The existing
  `ProEtale.derivedTensor` and exact comparison are reused, not redefined.

Source checked: `literature/stacks-project/weil.tex`, proposition-chern-class
and equation-chern-classes (Tag 0FI5), especially the constant-rank reduction,
the unique defining relation, and the line-bundle case. Multiplying Stacks'
relation by (-1)^r and commuting the even classes gives exactly our equation.
The current natural node and its seven recorded dependency statements were
read in full. Their unchanged statements remain the contract.

Edge cases checked: r=0 forces the unique family (1,0,0,...) without selecting
any projective bundle; r=1 gives c_1=h after pullback along P(F)≅T, consistent
with Kummer c_1(F); r=2 gives h²=q*c_1 h-q*c_2 with the required sign. For a
split rank-two bundle this is (h-x_1)(h-x_2)=0. The empty scheme remains allowed:
its zero coefficient unit has identity equal to zero, so the c_0 convention is
consistent there. No field assumption is imposed on A. The cohomological
universe is the published ModuleCat.{u+1} on Scheme.{u}; none is auto-bound.

Searches repeated during repair: `msearch.py leanfinder` with “Chern classes of
a locally free sheaf as unique coefficients of the projective bundle relation”
returned eight hits on sheaf presentations and Proj extensionality, none a
Chern-class construction. `msearch.py loogle '"Chern"'` returned two unrelated
Lean matcherName declarations. `msearch.py grep 'Chern|chernClass|chern_class'`
returned twelve matcherName/Chernoff-bound hits, none relevant. The inherited
LeanSearch searches are also recorded on the node. `rg` for `chern|Chern` and
`grep -rn def-pur-chern-classes` in the upstream WeilConjectures tree found no
existing construction. Repository searches find the Kummer/projective-bundle
infrastructure but no ordinary Chern family. No duplicate notion was introduced.

## Second reading by NJ

Independent maintainer second reading, 2026-10-18, of immutable delivery
5a5d86a955143e95eff32a8f59e34f3b68c97004. This reader did not author or previously
second-read the delivery. This section replaces the delivered author self-check;
the Worker report above is preserved verbatim.

Read the item, all seven statement-dependency records, the entire delivered Lean
module, and the exact dependency declarations and their docstrings. Read Stacks
weil.tex, section-chern, proposition-chern-class and equation-chern-classes
(Tag 0FI5), including the preceding axioms; also read the blueprint ancestor's
Step 4 (L4). No natural statement correction or dependency-record repair is needed.

Clause-by-clause reading:

- Finite coefficients and positive level: PurityFiniteSetting bundles the actual
  finite-field and finite-extension datum and level_pos. Coefficient is the
  published ULift of O_E/(varpi^n). diagonalExponent is ell^n, annihilating A at
  every positive level. In particular no e|n assumption is introduced.
- The base and bundle: a : T -> Spec k with IsSeparated, LocallyOfFiniteType and
  QuasiCompact is precisely separated finite type; F : T.Modules with
  IsFiniteLocallyFreeOfRank r is the recorded open-cover definition. r is a
  natural number and includes zero. There is no smoothness or extra properness
  assumption on T.
- The groups: ordinaryFiniteCohomology is Hom(A_T,A_T(i)[2i]) in the actual
  small pro-etale module derived category. diagonalTwist already includes [2i].
  Full-support supported_cohomology_hom identifies these groups with the
  right-derived kernel-of-restriction groups. Comparison inverse image is used
  to present objects in this category, not to replace it with an etale Hom group.
- Geometry: ProjectiveBundleRealization contains the graded algebra identified
  with Sym F on affine opens, compatible restrictions, the actual relative Proj,
  and normalized degree-one twist/quotient charts. The tautological-geometry
  theorem supplies a realization and invertibility when r>0. Quantification
  over normalized realizations does not add an assumption to the class family.
- Hyperplane class: projectiveBundleChern is the recorded etale Kummer first
  Chern class of D.L; exact comparison gives the specified pro-etale class.
  No section, Euler class or purity isomorphism defines it.
- Pullback: ordinaryFiniteCohomologyPullback uses actual inverse image,
  kummerCoefficientPullback, and the unit and positive-power comparisons.
  OrdinaryFiniteTwistTransport fixes roots by inclusion in G_m and fixes line
  maps on pure tensors. The finite-twist pullback theorem supplies these
  normalized comparisons; this is not an arbitrary orientation parameter.
- Product: ordinaryFiniteHyperplaneStepRaw first applies the image of inverse
  unit multiplication, then the strong monoidal comparison, tensors alpha
  and the image of h, and applies the inverse comparison to the ordered next
  power. ComparisonMonoidal's exact declaration has the required direction.
  This is the full-support supported-cup construction in ordered shifted
  coordinates. The total-complex shift conventions agree here since all
  cohomological degrees are even. The recursion starts at alpha for exponent
  zero, so h^0=1 and every h power has the intended meaning.
- Relation: Fin r indexes i=1,...,r by i.val+1. Its scalar (-1)^i.val is
  (-1)^(i-1)=(-1)^(i+1); the equality is
  sum_i (-1)^(i-1) q*c_i cup h^(r-i)=h^r. The only cast uses
  (i+1)+(r-(i+1))=r. This is precisely the displayed node relation and, after
  reversing indices and multiplying by (-1)^r, the Stacks relation.
- Inverse coefficients: existsUniqueOrdinaryFiniteChernClasses states uniqueness
  of the entire dependent family satisfying that actual equation. The
  projective-bundle formula in degree 2r and twist r, via adjunction, finite
  sums and invertibility of Tate powers, determines its coefficients as
  c_i=(-1)^(i+1) a_(r-i). Its docstring explains this argument and transport
  between normalized presentations. It is a proof obligation intrinsic to
  this definition, not an independent unstated DAG prerequisite.
- Conventions: IsOrdinaryFiniteChernClasses imposes c_0=identity of the unit
  and c_i=0 for i>r. ordinaryFiniteChernClasses selects from this determining
  exists-unique theorem; ordinaryFiniteChernClass evaluates that family.
  This satisfies the permitted unique-characterization rule for definitions.

Edge cases: r=0 leaves only c_0=1 and all positive components zero and forms no
P(0). For r=1 the relation is q*c_1=h and P(F) is T with O(1)=F. For r=2 it is
h^2=q*c_1 h-q*c_2, agreeing with (h-x_1)(h-x_2) for a split bundle.
The empty scheme is permitted (its identity equals zero); n=1 and ramified
levels not divisible by e are permitted. No field assumption on A is used.
The declared universe u is arbitrary; Scheme.{u}, the small-site object and
morphism sizes, and ModuleCat.{u+1} agree with the published interfaces.
autoImplicit is false, with no unbound variable or silent universe equality.

Independent searches for Chern/characteristic-class terminology in Mathlib,
the slopmaster2 WeilConjectures tree and the group clone's lean/Sheaf find
Kummer first classes and projective-bundle infrastructure but no existing
ordinary higher Chern family. Read the inherited LeanSearch, LeanFinder,
Loogle and grep records and the worker's repeated-search report. No H4 duplicate
was found; helpers reuse the recorded objects and operations.

Maintainer gates: all eleven delivered declarations are recorded, the main
lean.statement is verbatim the file signature, every line is at most 100
characters, and source/blueprint docstrings are present. The only postponed
proof is the named exists-unique theorem with proof `by sorry` and a complete
source-based proof plan. All definitions contain real terms. No local theorem
proof, dropped route-pivot node, enhanced/dg/model-category machinery, or
pro-etale substitute is introduced. The route-pivot dropped list has no
intersection with the item's dependencies; there is no repair note for this
item at origin/newtargets-dag.

Validation: ran the prescribed wrapper on the immutable file:

    python3 /home/ubuntu/weil-launcher-nt/scompile.py NJ def-pur-chern-classes snapshot/lean/Sheaf/Paper/PurityChernClasses.lean

Exit 0, no diagnostics: isolated sandbox mode 8.6 seconds; library module mode
7.0 seconds. The installed wrapper performs the side-overlay compilation and
confirmation on the server; its output reports a private /dev/shm overlay.
No lake/global build, direct ssh command, live Lean write, project-clone edit,
or mutating Git command was performed. The immutable report and module were
also compared byte-for-byte with git show of the named delivery commit.

Finding and repair: the delivered section explicitly said it was an author
self-check rather than an independent reading (H11). Replace it by this actual
independent clause-by-clause reading and compiler evidence. No substantive
H3/H5 mismatch remains and no Lean or JSON replacement is necessary.
