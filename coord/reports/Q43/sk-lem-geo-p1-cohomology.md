## Worker report

The new module `Sheaf.AlgebraicGeometry.GeoP1Cohomology` states
`AlgebraicGeometry.ProEtale.geoP1Cohomology`, with its sole theorem proof `sorry`.
Its other declarations spell out the canonical objects and arrows of (G2), (G3)
and their base-change diagrams. No definition has postponed data or a new theorem
as a hidden proof. The source is the current main-20261015 blueprint unit,
sec-six-functors-basics/sk-lem-geo-p1-cohomology, and its nine-step DAG proof.
The stage-1 repair note is resolved; its instruction to retain the statement is
respected. No source statement correction or dependency repair is needed.

Hypothesis and conclusion correspondence:

- Prime ell: `(ℓ : ℕ) (hℓ : ℓ.Prime)`.
- Integer r at least one: `(r : ℕ) (_hr : 0 < r)`; this is the nonnegative-integer
  encoding of the stated positive integer. Set N = ell^r in every displayed term.
- Finite commutative Z/N-algebra: `(A : Type (u + 1)) [CommRing A] [Finite A]`
  and `hA : ((ℓ ^ r : ℕ) : A) = 0`. A ring killed by N has the unique canonical
  ZMod N algebra map, already used by the finite Tate construction. No flatness,
  reducedness or nonzero-ring condition is imposed.
- Noetherian base: `S : Scheme.{u}` and `[IsNoetherian S]`. The library class is
  locally Noetherian plus quasi-compact, equivalently a finite affine Noetherian
  cover. It allows empty schemes and does not require separatedness over a field.
- Ell invertible on S: `hS : IsUnit ((ℓ ^ r : ℕ) : Γ(S, ⊤))`. Since r > 0,
  invertibility of this power is equivalent to invertibility of ell. This is
  global invertibility of the integer, equivalently invertibility in every
  structure-sheaf stalk. There is no characteristic or ground-field binder.
- P^1_S and its projection: the existing `ProjectiveLine S` abbreviates
  `ProjectiveSpace (ULift.{u} (Fin 2)) S`, and the projection is
  `ProjectiveLine S ↘ S`. The lift only places the two coordinates in the
  scheme universe; it changes no scheme or coordinate index set.
- Ordinary small pro-etale coefficient category: every output is in
  `DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))`.
  These fixed-scalar module sheaves are the ordinary constant-ring-sheaf
  presentation, not condensed or completed coefficients.
- Constants: `geoP1Unit A S` is exact comparison of the existing etale constant
  sheaf in degree zero. The canonical comparison constant-sheaf identification
  identifies it with the constant pro-etale sheaf in degree zero.
- Finite signed twists and shifts: `geoP1Twist A N hA S a b` is exact comparison
  of `Etale.p1DecompositionTwist A N hA S a b`. This uses precisely
  `Scheme.finiteEtaleTateSheaf`: in degree one the scalar-extended roots of
  unity, and in degree minus one internal sheaf Hom into A. Exact comparison
  commutes with shifts. Thus the second summand is exactly Lambda(-1)[-2],
  without choosing a primitive root or imposing global constancy of the twist.
- Chern normalization: `geoP1EtaleChern` is the `chern` of the already recorded
  `Etale.projectiveLineTraceDatum`. Its `chern_spec` is the actual scalar
  Kummer boundary of `ProjectiveSpace.twist ... 1`, whose transitions are
  e_i=(x_i/x_j)e_j. The same arrow is used by both decomposition maps. This
  canonical selection is determined by its Kummer specification, not by an
  arbitrary existence of a map. The Cartier identification is the supplied
  `exists_geoCartierCycleClass` Chern equation, applied to the infinity divisor;
  its chart calculation and sign are retained in the main proof docstring.
- The map (G2): `geoP1DecompositionMap` is comparison of the existing
  `Etale.p1DecompositionMap`, with its two ordered summands compared by their
  injections, followed by `geoP1PushComparison`. The etale map is literally
  `biprod.desc` of the unit and the tensor-evaluation adjunct of this Chern class.
  The comparison is the adjoint of the pullback square followed by the image
  of the etale counit. Its mate normalization therefore identifies these with
  the pro-etale unit and the pulled-back Chern adjunct. The theorem asserts
  `IsIso` of this particular map for every S and hS.
- Base change of (G2): the first equation in the final conjunction says that
  `geoP1Pullback A g` of this map, followed by `geoP1UnitExchange A g`, equals
  `geoP1SourceMap ... g hS` followed by the same specified map for S'.
  `geoP1Exchange` is the existing `derivedBaseChangeMap` for the actual
  Cartesian projective-line square. The unit and roots-normalized twist
  comparisons in `geoP1SourceMap` are fully specified, not arbitrary maps.
- Twist of (G2): the existential family `b` has source Lambda(1)[2] plus Lambda
  and target Rp_*Lambda_P(1)[2]. Its `hom` is fixed to `geoP1TwistedMap`, which
  is comparison of the existing decomposition with shifted twisted unit and
  the same Chern adjunct. Tensoring the two specified components of (G2) by
  Lambda(1)[2], evaluating the dual line and using the projection formula gives
  exactly these two components, as explained in proof steps 5 and 8. This
  presentation avoids selecting any projection-formula isomorphism arbitrarily.
- The trace (G3): `geoP1Trace ... (b S hS)` is definitionally
  `(b S hS).inv ≫ biprod.snd`. Both the hom and inverse of b are determined,
  hence no arbitrary trace is introduced.
- Every Noetherian base change for trace: the second equation compares
  `g^*Tr` followed by `geoP1UnitPullback` with `geoP1TwistExchange` followed
  by `Tr` on S'. Both S and S' are arbitrary Noetherian schemes with the
  required integer invertible; g is unrestricted, including identity,
  nonflat, closed-immersion and empty-source maps. The family b is quantified
  before S,S',g, so the equation concerns the same traces at every base.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt` and its topology.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`,
  `ProEtale.derivedTensor`: the existing ordinary K-flat tensor. The twist
  calculation is implemented by the existing etale canonical tensor arrows.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`,
  `leftDerivedUpperStarIsoMapDerivedCategory`,
  `derivedUpperStarLowerStarAdjunction`, `derivedBaseChangeMap`: the closed
  upstream declarations for `sk-def-sfb-finite-derived-functors`, whose audit
  is closed even though its `lean` field is absent. No restatement is made.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`,
  `Scheme.finiteEtaleTateSheaf` and its pure root generators.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`,
  `siteComparisonDerivedPullbackPlus`; the helpers use exactly the same
  `comparisonUpperStar.mapDerivedCategory` before restricting to D+.
- `Sheaf.AlgebraicGeometry.GeoCartierCycleClass`,
  `exists_geoCartierCycleClass` and its Kummer Chern equation (proof input).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, `ProjectiveSpace`;
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, `ProjectiveSpace.twist`.
- Already landed nodes added to `stmt_deps`: `thm-amb-p1-decomposition`
  (`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition`,
  `Etale.p1DecompositionMap`, signed shifted twists and their normalized pulls);
  `def-amb-p1-trace` (`Sheaf.AlgebraicGeometry.ProjectiveLineTrace`,
  `Etale.projectiveLineTraceDatum`);
  `def-asd-ordinary-finite-p1-arrows`
  (`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`, the ordinary derived
  functors, unit pullback and twisted decomposition components); and
  `def-asd-ordinary-finite-p1-data`
  (`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data`, `OrdinaryFiniteP1Datum`).
  Each has a usable landed declaration. Traversing both dependency relations
  from each of these nodes finds no path to this item, so these added edges
  close no cycle. They introduce no new node or duplicate notion.

The module also imports all currently stated proof dependencies without `public`.
The main theorem's docstring preserves all nine proof steps and names their
inputs, including scalar-mate projection and coefficient-exchange mates.

Edge cases checked: r=1; finite nonflat coefficient algebras, zero coefficient
ring, disconnected and nonreduced bases, empty S, empty S', identity g, arbitrary
nonflat g, and locally constant but globally nonconstant roots of unity. The
integer shifts are -2 and +2 with the cohomological convention. The ordered
second summand of the twisted sum is the untwisted constant, fixing the trace
sign. Universes are explicit: schemes u, module coefficients and module carriers
u+1, small pro-etale objects u+1 and morphisms u. No equality of site object and
morphism universes or extra size hypothesis is introduced.

Searches:

- `msearch.py leanfinder`, query "projective line cohomology decomposition unit
  first Chern class Tate twist trace base change": eight unrelated group
  cohomology/Hilbert 90 hits; no match.
- `msearch.py loogle`, query "ProjectiveSpace, IsIso": no hits; unknown identifier
  ProjectiveSpace in the service's Mathlib index.
- `msearch.py leansearch`, query "projective line cohomology trace decomposition":
  eight Lie/algebra linear trace hits; no geometric statement.
- `msearch.py grep`, query `projective.*(cohomology|trace)|p1Decomposition` in
  Mathlib/AlgebraicGeometry: zero hits.
- `rg` of the upstream WeilConjectures tree for projective-line cohomology,
  decomposition, trace and this blueprint id: existing proper-base-change
  statements but no pro-etale (G2)/(G3) statement. Read the finite-coefficient
  derived functors with `scompile.py --source` where the local old source
  layout is stale.
- `rg` of lean/Sheaf for the same notions: the ordinary etale decomposition,
  Kummer class, adjunction datum and trace cited above; no corresponding
  pro-etale decomposition. The declarations were read in full and reused.
- `rg` of dag/lean_names_upstream.json for p1Decomposition or geoP1: no match.

Validation: the per-file `scompile.py` checks and the prescribed delivery dry run
are run before pushing. The expected sorry warning is the sole allowed warning.
There is no STATEMENT-DISPUTED flag: the source and node agree and the displayed
hypotheses suffice.

## Second reading by Q43

No independent second worker was started, as the dispatcher's direct-delivery
brief forbids subagents. The maintainer supplies the independent review. The
worker reread the node against the completed file: each coefficient and base
hypothesis, both summands and shifts, the fixed unit/Chern map, the unrestricted
Noetherian base-change square, the fixed twisted map and inverse-projection trace
have the counterparts listed above. In particular the two equations use the
canonical derived mate, and no arbitrary transport or chosen trace is assumed.
