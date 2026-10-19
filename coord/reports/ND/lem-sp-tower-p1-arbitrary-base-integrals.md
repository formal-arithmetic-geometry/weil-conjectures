## Worker report

The module `Sheaf.AlgebraicGeometry.ArbitraryBaseFiniteP1Integrals` states
`AlgebraicGeometry.Etale.exists_arbitraryBaseFiniteP1Integrals` with `sorry`.
It also constructs `AlgebraicGeometry.Etale.arbitraryBaseFiniteP1DiagonalTrace`, the
trace transported along the existing canonical projective-line chart. This helper
contains actual data: the chart adjunction unit, derived composition, congruence for
the chart's equation over its base, the normalized shifted-line pullback, and finally
`b.inv ≫ biprod.snd`. It makes no selection from an existence theorem.

The long conclusion is factored into same-node helpers to keep elaboration bounded:
`ArbitraryBaseFiniteP1ChernFamily` and `ArbitraryBaseFiniteP1SplittingFamily`
are the actual function types of c and b;
`ArbitraryBaseFiniteP1SplittingSpec` is exactly the Chern specification and
ordered component equation;
`ArbitraryBaseFiniteP1BaseChange` is exactly the two displayed base-change equations;
`ArbitraryBaseFiniteP1DiagonalIntegrals` is exactly the Cartier witness,
normalized supported class, canonical source isomorphisms and both integrals.
These predicates have explicit bodies, contain no sorry and are all listed in
lean.declarations. They package clauses of this node, not independent notions.

The target node is unchanged except for its Lean record. There are no new nodes,
no dependency repairs, no statement correction, and no disputed mathematical claim.
The withdrawn `Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals` contains no remaining
declarations; this delivery uses a new module and new declaration names.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The integer N ≥ 1 is `(N : ℕ) (hN : 0 < N)`. Using natural numbers loses no
  positive integer. The coefficient ring is `(A : Type (u + 1)) [CommRing A]
  [Finite A]`, and NA = 0 is `hA : (N : A) = 0`.
- The theorem provides one family on all `(S : Scheme.{u})` with
  `hS : IsUnit (N : Γ(S, ⊤))`. This is the source's family over every T over every
  such S: any T → S inherits invertibility by mapping hS along its map on global
  sections. Conversely every invertible-N scheme occurs by choosing S = T and
  its identity. Since every construction is intrinsic to T, quantifying the
  family before choosing a fixed S introduces no extra compatibility or choice.
  The base-change clause even permits any morphism between two such schemes,
  exactly what results by making T itself the base. No Noetherian or finite-type
  condition is imposed on any scheme.
- `DerivedCategoryModule A S`, through `ordinaryFiniteUnit`, `ordinaryFiniteLine`,
  `ordinaryFinitePullback`, and `ordinaryFinitePushforward`, is the ordinary
  unbounded derived category of module sheaves on S's small etale site. The
  functors are the recorded left-derived exact inverse image and total
  right-derived direct image. The derived tensor infrastructure is imported
  through the recorded ordinary finite projective-line arrows.
- `ProjectiveLine S` is the recorded projective space on `ULift (Fin 2)`, and
  `ProjectiveLine S ↘ S` is its projection. `ordinaryFiniteConstant A S` is the
  constant coefficient sheaf; `ordinaryFiniteUnit A S` places it in degree zero.
  `ordinaryFiniteLine A N hA S` places the recorded scalar-extended roots sheaf
  `Scheme.finiteEtaleTateLine S N A hA` in degree zero. Its actual scalar extension
  is the tensor product in the source, with the symmetric order fixed by its
  generator formula, not a replacement locally constant sheaf.
- The existential `t : OrdinaryFiniteTwistTransport A N hA` is normalized by its
  `roots_normalization` and `line_normalization` fields (inclusion into G_m and
  pure tensors). It is not an arbitrary system of identifications or an extra
  hypothesis. This reuses the statement dependency's exact canonical interface.
- The family c is the hyperplane Kummer arrow, characterized by
  `ordinaryFiniteP1ChernSpec ... (c S hS)`. That predicate compares its actual
  module-to-abelian cohomology realization with `ordinaryFiniteP1KummerClass`,
  which applies the Kummer boundary to `ProjectiveSpace.twist ... S 1` and then
  the scalar roots map. This is precisely the dependency's existing Chern
  specification, also used by the Noetherian splitting theorem.
- The adjunct h is `ordinaryFiniteP1ChernPushforward ... (c S hS)`. The first
  component is `ordinaryFiniteP1Unit ... t S hS`. The equation
  `(b S hS).hom = biprod.desc ... ...` fixes exactly those two components in
  the source's order. The family b has isomorphism type, asserting that this
  specified map is invertible, not merely that its endpoints are isomorphic.
- Every occurrence of the trace is explicitly `(b S hS).inv ≫ biprod.snd`.
  There is no independent trace variable or undetermined inverse.
- For every `(f : S' ⟶ S)`, the first base-change equation uses
  `ordinaryFiniteP1Exchange`, followed by the pushed-forward
  `ordinaryFiniteShiftedLinePullback` along `ProjectiveSpace.map ... f`. On
  the two summands it uses `ordinaryFiniteP1DecompositionSourceMap`. This is
  B_f f⁻¹b_S = b_S' σ_f, in Lean's left-to-right composition order.
  The second equation is exactly f⁻¹t_S = t_S' B_f after the canonical constant
  comparison `ordinaryFiniteUnitPullback`. Both source and target invertibility
  witnesses are explicit; no restriction on f occurs, including the identity.
- W is `pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)`. The source's
  effective Cartier diagonal is the conclusion
  `∃ hI : (pullback.diagonal ...).ker.IsInvertible`.
- The class κ is an Ext class from the actual closed direct image of the
  constant coefficient sheaf to `finiteEtaleTateLine W N A hA`, in degree 2.
  `SupportedKummerBoundary ... hI ... κ` fixes its relative Kummer boundary,
  including its divisor-section trivialization. By
  `ordinary_supported_kummer` and its unique-boundary clause, this is the
  canonical supported map with the positive convention δ u = c₁(O(Δ)); it
  cannot silently be replaced by its negative or by an arbitrary supported map.
  `supportedExactDerivedMap ... κ` realizes that class after the canonical
  exact closed-direct-image comparison, with source RΔ_* A_P.
- `a : Bool` ranges over both projections, using the dependency's
  `projectiveLineDiagonalProjection` and `projectiveLineDiagonalChart`.
  `projectiveLineDiagonalAlpha` is the recorded composite derived unit. Its
  additional `IsIso` clause renders the source's explicit isomorphism α_i.
  Its normalization is already the canonical composition identification for
  p_i Δ = identity, as explained in that declaration's docstring.
- The final equation is `alpha ≫ Rp.map delta ≫ transportedTrace = 𝟙 ...` for
  each Boolean a. The transported trace uses exactly b at ProjectiveLine S,
  not the Noetherian trace. Thus both diagonal integrals are included over
  arbitrary S with no hidden Noetherian instance.

Dependency declarations read and used (names below are in namespace
`AlgebraicGeometry` unless qualified otherwise):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its coefficient
  import: `Etale.DerivedCategoryModule` and the ordinary derived category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`,
  `ProjectiveLine`, `ProjectiveSpace.instIsProper`, and base-change charts.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback` (root and pure-tensor normalizations).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `ProjectiveSpace.twist` (the actual O(1) used by the Chern predicate).
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `Scheme.kummerSequence_shortExact`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `Etale.exactDerivedBaseChangeMap`, the exchange used by `ordinaryFiniteP1Exchange`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.diagonal`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`:
  `Etale.ordinary_supported_kummer`, `Etale.ordinary_supported_kummer_uniqueBoundary`;
  its public dependencies supply `SupportedKummerBoundary`,
  `supportedExactDerivedMap`, and `supportedDerivedUnit`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, imported for the
  composition-normalized proof plan; the actual constant-coefficient chart map
  uses `Etale.rightDerivedLowerStarComp` and `Etale.rightDerivedLowerStarCongr`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`:
  `Etale.ordinaryFiniteConstant`, `.ordinaryFiniteUnit`, `.ordinaryFiniteLine`,
  `.ordinaryFiniteP1KummerClass`, and `.ordinaryFiniteP1ChernSpec`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`:
  `Etale.OrdinaryFiniteTwistTransport`, `.ordinaryFiniteP1Unit`,
  `.ordinaryFiniteP1ChernPushforward`, `.ordinaryFiniteP1Exchange`,
  `.ordinaryFiniteShiftedLinePullback`, `.ordinaryFiniteUnitPullback`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data`:
  `Etale.ordinaryFiniteP1DecompositionSourceMap`; its Noetherian-only
  `OrdinaryFiniteP1BaseChange` is not reused as an arbitrary-base predicate.
- `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals`:
  `Etale.projectiveLineDiagonalProjection`, `.projectiveLineDiagonalChart`,
  `.projectiveLineDiagonalAlpha`; `.projectiveLine_diagonal_integrals` is only
  a proof dependency on the universal Noetherian base.

All stated proof dependencies are imported, directly or through these modules.
In particular the ordinary finite adjunction and trace, proper unbounded base
change, standard charts, Cartier line bundle, affine pullback of spectra, and
Mathlib's adjunction mate-pasting lemmas remain available to the future proof.
The seven-step DAG proof is copied in full into the theorem docstring, with
citations preserved.

Edge cases checked mathematically before writing:

- N = 1 forces 1_A = 0, so A is the zero ring. All displayed coefficient
  objects and endomorphisms are zero, and both integrals are identity on zero.
- The zero coefficient ring is permitted also for N > 1 (`Finite`, not
  `Nontrivial`, is required).
- The empty base and its empty projective line are permitted. No point,
  geometric-point choice, cover nonemptiness, or nonempty index is assumed.
- Identity base change is included, and arbitrary base maps are not assumed
  flat, finite type, separated, quasi-compact, or Noetherian.
- Non-Noetherian and non-quasi-compact bases are included. Invertibility in
  global sections is equivalent to local invertibility of the integer N.
- Schemes live in universe u and coefficient modules in u + 1, exactly as in
  the dependency interfaces. Every universe and variable is explicitly bound;
  `autoImplicit` is false.
- Both projection choices use the same supported class; the order of summands
  is always twist[2] first and constant sheaf second. Only an even shift occurs.

Searches actually run using `msearch.py` with this group and item:

- LeanFinder: `finite projective line Kummer decomposition and diagonal trace
  integrals over arbitrary base scheme`: eight hits, including proper-map and
  diagonal affine-cover lemmas; none is this finite etale splitting/integral.
- Loogle: `CategoryTheory.Limits.biprod.desc`: the binary biproduct constructor
  and its standard equations were found and reused; no projective-line result.
- Mathlib grep: `Kummer|diagonal.*trace|trace.*diagonal`, subdirectory
  `AlgebraicGeometry`: zero hits.
- LeanSearch: `projective line finite etale Kummer splitting trace diagonal
  arbitrary base`: eight linear-algebra field-trace hits, none this statement.
- `rg`/`grep` of `lean/WeilConjectures` for the item id and Kummer/diagonal/trace:
  Kummer sequences and curve-cohomology lemmas exist; no arbitrary-base finite
  P1 splitting and integral statement is present.
- `rg` of `lean/Sheaf` for the item id, `arbitraryBaseP1`,
  `arbitraryBaseFiniteP1`, and `diagonal_integrals`: only the Noetherian
  `projectiveLine_diagonal_integrals` is present. The old arbitrary-base module
  is an empty withdrawal stub. Its old declarations are not rebound.
- `rg` of `dag/nodes` and `dag/lean_names_upstream.json` for these names found
  no extant matching arbitrary-base declaration.

Validation: the factored interface compiled on the server through `scompile.py`
in 45.4 seconds (60-second limit, two threads, nice 19), with no warnings.
The earlier monolithic conclusion exceeded the limit and was replaced by the
explicit same-node predicates described above; no mathematical clause changed.
Temporary `#check` commands and profiling options have been removed. The final
file is checked again by the dry-run delivery wrapper, including preflight.
No global build or direct repository mutation is used.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
