## Worker report

This delivery states `AlgebraicGeometry.veryTame_quotient_logRegular` in
`Sheaf.AlgebraicGeometry.VeryTameQuotientLogRegular`. Its only theorem proof is `sorry`.
The original mathematical statement is unchanged. Two genuinely missing definitions
are supplied as new nodes; two already landed definition nodes are added to statement
dependencies. All writes are in the assigned sandbox, and every compile uses scompile.py.

Source read: ILO Exposé VI 1.1--1.4, 3.1--3.7, especially Theorem 3.2, Proposition
3.5(c) and its following paragraph, and the quotient-pair use in IX 2.4. The available
ILO text extract has the actual printed pp. 73--76. Generic freeness and integrality
are retained, even though the log regularity assertion alone needs less.

The correspondence with every hypothesis is as follows.

- The integral Noetherian scheme D is `(D Y : Scheme.{u}) [IsIntegral D]
  [IsNoetherian D]`. The ambient universe is arbitrary. The finite group is
  `(G : Type v) [Group G] [Finite G]`, with its independent arbitrary universe.
- The closed boundary E is represented by the closed complement of `U : D.Opens`.
  `hU : DenseRange U.ι` makes its open complement dense. `hlog` uses the exact
  recorded `IsDivisorialFineSaturatedLogRegularPair D U.toScheme U.ι hU`, including
  its small étale divisorial sections, strict-local stalks, fs charts, regular
  stratum and rank dimension formula. No alternate log-pair definition is introduced.
- `a : G →* Aut D` is the scheme action. `hpres` asserts preservation of U (hence
  equivalently of E) for every group element and ordinary point.
- `hfree` supplies a dense invariant open V and tests freeness on every geometric
  point over V: `t ≫ (a g).hom = t → g = 1`. This is geometric freeness and does
  not incorrectly require freeness on ordinary scheme points.
- `htame : IsVeryTameDivisorialAction U a` uses the geometric stabilizer subtype
  `{g : G // t ≫ (a g).hom = t}`. Its cardinal is invertible in Ω, exactly the
  prime-to-residue-characteristic condition. The canonical map on the strict local
  ring sends each divisorial germ to a unit times that germ, exactly triviality
  on the quotient by units. Its difference from the identity lies in the actual
  `divisorialNonunitIdeal`, exactly identity on the coordinate ring of the log
  stratum, hence on its scheme. The map is constructed from ring-colimit germs
  by rebasing pointed neighbourhoods. This is inverse pullback, which has precisely
  the same triviality conditions as pullback. It is never an arbitrary input map.
- `q : D ⟶ Y` and `hquot : IsAdmissibleFiniteSchemeQuotient a q` are precisely
  admissibility (each orbit lies in an affine open), finiteness, invariance,
  quotient topology, orbit fibres and the canonical invariant structure sheaf.
  This landed predicate states exactly the quotient assumptions of the item.

The correspondence with every conclusion is as follows.

- The existential `N : EtaleLogStructure Y` includes the sheaf and genuine log
  condition. `hY : IsLocallyNoetherian Y` supplies the size/local Noetherian datum
  needed by the existing `FineSaturatedLogScheme`; it is a conclusion, not a new
  assumption on the quotient.
- For every `W : Y.Etale`, a multiplicative equivalence `e` identifies its N-sections
  with `invariantDivisorialDirectImageSections U a q hquot.2.2.1 W`. These are
  exactly the fixed divisorial functions on `W ×[Y] D`. The displayed equality
  `(pullback.fst W.hom q).appTop (N.alpha.app (op W) s) = (e s).val`
  imposes the canonical structural map. Thus this is the actual invariant direct
  image `(q_* M_D)^G` with its structural map, not an arbitrary log structure.
  Restrictions are forced: the inclusions into functions are injective, and the
  canonical ring pullback is injective after étale base change of this scheme
  quotient, so these structural-compatible equivalences are natural and unique.
  Specifying them objectwise with this compatibility is equivalent to identifying
  the presheaves. No independent identification or arbitrary isomorphism is assumed.
- `hfs : N.IsFineSaturated` is the existing definition of étale-local fs charts,
  not finite generation of the stalk alone. `(FineSaturatedLogScheme.mk Y hY N hfs).
  IsLogRegular` gives regular strict-local stratum quotients and the actual
  characteristic rank dimension formula.
- `N.trivialityLocus = (q '' ((U : Set D)ᶜ))ᶜ` is exactly the specified
  `Y \ q(E)`, with E the complement of U.
- The final V, its dense open immersion, the equality of its underlying set with
  that same complement, and `IsDivisorialFineSaturatedLogRegularPair` state exactly
  that `(Y,q(E))` is a log regular pair. In particular q(E) is closed, and its
  complement is dense. The log structure in the pair predicate is its prescribed
  divisorial structure; both its identification with N and its fs/log-regular
  properties follow from the invariant sheaf construction and divisorial recovery.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`: nonempty
  and domains on nonempty opens, exactly integral scheme.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` and the affine-local
  scheme interface `IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`,
  `IsDivisorialFineSaturatedLogRegularPair`, `divisorialSections`,
  `divisorialStalk`, `divisorialNonunitIdeal`, `strictLocalRing`, `strictLocalGerm`.
  Full source and docstrings read, including the actual fs chart pushout and rank.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`:
  affine and finite on each affine-open section ring; also read `IsIntegralHom`
  in `Mathlib.AlgebraicGeometry.Morphisms.Integral`.
- Added already landed node `def-per-admissible-finite-scheme-quotient`, module
  `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`, declaration
  `AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient`: its full predicate is used.
- Added already landed node `def-trf-fs-log-blowup`, module
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`,
  `EtaleLogStructure.IsFineSaturated`, `EtaleLogStructure.trivialityLocus`,
  `FineSaturatedLogScheme` and `FineSaturatedLogScheme.IsLogRegular` are used.
- Available proof dependencies are imported privately:
  `Sheaf.TraceFormula.LogRegularDivisorialStructure` (`logRegular_divisorialStructure`),
  `WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp`
  (`ringKrullDim_eq_of_isIntegral`), and
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`Algebra.IsIntegral.of_finite`).
  The strict-local invariant, equivariant chart and local Kummer quotient children
  have no declaration yet; they are not statement prerequisites and introduce no
  import. Their five-step use is written in the main theorem docstring.

Edge cases checked:

- The trivial group gives identity stabilizer maps and all invariant sections.
- Empty boundary U = D yields the units log structure; very tameness then forces
  the geometric stabilizer action on the whole strict-local ring to be trivial.
  Identity quotient is included. No positive log-rank assumption occurs.
- Geometric stabilizers are never empty (identity belongs), so Nat.card is their
  actual finite positive order; no requirement that the whole group order be
  invertible has been added. In characteristic zero the tameness condition is
  automatic. Wild groups acting freely are not excluded.
- Empty étale test objects are allowed; their section monoids and equalizer
  intersection are well-defined. The original integral D is necessarily nonempty.
- A geometric generic point fixed as an ordinary topological point can still move
  as a geometric point. Both hfree and htame use the latter, correctly.
- Scalar multiplication on a boundary coordinate by a root of unity changes its
  log germ by a unit and is admitted; a nontrivial action along the stratum is
  excluded by the difference-in-ideal clause, not by a stronger pointwise criterion.
- All geometric test fields use Type u, the scheme's universe, and the finite
  group uses Type v. No universe equality or unrelated smaller test universe is imposed.

Searches made (the machine outputs are retained in searches.jsonl and copied into
new-node mathlib_searches):

- msearch LeanFinder: “A very tame finite group quotient of a fine saturated log
  regular scheme is log regular” gave eight ordinary smooth/étale/normalization
  declarations, none a log theorem. Earlier equivalent plain-word searches also
  gave ordinary scheme declarations.
- msearch LeanSearch: “Very tame action on log scheme and invariant direct image
  logarithmic structure” gave representation linearization, ordinary pushforward,
  proper actions and unrelated logarithms, no matching notion. “Invariant direct
  image of divisorial log structure under finite scheme quotient” gave ordinary
  finite morphisms and scheme quotient ideals, not the requested invariant monoids.
- msearch LeanFinder: “Very tame group action fixes characteristic monoid and
  strict local log stratum” returned fundamental domains/supports, no log actions.
- msearch Loogle for `"LogRegular", "VeryTame"`, `"LogRegular"`,
  `"IsVeryTameDivisorialAction"`, and `"invariantDivisorialDirectImageSections"`
  returned no hits.
- msearch grep in Mathlib AlgebraicGeometry for `LogRegular|VeryTame|very.?tame`
  and `divisorial|VeryTame|invariantDivisorial` returned no hits.
- rg over Mathlib, upstream WeilConjectures, the project's lean/Sheaf, and
  dag/lean_names_upstream.json for all seven new declaration names returned none.
  Broader log-regularity searches located the reused existing interfaces above.
  Upstream grep for this exact item id returned none.
- DAG search for very tame actions finds statements using the notion but no
  definition node. The admissible quotient definition is already present and is
  reused. `blueprint_refs.py search 'very tame'` and search 'invariant direct image'
  each returned zero blueprint nodes. Its ancestor command returned
  `lem-per-artin-gabber-affine-curve`, used in the new records.

No statement dispute, dependency-interface replacement, or statement correction.

## New nodes

`def-per-very-tame-divisorial-action` defines exactly the stabilizer-order,
characteristic and strict-local-stratum conditions of ILO VI 3.1, using the already
recorded divisorial stalk and nonunit ideal. Its helper definitions explicitly rebase
étale neighbourhoods, geometric lifts and their ring-colimit germs to construct the
canonical strict-local map. Searches above found no existing definition node or
Mathlib/upstream/project declaration of this notion. Its four declarations are in
`Sheaf.AlgebraicGeometry.VeryTameDivisorialAction`; no theorem is postponed there.

`def-per-invariant-divisorial-direct-image` defines the section monoids of
`(q_* M_D)^G` exactly as in the paragraph after ILO VI 3.5. It constructs the action
on `W ×[Y] D` with `pullback.lift` and intersects the divisorial section submonoid
with the equalizers of its prescribed pullback homomorphisms and the identity.
Its source is VI 3.5 and 3.7(b). Searches above found no existing node or declaration
for this fixed divisorial section construction. Its two declarations are in
`Sheaf.AlgebraicGeometry.InvariantDivisorialDirectImage`; no data is chosen from an
existence theorem, and no theorem is postponed there.

## Second reading by Q128

No second worker was started, as required by the dispatch brief. The maintainer's
independent review reads this delivery. I checked the final signatures again against
the node and the full dependency definitions, including geometric versus ordinary
stabilizers, the actual invariant direct image, étale-local fs charts, the exact
boundary image and geometric freeness. No mathematical statement change was needed.

Validation: all three modules compile separately through scompile.py, including their
library-named overlay compilations. No errors or warnings other than the permitted
sorry warning. The definitions contain actual data and only the main theorem has sorry.
