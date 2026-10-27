## Worker report

The delivery states `AlgebraicGeometry.smooth_trait_local_rational_spreading` in
`Sheaf.AlgebraicGeometry.SmoothTraitLocalRationalSpreading`, with its whole proof `sorry`.
It also supplies the missing fibrewise rational-map definitions in
`Sheaf.AlgebraicGeometry.FiberwiseRationalMap`. No statement correction or dependency
replacement was needed. No STATEMENT-DISPUTED finding remains.

Hypothesis and clause correspondence:

- The ring is `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`;
  the base is exactly `Spec (.of R)`. The generic point is explicitly
  `(⊥ : PrimeSpectrum R)` and the special point is `IsLocalRing.closedPoint R`.
  `Scheme.Hom.fiber` is the pullback along the canonical residue-field point.
  The residue field at the zero prime of a domain is canonically its fraction field,
  and the residue field at the closed point is canonically R/m. This uses the
  point-fibre convention expressly allowed by the node's base-change dependency,
  without replacing the scheme-theoretic fibres by set-theoretic fibres.
- `z : Z ⟶ Spec (.of R)`, `v : V ⟶ Z`, and `w : W ⟶ Z` are exactly the three
  supplied structure maps. Each has `Smooth`, `LocallyOfFiniteType`, `QuasiCompact`.
  The latter two classes together mean finite type, following the recorded dependency.
  Only `w` has `IsSeparated`; no separatedness of V or Z is imposed.
- `h` is the map between the generic fibres. `hh` states compatibility with their
  projections to Z. Since the maps are already between the two fibres over the
  fixed generic point, this is exactly being over Z_E: maps to Spec κ(eta) are unique.
- Fibrewise density is `f.IsFiberwiseDense U`, literally
  `∀ s : S, Dense (f.fiberι s ⁻¹' (U : Set X))`. It covers both points of the trait
  and is also defined for arbitrary bases. `FiberwisePartialMap` records the dense
  open domain, actual scheme morphism, and base compatibility. `Equiv` records
  equality on a fibrewise dense open contained in both domains. `FiberwiseRationalMap`
  is `Quot` by that relation. The relation is already an equivalence relation:
  reflexivity uses the domain, symmetry the same common open, and transitivity the
  intersection of two common dense opens, fibre by fibre. Thus the generated relation
  of `Quot` gives exactly the specified equivalence classes. No postponed equivalence
  proof or opaque data enters this construction.
- `FiberwisePartialIso` consists of two fibrewise dense opens and a real scheme
  isomorphism over the base. `toPartialMap` is its actual composite with the target
  inclusion. `FiberwiseRationalMap.IsBirational` means a representative of this form.
- The first conjunct quantifies over `ξ : z.fiber (IsLocalRing.closedPoint R)` in
  `genericPoints _`. Its local ring is exactly
  `Z.presheaf.stalk (z.fiberι (IsLocalRing.closedPoint R) ξ)`. It concludes both
  `IsDomain` and `IsDiscreteValuationRing`, rather than silently assuming this assertion.
- `stalkBaseChange v x` is the canonical projection from
  `pullback v (Z.fromSpecStalk x)` to `Spec (Z.presheaf.stalk x)`. This is V_A,
  not an arbitrary local test scheme or an abstract replacement for its stalk.
- `SmoothTraitLocalExtension ... false` supplies a fibrewise dense open and an
  actual Spec A-morphism to W_A. Its first condition contains every point mapping
  away from A's closed point. By the first conjunct A is a DVR, so that complement
  is precisely Spec Frac A; this is the entire local generic fibre. Fibrewise density
  includes density of the local special fibre. `AgreesOnPullback` compares its map
  and h on the canonical common domain over V. That common domain is V_L because
  the former contains the entire local generic fibre. Equality after composing
  into W is equivalent to equality into W_L by the monomorphism of its base-change
  inclusion. No embedding L into a separately selected field is assumed.
- The second conjunct assumes that condition for every special-fibre component
  generic point and concludes a `FiberwisePartialMap (v ≫ z) (w ≫ z)`.
  `Set.range ((v ≫ z).fiberι ...) ⊆ d.domain` contains the ENTIRE V_E;
  `d.hom ≫ w = d.domain.ι ≫ v` asserts the stronger structure compatibility
  required by the node, namely over Z. The final agreement on the common pullback
  says the restriction is exactly the given h_E.
- The third conjunct assumes `IsIso h` and the same local condition with `true`.
  For `true` the last condition requires an actual `FiberwisePartialIso` whose
  underlying partial map is the supplied local extension. It concludes a global
  `FiberwisePartialIso`, containing V_E, over Z, and agreeing with h_E.
  The isomorphism of base-dense opens is exactly a representative of the claimed
  T-birational map. No quotient existence alone replaces the specified representative.
- The fourth conjunct quantifies over EVERY `B : V.Opens` and EVERY pair of actual
  `B.toScheme ⟶ W` maps over Z. Equality of their composites with the canonical
  generic-fibre inclusion `(B.ι ≫ v ≫ z).fiberι ...` implies equality of the maps.
  Applying this assertion to an intersection is exactly the stated overlap consequence.
- The last conjunct quantifies over another arbitrary DVR R' and an arbitrary
  scheme morphism `b : Spec (.of R') ⟶ Spec (.of R)` with the two exact point-image
  equalities. Its first conclusion quantifies over arbitrary X, f, U, with only
  `f.IsFiberwiseDense U` assumed: the base-changed open is literally
  `pullback.fst f b ⁻¹ᵁ U`, with structure map `pullback.snd f b`.
  Its second conclusion takes EVERY isomorphism of base-dense opens e and gives
  one with exactly these two pulled-back opens, agreeing with the original map on
  their canonical pullback. Thus this really is the base change of e, not merely
  existence of some unrelated birational map. Both inverse maps are already part
  of the scheme isomorphism. This gives the birational base-change consequence.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (including the locally affine condition and locally ringed-space maps).
- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing`, with explicit `IsDomain`; its nonzero maximal ideal
  excludes fields.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`;
  its module/docstring fixes `Limits.pullback`, the two projections and the
  `Scheme.Hom.fiber` convention. The module is imported publicly. No module-sheaf
  construction is used as a substitute for scheme base change.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `IsClosedImmersion`, used through `IsSeparated`'s closed diagonal in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- New dependency `def-sfb-fibrewise-rational-map`: all seven listed declarations in
  `Sheaf.AlgebraicGeometry.FiberwiseRationalMap`.

Recorded proof-dependency modules are imported without `public`, including affine
nonzerodivisor density, fibre-stalk quotients, principal-prime DVRs, finite-presentation
arrow descent, fibre products of limits, Spec-stalk neighbourhood limits, eventual
map equality, schematic-density separated equality, smooth-fibre criterion, and
geometric reducedness. Mathlib modules of the recorded leaves are also imported.
`lem-trf-smooth-reduced-dense-pullback` has no Lean declaration or Mathlib match;
its import is absent, as it is only a proof prerequisite, not an object used in
the statement. Its use is retained in the complete fifteen-step proof docstring.

Source checks: read the primary BLR scan, §2.5 printed pp.55–58, §4.3 Proposition 5
printed pp.107–108, and §4.4 Corollary 4 printed pp.110–111, at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf .
The local-ring spreading assembly is the node's explicit fifteen-step argument,
not a claim that BLR §2.5 Proposition 5 by itself states the entire result.

Edge cases checked before and after drafting:

- Z, V, or the special fibre can be empty; the local hypotheses and local-ring
  assertion then quantify over the empty set, and the generic-fibre piece supplies
  the appropriate open. A dense open of an empty fibre has the ordinary vacuous
  density property. No Nonempty assumption is introduced.
- Disconnected V, W, Z and several components of Z_k remain covered by `genericPoints`;
  there is no irreducibility hypothesis or chosen unique generic point.
- The open B in uniqueness may be empty. It need not itself be fibrewise dense.
- V is allowed to be nonseparated; the birational proof glues inverses over the
  chosen component neighbourhoods as in Steps 10–13 of the node.
- The identity generic map and identity trait base change are included. Ramified
  and inseparable residue-field extensions are included, as are arbitrary scheme
  maps b satisfying the two point-image conditions.
- The final density assertion permits nonreduced, nonflat, infinite-type X, as
  well as empty fibres. R and R' are not required to be complete or henselian.
- One universe u suffices after enlarging all data to a common universe. There is
  no independently smaller test-algebra universe and no hidden auto-implicit binder.

Searches performed (real tool results are in searches.jsonl):

- LeanFinder: “A morphism on the generic fibre of smooth schemes over a discrete
  valuation ring spreads from local rings at generic points of the special fibre
  to a fibrewise dense open”: 8 results, general valuative criteria/flatness only.
- Loogle: `AlgebraicGeometry.Smooth, IsDiscreteValuationRing`: 0 results.
- msearch grep: `Dense.*[Ff]ib|[Ff]ib.*Dense|[tT]rait|[sS]preading`, AlgebraicGeometry:
  spreading-out and ordinary rational maps, no exact statement.
- LeanSearch: “Open subsets dense in every fibre and rational maps over a base scheme”:
  8 results, ordinary `Scheme.RationalMap`, `PartialMap`, dense-domain restrictions.
- LeanFinder: “Relative rational maps are classes of morphisms on open subsets dense
  in every scheme theoretic fibre”: 8 results, ordinary rational maps only.
- Loogle: `AlgebraicGeometry.Scheme.RationalMap`: ordinary rational-map API;
  inspected its actual definition and `IsOver`. Neither requires fibrewise density.
- msearch grep: `FiberwiseRational|FiberwisePartial|IsFiberwiseDense|[fF]ib[er]*wise.*[rR]ational`,
  AlgebraicGeometry: 0 matches.
- rg of WeilConjectures and Sheaf for fibrewise density and relative rational-map names:
  density occurs inline in GenericOpenFibreDensity and GoodCurvesFibreDensity,
  but there is no named relative rational-map construction. rg of the exact item
  id in WeilConjectures: no matches.
- DAG grep for base-dense/T-dense and relative rational maps found several statement
  nodes with inline explanatory conventions, none with a definition node or usable
  Lean interface. `blueprint_refs.py search fibrewise rational` found an unrelated
  Picard-degree statement; `search rational maps` found no definition of this notion.
  `blueprint_refs.py ancestor` returns null, matching the item's existing ancestry.

Validation: each of the two modules compiled separately, in dependency order,
with scompile.py against the published live server build. The definition module
has no sorry. The sole postponed proof is the named main theorem, with all fifteen
natural-language proof steps in its docstring. Initial elaboration failures from
untyped `⊥` were fixed by giving `PrimeSpectrum R` explicitly throughout.

## New nodes

`def-sfb-fibrewise-rational-map` defines fibrewise dense opens, relative partial
maps, their common-dense-open relation and quotient, partial isomorphisms, the
underlying partial map, and the birational predicate. Its source is BLR §2.5,
printed pp.55–56, and the representative-isomorphism convention used in §4.3.
The three kinds of recorded Mathlib searches and project/DAG searches above
establish that this is not the ordinary rational-map notion and has no existing
node/declaration interface. It has its own module and real data throughout.
The item cites it in stmt_deps. All original node fields are preserved except
lean and this added stmt_dep.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
