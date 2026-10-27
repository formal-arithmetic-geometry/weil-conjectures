## Worker report

The module `Sheaf.AlgebraicGeometry.GroupoidOpenUnitEtale` states
`AlgebraicGeometry.IsGroupoidScheme.etale_of_isOpenImmersion_unit`, with a single
`sorry` proof and no definitions. The node is unchanged except for `lean`.
There are no new nodes, dependency repairs, or statement corrections.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary base scheme is `{S : Scheme.{u}}`; the schemes over it are
  `{U R : Over S}`. Their structure maps are `U.hom` and `R.hom`.
- The source and target are `(s t : R ⟶ U)` in `Over S`, so their underlying
  scheme morphisms `s.left` and `t.left` commute with the base structure maps.
- Unit and inversion are `(e : U ⟶ R)` and `(i : R ⟶ R)` in `Over S`.
- Composition is `(c : pullback s.left t.left ⟶ R.left)`, with the exact
  source/target order of the node and its recorded groupoid predicate.
- The groupoid axioms are
  `_hG : IsGroupoidScheme s.left t.left e.left i.left c`. This is the recorded
  `def-a1-groupoid-scheme` predicate, including all test schemes and associativity.
  Although that predicate is absolute, these are groupoids over S: the Over
  morphisms supply all the base compatibilities except for composition, whose
  base compatibility follows from `_hG.composition_source` and `s.w`.
  Explicitly, `c ≫ R.hom = c ≫ s.left ≫ U.hom =
  pullback.snd s.left t.left ≫ s.left ≫ U.hom`, the pullback's structure map to S.
  Thus no missing relative structure is replaced by an arbitrary map or an extra
  hypothesis. Conversely every groupoid scheme over S supplies these data.
- Flatness of each projection is `[Flat s.left]` and `[Flat t.left]`.
- Local finite presentation of each projection is
  `[LocallyOfFinitePresentation s.left]` and
  `[LocallyOfFinitePresentation t.left]`.
- The open unit hypothesis is `[IsOpenImmersion e.left]`.
- Both conclusions are retained separately in `Etale s.left ∧ Etale t.left`.
- No Noetherian, reducedness, field, separatedness or nonemptiness predicate occurs.
  The only universe is explicitly declared `u`; all schemes use `Scheme.{u}` and
  all variables are bound, with `autoImplicit false`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.GroupoidScheme`:
  `AlgebraicGeometry.IsGroupoidScheme`, including its complete structure and docstring.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, and its
  `Flat.iff_flat_stalkMap`, matching the node's stalkwise definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, its affine-local definition,
  and the instance giving `LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` and
  `Etale.iff_flat_and_formallyUnramified`; the former is the recorded declaration,
  rather than the deprecated alias `IsEtale` returned by search services.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  its `isOpenImmersion_stableUnderBaseChange` is the Mathlib leaf for the proof.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and `pullback.lift`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, for the proof dependency.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`:
  `AlgebraicGeometry.IsUnramified`, the conjunction of locally finite type with
  an open-immersion diagonal, for the proof dependency.

The statement dependencies have public imports. The proof-only dependencies have
ordinary imports; the base-change leaf shares the already public open-immersion
module. `lem-a1-map-over-base-finite-presentation` has no recorded declaration or
Mathlib match, and searching its id/name in the Lean sources found no module to
import. It is not needed to type this statement; it remains cited in the complete
five-step proof docstring. Its special case here is also the existing Mathlib
instance from local finite presentation to local finite type, whose source was read.

Sources read: `more-groupoids.tex`, Tag 04R9, the full differentials lemma and
proof diagram; `stacks-morphisms.tex`, Tag 06N0, its final open-unit argument;
and the current latest blueprint's direct-images proof (3), whose supporting
alteration/plurinodal prerequisite chain the node records. The module docstring
and theorem docstring identify the source, and the latter carries all five DAG
proof steps, including the arbitrary-test-scheme verification of the cartesian square.

Edge cases checked mathematically before writing: empty U and R are permitted
(the groupoid maps force R empty if U is empty); the identity groupoid gives
identity projections; a one-object group scheme with open unit is covered;
nonreduced bases, all characteristics, and nonseparated schemes are unrestricted.
Flatness and local finite presentation are relative to the projections, not to S.
There is no quasi-compactness or global finite-presentation hypothesis.
No statement dispute or node fault was found.

Searches actually run:

- `msearch.py leanfinder`: "flat locally of finite presentation groupoid scheme
  open unit etale source target". Eight hits: universally open flat-lfp maps,
  general etale definitions/sites and smoothness; none states this groupoid result.
- `msearch.py leansearch`: "An internal groupoid scheme with flat locally
  finitely presented source and target and open identity section has etale
  source and target". Eight general etale/open-immersion facts; no matching theorem.
- `msearch.py loogle`: "IsGroupoidScheme, Flat, LocallyOfFinitePresentation,
  IsOpenImmersion, Etale". Zero hits, with unknown identifier `IsGroupoidScheme`;
  this is an unavailable project identifier in that service, not evidence of absence.
- `msearch.py loogle`: "AlgebraicGeometry.Flat, AlgebraicGeometry.Etale".
  Three hits: `Etale.of_formallyUnramified_of_flat`,
  `Etale.iff_flat_and_formallyUnramified`, and flat descent for etaleness.
  None includes the internal-groupoid open-unit argument.
- `msearch.py grep`: `GroupoidScheme|groupoid.*etale` in `Mathlib/AlgebraicGeometry`,
  and `GroupoidScheme|groupoid.*[Ee]tale|[Ee]tale.*groupoid` in `AlgebraicGeometry`.
  Both returned zero hits.
- `rg` in project `WeilConjectures/`, `Sheaf/`, and `dag/lean_names_upstream.json`
  for `GroupoidScheme`, groupoid/etale phrases, and this node id. The existing
  groupoid predicate and other groupoid theorems occur, but no theorem for this
  statement. The upstream node-id search returned no hit. Read the nearby
  relative-groupoid signature in `FppfGroupoidRestrictionQuotient.lean` to check
  the established use of `Over S` with the absolute groupoid predicate.

Validation: the prescribed `scompile.py` server compile is used for this module;
delivery preflight and its per-file compile are run by `deliver2.py`.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
