## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLogJacobianCriterion` states
`AlgebraicGeometry.EtaleLogHom.smooth_near_of_strict_logCotangent_injective`, with
`sorry` as its entire proof. It reintroduces the deleted criterion using the live
module-mode providers. Only the item's `lean` field changes. No new notions,
dependency repairs, or statement corrections are needed.

I read ILO, Exposé X, proof of Proposition 1.2, printed p.138 (the paragraph
beginning “This map is strict”), from the supplied PDF. It applies Kato 3.12 to
strict b′ between X and X′ log smooth over Y, with injective induced cotangent map,
and concludes smoothness at x. This is precisely the node's general criterion.

Hypothesis and clause correspondence:

- `S X Y : FineSaturatedLogScheme.{u}` supplies all three schemes, their locally
  Noetherian hypotheses, their actual étale log sheaves and their fs charts.
- `f : EtaleLogHom X S`, `g : EtaleLogHom Y S` are the two structure morphisms.
  `hf : f.IsLogSmooth` and `hg : g.IsLogSmooth` assert exactly their chart-based
  log smoothness, without asserting ordinary smoothness of either structure map.
- `h : EtaleLogHom X Y` is the comparison log morphism. `hover : h.CompEq g f`
  means `h.base ≫ g.base = f.base` AND compatibility on all relative étale log
  sections. Thus it says that h is an S-morphism of log schemes, rather than
  merely an S-morphism of underlying schemes.
- `hstrict : h.IsStrict` uses the recorded canonical characteristic-stalk
  isomorphism criterion for the source structure to be the pullback of the target.
  Its normalization by `CharacteristicRelation` prevents an arbitrary isomorphism.
- `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `t : Spec (.of Ω) ⟶ X.scheme` specify the arbitrary geometric point. Its image
  in Y is `t ≫ h.base`, as used inside the cotangent predicate. The underlying
  point of X is `(Scheme.SpecToEquivOfField Ω X.scheme t).1`.
- The node's description of logarithmic differentials is supplied by the existing
  `LogDifferential`, `logDifferentialRelations`, `logD` and `logDLog`. These use the
  free module on ordinary and log-stalk symbols modulo additivity, Leibniz,
  multiplicativity of dlog, compatibility with alpha, and both kinds of base
  relations. No new differential module is introduced.
- `hinj : IsLogCotangentInjective f g h t` is exactly injectivity of the canonical
  map specified by those ordinary and logarithmic symbols. `logCotangentResidue`
  is the quotient of the actual geometric local ring by the ideal of nonunits.
  `LogCotangentSource` is its balanced tensor product with the Y/S differential
  stalk, `LogCotangentTarget` is its tensor product with the X/S differential
  stalk, and `logCotangentGraph` prescribes the canonical comparison. Under
  `hover`, triviality of the graph kernel is precisely the map's injectivity.
- The conclusion `∃ U : X.scheme.Opens, point ∈ U ∧ Smooth (U.ι ≫ h.base)` says
  that the underlying h is smooth on an open neighborhood of the specified point.
  There is no extra conclusion about global smoothness or relative dimension.

Statement dependency declarations read and used (all modules imported publicly):

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogHom`, `EtaleLogHom.CompEq` (and the constituent log sheaves/charts).
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogSmooth` and its
  `FSLogChart.IsSmoothChart` definition.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalk`,
  `pointedEtaleStalkDiagram`, `pointedEtaleGerm`; these are used through the
  log/differential/cotangent definitions' actual stalks.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.LogDifferentialStalk`: `EtaleLogHom.LogDifferential`,
  `logDifferentialRelations`, `logD`, `logDLog`.
- `Sheaf.AlgebraicGeometry.FSStrictLogMorphism`: `EtaleLogHom.IsStrict` and
  `EtaleLogHom.CharacteristicRelation`. The recorded provider is used directly;
  the historical duplicate `StrictLogMorphismCharts` is not recreated.
- `Sheaf.AlgebraicGeometry.LogCotangentComparison`:
  `EtaleLogHom.IsLogCotangentInjective`, together with its residue, balanced
  tensor source, tensor target and prescribed graph.

The already-stated proof dependencies are imported privately:
`WeilConjectures.RingTheory.FiniteFreeMapResidueLocalizationStrong`
(`Module.finiteFreeMap_residue_localization_strong`),
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
(`LocallyOfFinitePresentation.finitePresentation_appLE`),
`Mathlib.RingTheory.FinitePresentation`
(`Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`), and
`Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource`
(`smooth_at_iff_of_etale`, `smooth_iff_of_jointly_surjective_etale`).
`lem-per-log-smooth-infinitesimal-calculus` and
`lem-per-etale-local-infinitesimal-lifts-smooth` have no live Lean record, so no
module can yet be imported for them; their mathematical uses are retained in the
five-step proof docstring. They are proof prerequisites, not notions needed to
state this item. No proof dependency or DAG proof text changes.

Edge cases checked before writing:

- Empty X admits no specified geometric point, so this pointwise statement makes
  no incorrect nonemptiness assumption. No nonemptiness instance is added for S/Y.
- Zero cotangent source is allowed: injectivity is then automatic, as it should
  be for this criterion. No positive rank, finite positive dimension, or basis
  choice occurs among the hypotheses.
- Nonzero and positive-characteristic residue fields are all covered; there is
  no extra characteristic restriction beyond the recorded log-smooth chart notion.
- Trivial log structures specialize to the ordinary relative differential
  criterion; strictness is kept, and never replaced by ordinary smoothness.
- The one universe u follows the recorded fs scheme and geometric stalk interfaces;
  all scheme-sized algebraically closed geometric fields are quantified. No
  independent smaller test universe, site-universe equality, or finiteness of Ω
  is assumed. Every variable and universe is explicitly bound.
- The conclusion uses the underlying image point of Spec Ω, not an arbitrary
  chosen point or a demand that all of Spec Ω factor through an unrelated open.

Searches (2026-10-24):

1. `msearch.py ... leanfinder "A strict morphism between log smooth fs log schemes
   is smooth near a point if the map on logarithmic cotangent spaces is injective"`:
   eight ordinary scheme smoothness hits (`IsSmooth`, `isSmooth_iff`, etc.), none
   about logarithmic cotangent injectivity. Returned signatures were read.
2. `msearch.py ... loogle '"LogSmooth", "IsStrict"'`: OK, zero hits.
3. `msearch.py ... grep 'logarithmic.*[Jj]acobian|LogSmooth|logCotangent'
   AlgebraicGeometry`: OK, zero Mathlib hits.
4. `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for the former theorem name, criterion name,
   `IsLogCotangentInjective`, and the item id: only the existing cotangent
   predicate is present; no live theorem states the criterion. The node records
   that its old module was removed, so the old binding cannot be existing:true.
5. The generic ordinary algebra Jacobian results found in the node's earlier
   search record do not involve fs log structures or this comparison. They do
   not state the item.

No mathematical statement fault or STATEMENT-DISPUTED issue was found. The
historical CompactObject example module is withdrawn; I also read its recorded
upstream replacement `WeilConjectures.CategoryTheory.CompactObject` for conventions.

## Second reading by Q25

A second pass by this worker reopened the node and the finished Lean file; this
is a self-check, not a claim of an independent agent review. The dispatcher
explicitly prohibits starting other agents; the maintainer supplies the independent
review of this delivery.

I checked every binder against the original statement: the three bundled fs
schemes include locally Noetherian; there are exactly two log-smooth structure
maps; CompEq supplies both scheme and log compatibility over S; strictness is
canonical, in the correct direction; t is an algebraically closed geometric point;
the induced Y-point and residue field are fixed by the existing canonical graph;
and its injectivity is the sole differential hypothesis. The final existential
open includes the geometric point's image and asserts ordinary Smooth for the
restricted h. The descriptions of differential relations match the imported
quotient, including the base-log relations. No statement correction or extra
hypothesis was needed. Each of the five original proof steps is retained in the
docstring, with all named dependencies and the sign of the correction `-δ ∘ r`.
