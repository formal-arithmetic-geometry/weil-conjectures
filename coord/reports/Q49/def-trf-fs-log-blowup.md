## Worker report

The item defines general fine saturated log schemes, log regularity, log ideals,
saturated log blowups by their universal property, and finite towers. The module is
`Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`; its principal declaration is
`AlgebraicGeometry.IsSaturatedLogBlowup`. All constructions have actual data.
There are no postponed theorems and no `sorry` terms. The item statement is unchanged.

Source read: ILO, Exposé VI 1.1--1.4, printed pp. 69--70, and Exposé VIII
3.3.7--3.3.10, printed pp. 107--108, from the repository PDF. In particular VI 1.1
stipulates locally Noetherian underlying schemes and the étale topology; VIII 3.3.8
means local principality of the log ideal, and 3.3.9 takes saturation in the fs
category. The blueprint source of the geometric-stalk dependency was also read.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The underlying scheme is `FineSaturatedLogScheme.scheme : Scheme.{u}` and the
  locally Noetherian condition is the field `locallyNoetherian : IsLocallyNoetherian
  scheme`. No separatedness, quasi-compactness, field, characteristic, regularity,
  or integrality of the underlying scheme is added.
- The small étale site is `X.smallEtaleTopology` on `X.Etale`. A log structure's
  `monoidSheaf` is an actual `Sheaf ... CommMonCat.{u}`. Thus its sections are
  commutative monoids, its restrictions are monoid homomorphisms, and its underlying
  sets satisfy descent. `EtalePrelogStructure.alpha` is a natural transformation
  into `X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat`, so the target
  is the multiplicative monoid of the actual étale structure sheaf.
- The log unit condition is `EtaleLogStructure.reflectsUnits` together with
  `unitsBijective`, at every geometric point. A monoid map restricts to an
  isomorphism on the inverse image of ring units exactly when it reflects units
  and induces a bijection of unit groups. Filtered colimits commute with units,
  and geometric stalks detect sheaf isomorphisms, so this is the stated sheaf log
  condition, including noninjective structural maps. `unitsIn` is the inverse of
  that uniquely determined unit isomorphism, composed with the unit inclusion.
- A geometric point is explicitly `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ X)`. `strictLocalRing X t`, reused from the divisorial-pair
  dependency, is the ring-valued point fibre of the étale structure presheaf.
  The repaired dependency's `pointedEtaleStalk` and `pointedEtaleGerm` give the
  monoid stalk and germ. `stalkAlpha` is the induced map from the cocone whose
  components are `alpha` followed by `strictLocalGerm`; it is not a chosen map.
- For a chart map `β`, `IsStalkChart` says `β.coprod (M.unitsIn t)` is surjective
  and its kernel congruence is `divisorialChartCongruence` of the ring-valued
  composite, restricted to its monoid range. The range restriction changes no
  relation: the existing congruence identifies `(q,1)` with `(1,u)` precisely
  when the structural image of `q` equals the ring unit `u`. Congruence closure
  consequently identifies `(pq,v)` with `(p,β(q)v)` and nothing more. Surjectivity
  and equality of this kernel say exactly that the induced map from the actual
  quotient pushout is an isomorphism. `IsChart W β` imposes this at all geometric
  points of the neighbourhood, not only the point used to choose it.
- `IsFineSaturatedMonoid` is reused without alteration. Its actual
  `Algebra.GrothendieckGroup` is the canonical group completion; its three
  conjuncts are finite generation, injectivity of the canonical map, and
  saturation for every positive natural exponent. Multiplicative notation
  `g ^ n` is the node's additive `ng`. `IsFineSaturated` asks for such a chart
  on a pointed étale neighbourhood of every geometric point.
- `characteristic` is `Associates` of the log stalk, i.e. quotient by the unit
  action, which `unitsIn` identifies with the ring-unit action. A trivial
  characteristic monoid is `Subsingleton`; `trivialityLocus` is the set of
  underlying points where it is trivial at every geometric point lying above.
- `nonunitIdeal` is `Ideal.span` of exactly the images under `stalkAlpha` of the
  nonunits of the log stalk. `IsLogRegular` requires `IsRegularRing` of the
  quotient and the equality of `ringKrullDim` of the strict local ring with
  the quotient's dimension plus `characteristicRank`, at every geometric point.
  The rank is `Module.rank ℚ (TensorProduct ℤ ℚ (Additive
  (Algebra.GrothendieckGroup ...)))`, converted to `ℕ∞` and then `WithBot ℕ∞`.
  This retains infinite dimension and the zero-ring convention. It matches the
  divisorial pair dependency's rank and regular-ring interfaces.
- `EtaleLogHom.base` is the scheme map. For every étale `W → X`, étale `V → Y`,
  and `k : V → W` over that base, `sectionMap` gives `M(W) →* N(V)`.
  `naturality` imposes every commuting square in both test objects, and
  `compatibility` is the square with pullback of regular functions. This is
  exactly the relative-test-object presentation of `f⁻¹ M → N`: restrict first
  to `V = W ×_X Y` to recover the adjoint map `M → f_*N`; all other components
  are its restrictions by the unique map to that pullback. Conversely any log
  sheaf morphism gives these components and squares. No arbitrary stalk maps
  or additional étale hypothesis on the base morphism are substituted.
- `IdealFamily` records subsets of sections. `IsIdeal` requires absorption under
  multiplication, restriction stability, and geometric-local membership. The
  last clause is exactly the missing subsheaf condition on a subpresheaf of a
  sheaf. `idealStalk` consists of the actual germs of its sections.
- `IsNonemptyCoherentIdeal` requires `IsIdeal` and, locally at every point, a
  chart and a finite set `E` with `E.Nonempty`; at every stalk in that chart
  the ideal consists exactly of chart images of members of `E` times arbitrary
  log elements. This expresses sheaf generation, rather than incorrectly
  demanding global sectionwise generation. Whole-monoid ideals are allowed.
- `pulledIdealStalk` is the log ideal generated by the images of all source
  ideal sections on relative pointed neighbourhoods. `pullbackIdeal` consists
  of sections whose every germ is in that generated ideal. This is sheaf-local
  ideal generation of the image in `N`, not multiplication by a ring ideal.
- `IsInvertibleIdeal` requires an ideal which, on a pointed étale neighbourhood
  of every point, is generated by one section at every stalk in that
  neighbourhood. This is étale-local principality; it imposes no nonvanishing
  condition on the section's image in the structure ring.
- `IsSaturatedLogBlowup b I` requires the coherent nonempty center, invertibility
  of `b.pullbackIdeal I`, and for every fs `Y` and every log morphism `f` with
  invertible pullback, `∃! h : EtaleLogHom Y X', h.CompEq b f`. `CompEq` requires
  equality of base composites and equality of section-map composites on all
  relative étale triangles. Every test triangle factors through the pullback
  of its target to the intermediate scheme, so this is exactly equality of
  log morphisms with the composite. Uniqueness concerns the full log morphism,
  not only its underlying scheme map. No blowup is chosen and no existence
  theorem is presumed in the definition.
- `SaturatedLogBlowupTower` has `length : ℕ`, levels `Fin (length + 1)`, arrows
  from level `i.succ` to `i.castSucc`, one center per `i : Fin length`, and
  `isBlowup` for each. For length zero there is one base and no arrows/centers.

Dependencies used, after reading their full recorded source signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and `Mathlib.AlgebraicGeometry.ResidueField`:
  `IsAlgClosed` and `Scheme.SpecToEquivOfField`.
- `Mathlib.CategoryTheory.Sites.Point.Basic` and
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Point.sheafFiber`, its defining
  `presheafFiber` diagram, `Scheme.pointSmallEtale`, and the canonical germs.
  The restricted assumption in the existing fibre API needs the repair below.
- `Sheaf.AlgebraicGeometry.LogRegularPair`: `strictLocalRing`, `strictLocalGerm`,
  `IsFineSaturatedMonoid`, `divisorialChartCongruence`. The divisorial-specific
  predicate is not used for general log structures, as its structural map is
  an inclusion whereas a general log structure need not embed in the ring.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularRing` (and the read
  `IsRegularLocalRing` definition); `Mathlib.RingTheory.KrullDimension.Basic`:
  `ringKrullDim`. These are transitively publicly imported by `LogRegularPair`.
- The repaired dependency module below supplies `pointedEtaleStalk` and
  `pointedEtaleGerm`; its explicit monoid-colimit instance uses Mathlib's
  `CommMonCat.FilteredColimits.colimitCoconeIsColimit` on a small filtered final
  model. Its universes do not force coefficient and site universes equal.

Edge cases checked mathematically: the empty scheme (all stalk-local conditions
are vacuous and the sheaf condition controls empty-object sections); the trivial
log structure (characteristic rank zero and nonunit ideal zero); a noninjective
structural map, including chart elements with zero ring image; the whole log
ideal (generated by the identity); exclusion of an empty ideal on a nonempty
scheme by `E.Nonempty`; a single principal ideal without a nonzero ring-image
assumption; arbitrary-length finite towers including zero; arbitrary relative
scheme maps in the universal property; and characteristic-free ring dimensions.
A fs chart can be taken in `Type u`: finite generation bounds its monoid size,
and its log stalks are generated by that monoid and the strict-local units.
The étale category remains object universe `u+1`, morphism universe `u`; the
small-final-model construction shrinks the indexing category, not those universes.

Searches made with `msearch.py Q49 def-trf-fs-log-blowup`:

- `leanfinder`: “Fine saturated log schemes, log regularity and the universal
  saturated logarithmic blowup of a coherent log ideal”. Eight hits concern
  normalization, ordinary smoothness/étaleness, ordinary scheme ideals and
  projective spectra. None defines the logarithmic notions here.
- `loogle`: `"LogStructure"`. Zero hits.
- `grep`: `LogStructure|LogScheme|logBlow|FineSaturated`. Zero Mathlib hits.
- `leansearch`: “An etale sheaf of commutative monoids defining a logarithmic
  structure with fine saturated charts and saturated log blowups”. Eight hits
  include the existing small étale site, regular structure sheaves, smooth
  manifold sheaves and formal étale localization; no logarithmic structure.
- `rg` of that same name pattern in upstream `WeilConjectures` found nothing;
  in project `lean/Sheaf` it found only `LogRegularPair`, whose fs monoid and
  congruence constructions are reused. `grep -rn def-trf-fs-log-blowup` in
  upstream found nothing. Explicit searches of all proposed public names in
  Mathlib, upstream, project Lean, and `dag/lean_names_upstream.json` found no
  existing names. Mathlib's monoid filtered-colimit and final-model sources
  were opened to use their constructions rather than postulating colimits.

Validation: both delivered modules are compiled separately through `scompile.py`
in dependency order. No warnings, errors, implicit variables, local notation,
private definitions, or postponed data are permitted in the delivery. The first `deliver2.py --no-push` run found only a signature-record formatting
mismatch: its parser starts at `def`, omitting `noncomputable`. The dependency
record was adjusted to that verbatim signature convention and the dry run repeated.

## Dependency modules

`def-weil-pbc-geometric-stalks` receives a §1(B) lean-only repair, module
`Sheaf.AlgebraicGeometry.PointedEtaleStalk`. Its prior recorded declaration
`Point.sheafFiber` requires all small colimits in the coefficient category.
Mathlib provides an explicit filtered colimit of commutative monoids but no
all-colimits instance for that category; thus that interface cannot be applied
to this item's monoid sheaf. The repaired `pointedEtaleStalkDiagram` is precisely
its original opposite category-of-elements diagram, and `pointedEtaleStalk` is
its colimit under the single necessary `HasColimit` assumption. `pointedEtaleGerm`
is its colimit injection. The monoid instance constructs that required colimit
using Mathlib's filtered colimit on `FinallySmall.FilteredFinalModel` and the
final functor back to the neighbourhood category. All set-valued and previous
coefficient-category specializations remain available. Only the dependency's
`lean` field changes; the node statement and `mathlib_match` remain intact.
The item consumes this repaired declaration directly for its monoid stalks and
canonical germs. There are no new independent notions or new DAG nodes.

Final dry run: `deliver2.py Q49 def-trf-fs-log-blowup --no-push` printed
`OK (dry run): commit ae5dad8453 passes the preflight and compiles; nothing pushed`.
Both files compiled cleanly separately in dependency order. The packet contains
exactly the two modules, the two lean-only node records, and this report.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
