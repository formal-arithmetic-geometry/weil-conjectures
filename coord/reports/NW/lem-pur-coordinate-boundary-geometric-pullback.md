## Worker report

The module `Sheaf.Paper.CoordinateBoundaryGeometricPullback` states
`WeilConjectures.PurityFiniteSetting.coordinate_boundary_geometric_pullback`.
Its only postponed proof is that theorem. All helper definitions contain actual
constructions. The theorem gives the three coordinate identities on both sites,
including their site comparisons. It does not assume that Spec Omega is finite type.

The hypotheses and objects of the node are rendered as follows.

- `P : PurityFiniteSetting.{u}` is the recorded finite purity datum: its field,
  coefficient extension, positive level, and actual quotient coefficient ring are
  used unchanged. `h : P.ramificationIndex ∣ P.level` is precisely e dividing n.
  `P.exponent` remains ell^(n/e) everywhere. `P.Coefficient` is the recorded
  universe lift of the actual quotient, not an independent coefficient ring.
- `Y : Scheme.{u}` and `a : Y ⟶ Spec (.of P.field.k)` specify the k-scheme;
  `[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]` say separated and
  finite type. The explicit structure morphism is used by the recorded datum.
- `Line Y`, `zeroSection Y`, `Punctured Y`, `openImmersion Y`, `coordinate Y`,
  `coordinateUnit Y` and `puncturedMap g` are the dependency's actual affine-line
  constructions. The induced line map `coordinateLineMap g` is literally
  `AffineSpace.map (ULift (Fin 1)) g`, with domain and codomain named by the datum.
  Thus neither the coordinate nor its open pullback is an arbitrary chosen unit.
- `P.twistEtale h T`, its exact comparison image, and the single complexes
  `coordinateEtaleInput` and `coordinateProInput` render F and F'. The
  root-tensor twist model already implements theta; `P.rootCoefficientMap`
  implements theta inverse after u tensor 1 (the recorded scalar-first tensor
  presentation uses 1 tensor u). `P.kummerEtale` applies this map to the ordinary
  Kummer connecting class; `P.coordinateKummer` is its recorded pro-etale image.
- `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Y)` is the
  geometric point. There is no finite-type, algebraicity, or transcendence-degree
  restriction on Omega or g. All coefficient maps are defined for arbitrary
  scheme morphisms. The common universe is the existing scheme-site convention;
  u is arbitrary, with site objects in u+1 and morphisms in u.

The three equalities and the simultaneous comparison clause are rendered as follows.

- `CoordinateKummerPullback` writes both actual Ext-class equalities using
  `CategoryTheory.Abelian.Ext.coordinatePullbackIdentity`, which expands to
  the two Yoneda compositions in abstract categories, with no assumptions on
  the classes beyond the equality being stated. Each left
  side applies the site's exact inverse-image functor to the coordinate class
  and postcomposes the canonical twist map. Each right side precomposes the
  target coordinate class by the canonical constant-sheaf comparison. Ext degree
  is exactly one, with `add_zero 1` and `zero_add 1`. On the pro-etale side the
  coefficient maps explicitly use `comparisonUpperStarCompUpperStarIso` and
  comparison inverse image of the SAME ordinary root-tensor and constant maps.
  This is h_U^* kappa(t) = kappa(t'), retaining the same m and scalar one.
- `CoordinateBoundaryModel` packages the unique complement identification over
  X, the existing `Sheaf.SupportSequenceBoundary` on each site, and the existing
  `supportBoundaryNormalization` fixing their injective snake-boundary sign.
  Its `chiEtale` and `chiPro` are the dependency's normalized `Identification`,
  including coefficient naturality and evaluation-at-one normalization.
  These are conclusions of existence, not extra input hypotheses or arbitrary
  maps substituting for the canonical constructions.
- `coordinateClassSection` evaluates the actual ordinary Ext class on the
  constant unit through canonical derived and shift comparisons.
  `Abelian.Ext.coordinateSectionMap` spells out their composite morphism before
  evaluation; its six factors are the same maps as in the original definition.
  `coordinateOpenSectionsIso` and `coordinateOpenDerivedIso` restrict to the
  actual open object by etale localization. The latter uses the existing exact
  open lower-shriek adjunction to preserve injectives. `coordinateEtaleOpenClass`
  uses the inverse of the recorded pure-tensor twist pullback isomorphism and
  then the unique complement isomorphism. `openProClass` applies the existing
  canonical comparison `finiteComparisonSectionHypercohomology`. Hence these
  are the open terms in the support sequence of F, not unrelated H^1 groups.
- `alphaEtale` and `alphaPro` apply the respective normalized boundary at degree
  one to precisely these open classes, giving degree two supported classes.
  `CoordinateBoundaryPullback` first states the two equalities of these classes
  under `Transport.coefficientGroupMap`. That map is the existing canonical
  `Transport.derivedMap` followed by the coefficient map on support cohomology.
  The coefficient maps `coordinateEtaleCoefficientPullback` and
  `coordinateProCoefficientPullback` use the recorded twist pullback and
  canonical single-complex and site comparisons. This is h^* alpha = alpha'.
- The `Transport.CoefficientCompatible` predicates each pair the support equality
  with a Hom equality. Their Hom clauses apply `D.chiEtale.chi` / `D.chiPro.chi` in degree two to
  alpha and alpha'. `Transport.coefficientHomMap` is literally the existing
  `Transport.homMap` followed by the shifted coefficient comparison.
  `homMap` is `Functor.representableTransportHom`, so it precomposes by
  `e.closedIso.inv`, pulls back the derived morphism, and uses the canonical
  single-object and shift comparisons. `Transport.closedIso_spec` fixes c by
  the constant restriction and `constantIso_spec` fixes its constant unit.
  Thus the direction is chi(alpha') = h^*M composed with c inverse, exactly.
- `CoordinateBoundarySiteAgreement` at Y and at Spec Omega states comparison of
  BOTH alpha and its chi representative using the canonical comparison inverse
  image and identity on `coordinateProInput`. `SupportHomSquareCoherent` is the
  recorded coherence of the derived support and closed-constant comparison
  squares. Together these specify the simultaneous ordinary/pro-etale identities.

Dependency declarations used, after reading their signatures and docstrings:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Coefficient`,
  `exponent`, `constantEtale`, `twistEtale`, `constant`, `twist`,
  `moduleClassToAbelian_bijective`, and `exponent_isUnit`.
- `Sheaf.Paper.PurityAffineLineDatum`: all affine-line objects above,
  `rootCoefficientMap`, `kummerEtale`, `coordinateKummer`,
  `twistEtalePullback`, `isIso_twistEtalePullback`, and `puncturedMap`.
- `Sheaf.AlgebraicGeometry.SupportLongExact`:
  `Sheaf.sectionHypercohomologyFunctor`, `supportHypercohomologyFunctor`,
  `SupportSequenceBoundary`, and `supportSequenceModelBoundary`; its theorem is
  `AlgebraicGeometry.exists_support_longExact`.
- `Sheaf.Paper.SupportedCohomologyHom`:
  `AlgebraicGeometry.ProEtale.supported_cohomology_hom`, imported transitively.
  The normalization used here is the refinement in the following dependency.
- `Sheaf.Paper.SupportedHomPullback`: `SupportHomPair`, `Identification`,
  `Transport`, `Transport.derivedMap`, `Transport.homMap`, `etaleSupportHomPair`,
  `proEtaleSupportHomPair`, the three scheme transport aliases,
  `supportHomDerivedComparison`, `SupportHomSquareCoherent`, and
  `supportedHom_pullback`. No private implementation of these is copied.
- New definition dependency `def-pur-support-boundary-normalization`,
  `Sheaf.AlgebraicGeometry.SupportComparisonBoundary`:
  `supportBoundaryNormalization` and
  `ProEtale.finiteComparisonSectionHypercohomology`. Only these general-site
  constructions are used; the finite-type existence theorem is NOT applied to
  Spec Omega over k. Normalized boundaries on its line exist by the same
  general-site injective construction; this existence is part of our theorem.

The two relative Kummer normalization nodes are proof dependencies; neither has
an assigned Lean record in this checkout. The statement uses the existing actual
Kummer maps from the affine-line datum, rather than replacing those maps or
assuming their naturality. The postponed proof's docstring follows the node's
four proof steps and names both normalization arguments. No missing proof
result is promoted to a new hypothesis.

Sources read: the current main-20261015 blueprint orientation proof, especially
its geometric-fibre sentence; Milne LEC Theorem 9.4, its Ext proof and Example
9.5 (PDF pages 66-68); Stacks `etale-cohomology.tex`, tag 03PL, label
`lemma-kummer-sequence`. No change to the node's mathematical statement is needed.

Edge cases checked: empty Y has no geometric points, while its normalized
boundary data still exist; n=e gives N=1 and keeps the same exponent in every
class; the coefficient characteristic is prime to the geometric characteristic
by P, so `exponent_isUnit` needs no extra hypothesis; arbitrary infinite
transcendence degree Omega is allowed; no preservation of injectives is assumed
for general geometric inverse image (its support map is derived base change);
only OPEN restriction uses the exact lower-shriek adjunction. The boundary sign,
closed comparison inverse direction, degree 1 to degree 2, and site shift maps
are all explicit. No choice of a generator replaces the coordinate class.

Searches performed before adding helpers:

- `msearch.py NW lem-pur-coordinate-boundary-geometric-pullback leanfinder`
  query: "Coordinate Kummer class pullback commutes with support boundary and
  supported Hom for arbitrary geometric point on etale and proetale sites".
  Eight affine-space/naturality/base-change hits, no statement of these
  simultaneous Kummer, support, and Hom identities.
- The same wrapper, `loogle`, query `"Kummer"`: eight field-theory and
  Kummer-Dedekind arithmetic declarations, none matching this node.
- The same wrapper, `grep`, query
  `coordinateKummer|supportSequenceBoundary|supportedHom`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Kummer, coordinateKummer,
  support boundaries, supportedHom, and open evaluation comparisons. Read the
  matching affine-line datum, relative-Kummer, Gysin, orientation, boundary
  realization and supported-Hom modules. Upstream `Etale.kummerBoundary_baseChange`
  is abstract ordinary Kummer naturality, not these actual finite coefficient
  maps or the pro-etale/support/Hom conclusions. The Gysin/orientation helpers
  concern a more specialized comparison package and do not give this unrestricted
  geometric-fibre statement; downstream orientation is not imported.
- Search for this item id in `lean/WeilConjectures`: no match. Search all proposed
  declaration names in Mathlib, WeilConjectures and Sheaf: no collision. An
  unrelated `coefficientGroupMap` in another namespace is not this support map.
- Existing `lem-asd-supported-kummer-boundary-pullback` is an etale-only
  Cartier-extension predicate, not an exact match for this item.

The new definition node below records existing boundary-normalization and section-
comparison definitions. The new node itself introduces no Lean declaration or
dependency module. The coordinate helpers remain listed in the item's `lean.declarations`. No
STATEMENT-DISPUTED issue was found.

## New nodes

`def-pur-support-boundary-normalization` records the existing general-site predicate
`AlgebraicGeometry.supportBoundaryNormalization` and the existing unit, derived,
and degreewise section comparisons `ProEtale.finiteComparisonSectionUnit`,
`ProEtale.finiteComparisonSection`, and
`ProEtale.finiteComparisonSectionHypercohomology`, all in
`Sheaf.AlgebraicGeometry.SupportComparisonBoundary`. Its source is Stacks Tag 09XP,
`section-cohomology-support`, the injective kernel sequence, together with the
blueprint orientation proof's final site-comparison sentence. The predicate fixes
the snake sign on each injective complex; the comparison is defined from the
actual adjunction unit. It asserts no existence of normalized boundaries and no
comparison theorem. The recorded signatures are general: neither finite type nor
finite coefficients is required. `existing: true` avoids duplicating these data.

Searches on 2026-10-23: `blueprint_refs.py search 'support boundary normalization'`
and `... 'snake boundary'` each found zero blueprint nodes; `rg` over DAG nodes
for the four declaration names found only the theorem carrier
`lem-pur-support-comparison-boundary`. Its statement is a finite-type comparison
THEOREM, rather than a definition of these general-site constructions. The
logged `msearch.py` LeanSearch query on injective snake normalization and the
etale/pro-etale section unit returned eight unrelated adjunction/normalization
hits; Loogle `"supportBoundaryNormalization"` and Mathlib grep
`supportBoundaryNormalization|finiteComparisonSection(Hypercohomology|Unit)?`
returned zero hits. The same `rg` over `lean/WeilConjectures` and `lean/Sheaf`
located the four definitions in `SupportComparisonBoundary.lean` and a use in
`PurityAffineLineOrientation.lean`, with no upstream duplicate. Thus the new node
records existing Lean definitions that no existing definition node carries.

## Second reading by NW

I reopened the item JSON, its delivered module, the four existing definitions
recorded by the new node, and the blueprint geometric-fibre and final comparison
sentences. This is the dispatch-authorized second reading in the same worker;
the maintainer supplies the independent review. The clause matching is:

1. The node fixes the finite purity datum, A=O_E/varpi^n, e dividing n,
   N=n/e and m=ell^N. The theorem binds `P : PurityFiniteSetting.{u}` and
   `h : P.ramificationIndex ∣ P.level`. `coordinateEtaleKummer` and
   `coordinateEtaleOpenClass` use `P.kummerEtale h` and `P.exponent_isUnit`;
   `CoordinateKummerPullback` uses `P.coordinateKummer h` on the pro-etale side.
   These are the existing datum's quotient coefficients and exponent, not new
   free coefficient parameters. No discrepancy found.
2. The separated finite-type k-scheme is exactly `Y`, its structure morphism `a`,
   and `[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]`. The arbitrary
   geometric point is `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
   (g : Spec (CommRingCat.of Ω) ⟶ Y)`. There is no finite-type instance for g
   or its composite with a. The single arbitrary scheme universe follows the
   supplied small sites, with objects in u+1 and arrows in u. No case is lost.
3. X, s, U, j and the corresponding primed objects are the imported `Line`,
   `zeroSection`, `Punctured`, and `openImmersion` applied to Y and Spec Omega.
   The maps h and h_U are `coordinateLineMap g` (the actual `AffineSpace.map`)
   and `puncturedMap g`. The complement isomorphisms are over X and hence unique.
   The coefficient complexes are exactly `coordinateEtaleInput` and its
   `coordinateProInput` comparison image. No arbitrary replacement is used.
4. The node's theta and u tensor one are the datum's root-tensor twist and
   `rootCoefficientMap` (scalar-first order one tensor u). Both arguments of
   `CoordinateKummerPullback` use the SAME P and h. Its abstract helper now uses
   the existing `IsGrothendieckAbelian.hasExt` instance in both categories;
   the concrete sheaf categories already have these structures. This only
   shares the instance proof and adds no premise to the theorem. Its two Ext equalities
   expand via `coordinatePullbackIdentity` to exact inverse image of the source
   class followed by the canonical twist map, equal to the target class
   precomposed by the constant comparison. The target unit is `coordinateUnit`
   on the actual punctured line. This renders h_U^* kappa(t)=kappa(t') on BOTH
   sites and preserves m and one exactly; no discrepancy found.
5. Alpha and alpha' are `D.alphaEtale` / `D'.alphaEtale` and their pro-etale
   counterparts, defined by `(boundaryEtale 1).app` or `(boundaryPro 1).app`
   on the coordinate open class. Thus degree one maps to supported degree two.
   I also read the compiler repair: `coordinateSectionMap` composes the
   degree-zero derived unit, inverse single-object homology comparison,
   homology of the derived Ext morphism, shift comparison, and inverse
   bounded-below/unbounded comparison. Applying that composite to the original
   constant-unit section reproduces the original nested evaluations in the
   same order, by composition of module maps. No sign, scalar, degree or
   comparison changes.
   `coordinateEtaleOpenClass` restricts the actual Kummer Ext class through the
   inverse twist-pullback isomorphism and the complement identification;
   `openProClass` uses `finiteComparisonSectionHypercohomology`. The fields
   `etale_normalized` and `pro_normalized` fix the snake boundary sign.
   The existential models conclude existence of this normalized data and
   identifications; they are not extra hypotheses or arbitrary generators.
6. The equality h^* alpha=alpha' occurs in each half of
   `CoordinateBoundaryPullback`, through `Transport.CoefficientCompatible`.
   Its first conjunct is `coefficientGroupMap b 2 x = y`. The body of that map
   applies degree-two homology to `Transport.derivedMap`, then maps the
   coefficient morphism b by the actual support-hypercohomology functor.
   The b arguments are `coordinateEtaleCoefficientPullback` and
   `coordinateProCoefficientPullback`. This is the derived support pullback
   followed by F'=h^*F, with no preservation-of-injectives assumption on h.
7. M=chi(alpha) and chi(alpha')=h^*M composed with c inverse occur in the SECOND
   conjunct of each `CoefficientCompatible`. `coefficientHomMap` first uses
   `Transport.homMap`, whose `representableTransportHom` uses `closedIso.inv`,
   then applies the shifted coefficient map. `constantIso_spec` and
   `closedIso_spec` normalize c by the constant unit and restriction; the
   `Identification.normalization` field fixes chi on injective cocycles by
   evaluation at one. The inverse direction and shift by two agree with the
   displayed node formula. No purity isomorphism is assumed.
8. The node requires simultaneous etale and pro-etale identities and their
   canonical comparisons. `CoordinateKummerPullback` has two site clauses,
   `CoordinateBoundaryPullback` has the two boundary/Hom clauses, and the
   theorem has `CoordinateBoundarySiteAgreement` at BOTH a and g composed
   with a. These use the canonical site transport with identity coefficient
   comparison on `coordinateProInput`. `SupportHomSquareCoherent` identifies
   the support and closed-constant comparison squares for e, p, v and v'.
   Therefore no one-site or comparison clause is omitted.
9. I read the new definition node clause by clause against the existing module.
   The general site, ring, arrow and boundary family are precisely the binders
   of `supportBoundaryNormalization`. Its quantified injective complex, short
   exact sequence witness and equality with `hS.δ q (q+1) rfl` give its entire
   first paragraph. The second paragraph's unit evaluation, derived base
   change and integer homology are respectively `finiteComparisonSectionUnit`,
   `finiteComparisonSection`, and `finiteComparisonSectionHypercohomology`.
   No existence assertion, finite-type restriction, or comparison theorem is
   included. Its three cited definition nodes supply the support kernel,
   cochain convention, and comparison adjunction; the signatures are read
   directly rather than through a choice from the theorem.

Return repairs: H2 is fixed by replacing the added theorem dependency
`lem-pur-support-comparison-boundary` with the new existing-definition node.
The five original statement dependencies are retained, including
`lem-pur-supported-hom-pullback`, whose structures carry the canonical
normalizations used here (the return's advisory). H11 is fixed by the detailed
reading above, replacing the six-line generic self-audit. The mathematical
statement and theorem signature remain unchanged. The compiler repair described
below only factors the same class-evaluation morphism and pins the existing Ext
instances; no mathematical clause changes. Edge cases were rechecked: the empty Y has no g; n=e still uses N=1; arbitrary
algebraically closed Omega of infinite transcendence degree is allowed; only
open restriction, not arbitrary geometric inverse image, uses preservation of
injectives. No mathematical mismatch or statement correction was found.

## Validation

The initial required dry run of the retained packet timed out in the server's
60-second compile. Isolated module-mode profiles identified repeated small-Ext
instance expansion and concrete class-evaluation kernel checking. The repair
keeps the theorem signature and all canonical constructions: the abstract
`coordinatePullbackIdentity` takes the existing Grothendieck abelian structures
and thereby uses their canonical `HasExt` instances; the new helper
`CategoryTheory.Abelian.Ext.coordinateSectionMap` composes the same evaluation
maps abstractly before applying them to the unchanged constant unit. The helper
is listed in `lean.declarations`, has a source docstring, and contains real data.
Search in Mathlib, WeilConjectures and Sheaf found no `coordinateSectionMap`
collision. No module was split and no compile limit was raised.

The complete repaired candidate compiled with `scompile.py` as sandbox and
library (45.8 s and 45.0 s), exit 0 and no warnings. The actual delivery module also compiled as
`Sheaf.Paper.CoordinateBoundaryGeometricPullback` (48.3 s), exit 0 without
warnings. The existing-definition checks are verified by the prescribed dry
run before push. All profiling and partial-module files remain outside the
packet's `lean/` directory and are excluded from delivery.
