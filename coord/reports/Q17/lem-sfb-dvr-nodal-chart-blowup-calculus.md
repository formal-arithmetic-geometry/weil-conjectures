## Worker report

The delivery states `lem-sfb-dvr-nodal-chart-blowup-calculus` in
`Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus`, namespace
`AlgebraicGeometry.DvrNodal`. The main recorded declaration is `blowup_geometry`;
`lean.declarations` records every helper and the seven theorem declarations that
together give all clauses of the node. Every theorem proof is `sorry`; definitions
contain actual data. There is no statement correction and no disputed statement.
The earlier NJ PASS is a review of the natural-language DAG split, with no Lean
record; it did not formalize this stage-2 item. This is a repair of the retained packet returned at head `6970892c66b3`.
The initial dry run of that saved packet passed as commit `51a7bba3dce`; the
self-check nevertheless confirmed that the two returned ownership findings still
needed concrete changes. The live node still has no Lean record; its original
statement, proof and proof dependencies are retained.

The source is de Jong, *Families of curves and alterations*, Lemma 3.13 proof,
printed p.609, read in the primary PDF. Its local equation and rational exceptional
curves are made explicit by the calculation in the node's 15 proof steps. I also
read the affine blowup and flat base-change statements in Stacks divisors.tex,
Tags 0804/0805, and curves.tex, Tag 0CBY. The full source-based node proof is carried
in the theorem docstrings, separated according to the corresponding clauses.

### Hypotheses and constructions

| Node text | Lean rendering |
| --- | --- |
| A discrete valuation ring R | `(R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]`; the recorded Mathlib class is a local PID with nonzero maximal ideal, not a field. |
| pi generates the maximal ideal | `(π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})`. No additional nonzero, irreducibility, completeness or residue-field hypothesis is imposed. |
| n >= 1 | `(n : ℕ) (hn : 1 ≤ n)` in `model_properties`; n >= 2 for the blowup statements. |
| M_n = Spec R[x,y]/(xy-pi^n) | `model R π n`, the arithmetic specialization of the existing `StrictSemistableModel.nodal` and `strictNodalRing`. `projection` is its existing coefficient map. |
| o = (pi,x,y) | `IsOrigin R π n o` is equality of `o.asIdeal` with the `originIdeal R (π ^ n) π`. `model_properties` proves existence of such an o. |
| k = R/(pi) | The centre quotient is that residue field: its generators are pi,x,y. All exceptional statements are geometric, quantified over algebraically closed `Ω` with a geometric morphism whose image is o, so the residue-field extension is specified by the morphism rather than chosen as unrelated data. |
| Ordinary blowup of the reduced point | `(centre R π n).blowup` and `.blowupMap`, with `centre` obtained from the actual `(pi,x,y)` generated ideal via `IdealSheafData.ofIdealTop` and `ΓSpecIso.inv`. `model_properties` identifies its support with `{o}` and states its radical equality, retaining the reduced scheme structure. |

### Clauses

| Node clause | Lean rendering |
| --- | --- |
| M_n integral | `IsIntegral (model R π n)` in `model_properties`. |
| All local rings integrally closed domains | The pointwise conjunction of `IsDomain` and `IsIntegrallyClosed` on `(model R π n).presheaf.stalk x`. It is the local-ring condition of the node, not only global integral closedness. |
| Flat over R | `Flat (projection R π n)`. |
| Reduced nodal geometric curve fibres | An existential `hfp : LocallyOfFinitePresentation ...` supplies the argument required by the recorded `HasNodalGeometricFibres`, followed by `@HasNodalGeometricFibres ... hfp`. Reducedness of every geometric fibre is stated separately as `IsReduced (pullback ... g)`. The existing nodal predicate includes nonemptiness, connectedness, dimension one, and completed local node equations. |
| Regular outside o | `IsRegularScheme (Scheme.Opens.toScheme (X := model R π n) (centre R π n).support.compl)`; the same theorem identifies the support with `{o}`. This uses the recorded locally-Noetherian regular-scheme notion, not a weaker standalone stalk condition. |
| Regular at o iff n=1 | `IsRegularLocalRing ((model R π n).presheaf.stalk o) ↔ n = 1`. |
| Every local dimension <=2; origin dimension 2 | `ringKrullDim ... ≤ 2` for every model point and `ringKrullDim ... o = 2`. |
| Smooth R-scheme of pure relative dimension one | `smooth_properties` takes `f : X ⟶ Spec R`, `[Smooth f]`, and `hpure : ∀ s, (f.fiber s).IsPureDimension 1`, using the recorded fibre and pure-dimension notions. |
| Smooth alternative regular and normal, all local dimensions <=2 | `IsRegularScheme X`, pointwise domain/integrally-closed conjunction and `ringKrullDim ... ≤ 2`. |
| Dimension 2 at closed points of the special fibre | A point `s : Spec R` with `s.asIdeal = maximalIdeal R`, then `z : f.fiber s` with `IsClosed {z}`; conclusion is the dimension of the total-space stalk at `f.fiberι s z`, equal to 2. Closedness is in the special fibre, as stated. |
| Common pointed etale local models | `pointed_etale_properties` takes the two etale legs `a : W ⟶ X`, `b : W ⟶ Y`, the equality over R, and a specified point `w`. `hmodel` says Y maps etale over R to a positive-exponent nodal model, or is the smooth pure-curve alternative. It gives normality, equivalence of the normal and regular local-ring predicates at `a w`/`b w`, equality of local dimensions and the upper bound. Applying it with one leg the identity compares a model to its etale chart; then a common neighbourhood transfers all the assertions, including dimension 2 and nonregularity at the indicated origin. There is no residue-field-isomorphism hypothesis. |
| Three affine chart rings | `chart_rings` gives ring isomorphisms from the existing strict nodal rings with parameters `π`, `π ^ (n - 2)`, `π` to the actual `AffineBlowup.chartRing` subalgebras for denominators x,pi,y. The equations for every coefficient `c : R` force these to respect R. |
| x-chart: xt=pi, y=x^(n-1)t^n | Its source ring supplies xt=pi; the e0-coordinate equations send x to the canonical x and the old y to `e₀ (X₀ ^ (n-1) * X₁ ^ n)`. There is no unsaturated substitution ring. |
| Middle: rs=pi^(n-2), x=pi*r, y=pi*s | The middle source ring supplies the relation; the two e1-equations give the displayed original-coordinate images. At n=2 its parameter is pi^0=1, hence rs=1. |
| y-chart: yt'=pi, x=y^(n-1)(t')^n | The e2-equations are symmetric to the first, with its first source coordinate the old y. |
| They cover B_n with the specified maps | `blowup_geometry` gives three open immersions `j₀,j₁,j₂` whose ranges cover the actual global blowup. Each map commutes with the R-projection, and its two `appTop` equations explicitly give all six original-coordinate formulas, using the canonical `ΓSpecIso`. These equations tie the covering embeddings themselves to the formulas, in addition to the actual-chart-algebra assertion in `chart_rings`. |
| B_n flat with reduced nodal geometric curve fibres | `Flat` of blowupMap followed by projection, the existing nodal predicate with its hfp argument, and explicit reducedness of every geometric fibre. |
| Only possible nonregular point is the middle origin when n-2>=2; local model M_(n-2) | For every blowup point z the nonregular-stalk predicate is equivalent to `4 ≤ n ∧ ∃ q : model R π (n - 2), IsOrigin ... q ∧ j₁ q = z`. The open immersion j1 supplies its actual open local model, not merely an abstract ring of the same dimension. |
| Geometric exceptional fibre, n=2 | `ExceptionalGeometry` requires smoothness, an isomorphism over Ω to `ProjectiveLine (Spec Ω)`, and an isomorphism over Ω to the actual conic subscheme `conicIdeal`. Its equation is the zero scheme of the section X*Y-P*P of O(1) tensor O(1); no radical or characteristic-dependent replacement. |
| Geometric exceptional fibre, n>2 | `ExceptionalGeometry` requires a reduced E and two closed immersions of P1 over Ω whose images cover E. `IsPullback a b i j` identifies their scheme-theoretic intersection with Spec Ω. Both a and b are sections over Ω. Thus the intersection is exactly one reduced rational point, not only a nonempty set intersection. |
| Map is an isomorphism off o | `IsIso (blowupMap ∣_ centre.support.compl)`; support={o} is in `model_properties`. |
| Descriptions after etale pullback | `etale_blowup` uses the inverse-image ideal `.comap e` and states that the canonical existing `blowupFlatBaseChange e` is an isomorphism. By its definition and recorded over-base identity it identifies every pulled-back chart, including the maps. At every chosen `u` over o and every geometric `g` with image `{u}`, it states `ExceptionalGeometry` for the actual pulled-back-centre blowup fibre. |
| Reduced point in a common pointed etale neighbourhood | `pointed_reduced_centre` supplies an open V containing the specified common point, a point v over it, closedness of v, and equality of the inverse-image ideal with the vanishing ideal of the closure of `{v}`. The latter is the actual reduced point since v is closed. It states the exceptional description for its blowup; the chart description follows by the canonical comparison of `etale_blowup` applied to this etale open chart. |
| No extra assumptions | No excellence, completeness, perfection, equal-characteristic, or residue-characteristic assumption occurs. |

### Dependency declarations used

The fourteen original statement dependencies were read with their recorded declaration
or Mathlib match. Their interfaces are usable; no dependency repair was required.

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` (the generator convention).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; multivariate presentations use
  the already-existing `strictNodalRing`, not a second quotient-ring definition.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd`; these are the recorded geometric-fibre construction, along the
  explicitly supplied algebraically closed geometric point.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`;
  its body is local Noetherianity together with the existing stalkwise `IsRegular`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`: the
  `ProjectiveLine` and standard-cover implementation underlying the recorded
  `ProjectiveLine.TwistData`. The item needs the line, not a choice of twist data.
- `Sheaf.AlgebraicGeometry.NodalGeometricFibres`: `HasNodalGeometricFibres`.

The added statement dependency `def-trf-strict-semistable-curve` owns
`Sheaf.TraceFormula.StrictSemistableCurve`: `strictNodalRing`,
`StrictSemistableModel.scheme`, and `StrictSemistableModel.baseMap`.
The former extra dependency `lem-trf-valuation-symmetric-nodal-blowup` was removed
in repair F1: the reviewer explicitly allowed the elementary definitions to live
in the item's module. `DvrNodal.constant` and `DvrNodal.coordinate` are the images
of `MvPolynomial.C` and `MvPolynomial.X` under `Ideal.Quotient.mk` in the existing
ring; `DvrNodal.originIdeal` is the sum of the coordinate-generated ideal and the
uniformizer-generated ideal. `centre` uses `IdealSheafData.ofIdealTop` directly,
with the same canonical `ΓSpecIso.inv` as the returned packet. These definitions
are real data, have source/blueprint docstrings, and are listed in
`lean.declarations`. No result or constructed object of the symmetric-blowup
theorem is used. This follows the precise alternative authorized in return F1.

Repair F2 adds the owners actually used in the signatures:

| Definition node | Module and declaration |
| --- | --- |
| `def-nagata-blowup-chart-ring` | `WeilConjectures.Blowup.Affine.ChartAlgebra`, `AlgebraicGeometry.AffineBlowup.chartRing` |
| `def-nagata-blowup-flat-base-change-map` | `WeilConjectures.Blowup.FlatBaseChange`, `Scheme.IdealSheafData.blowupFlatBaseChange` |
| `def-nagata-extended-ideal` | `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`, `Scheme.IdealSheafData.comap` |
| `def-pc-zero-scheme` | `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`, `Scheme.Modules.Hom.zeroLocus` |
| `def-sfb-projective-coordinate-section` (new ownership node) | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection`, `ProjectiveSpace.coordinateSection` |

Each existing node's statement and recorded declaration were opened; the actual
bodies are, respectively, the subalgebra generated by fractions, relative-Proj
comparison, kernel of the pulled-back closed immersion, and local coefficient
ideal. The coordinate section is the canonical pullback of multiplication by
`T_i` on the integral projective model. Its existing construction is recorded,
not implemented again.

The source's `WeilConjectures.Blowup.FlatBaseChange` supplies the canonical
`Scheme.IdealSheafData.blowupFlatBaseChange` and `blowupFlatBaseChangeIso`; the latter
is over the new base by `blowupFlatBaseChangeIso_hom_snd`. These are real existing
maps, not arbitrary isomorphisms selected with Nonempty. The modules recorded on
all stated proof dependencies are imported privately; the statement interfaces
are imported publicly. The new helper `conicIdeal` spells out the conic in this
item's own conclusion and `ExceptionalGeometry` groups its two exceptional cases;
these are owned by this node, not new independent mathematical prerequisites.

### Edge cases checked

- n=1: no blowup is asserted; pi=xy at the origin gives maximal ideal (x,y) and
  dimension two, hence regular. The origin remains a closed point, not a generic
  point of a branch.
- n=2: the middle ring has rs=1 and no origin; the singular-point equivalence has
  false left side everywhere since `4 ≤ n` is false. The exceptional middle chart
  is the overlap of the two affine lines, giving P1 and the smooth conic.
- n=3: the middle chart is M1, so the entire blowup is regular while its exceptional
  fibre is still a pair of P1's meeting once.
- n=4: the middle M2 origin is the unique remaining nonregular point.
- Characteristic two: the conic XY=P² has X/Y partial derivatives Y/X; both cannot
  vanish at a projective conic point. The displayed quadratic equation is unchanged.
- Mixed characteristic and nonexcellent DVRs: the ring calculations, flatness over
  a valuation ring, etale ascent/descent, and flat Rees comparison use none of the
  excluded hypotheses.
- Empty smooth scheme: `hpure` is vacuous for empty fibres and every conclusion
  about points is vacuous; `IsRegularScheme` admits the empty scheme.
- Nonrational etale points: neither local-property comparison nor the reduced-point
  blowup identifies residue fields. Exceptional geometry is taken over an explicitly
  chosen geometric point above that point.
- Schemes and geometric fields all use the same explicit universe u, exactly as
  the recorded nodal-geometric-fibre predicate; no smaller independent test universe.

### Searches and validation

- `msearch.py`, LeanFinder: "blowup of xy equals power of a uniformizer over a
  discrete valuation ring nodal surface three charts exceptional projective lines".
  Eight hits, all on elliptic Weierstrass minimal models or coordinate ideals;
  none states this result.
- `msearch.py`, Loogle: "IsDiscreteValuationRing, AffineBlowup, IsRegularLocalRing".
  Zero hits; AffineBlowup is not a Mathlib identifier (it is in the project).
- `msearch.py`, grep: "nodal|blowup" in Mathlib/AlgebraicGeometry. Zero hits.
- `rg` in `lean/WeilConjectures` for the item ID: no match. Searches for arithmetic
  nodal/blowup names found the general affine/global blowup infrastructure, not this
  combined theorem.
- `rg` in `lean/Sheaf` for nodal chart/blowup names found the existing strict nodal
  ring and the symmetric helper formulas inspected for the F1 repair, and downstream comments citing this item,
  but no declaration of its arithmetic singular-point calculation.
- The delivered module is compiled exclusively using `scompile.py`. A first clean
  compile confirmed all imports and the initial signatures. A later elaboration
  error on dot-notation for an open subscheme was repaired by the explicit recorded
  `Scheme.Opens.toScheme` constructor. Final compilation and the delivery preflight
  are run after the final statement and documentation edits.


## Repair of returned delivery

F1: removed the theorem dependency and its public import. Added the elementary
`constant`, `coordinate`, `originIdeal` definitions in this item's namespace,
with explicit binders and real quotient-ring/ideal data; inlined the canonical
affine-ideal conversion in `centre`. This is the item's-module alternative the
return requests. The same quotient ring and definitionally identical ideal and
section formulas underlie the original seven theorem statements.

F2: added all four named existing definition nodes and the new exact
`existing: true` ownership record for `ProjectiveSpace.coordinateSection`.
The new record has no module of its own and introduces no duplicate definition.
No statement correction is needed: the mathematical objects and assertions are
unchanged. The original node fields other than `lean` and `stmt_deps` are unchanged.

## New nodes

`def-sfb-projective-coordinate-section` records the already published
`AlgebraicGeometry.ProjectiveSpace.coordinateSection` in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection:109`.
It introduces the projective space, the projection to its integral model and
O(1), then defines T_i by pullback of the homogeneous multiplication map, with
its canonical unit identification. Source: Stacks constructions.tex, Tags
01ND/01NE/01NF, especially the paragraph after definition-projective-space;
the upstream construction explicitly implements this description. The node
cites the existing projective-space, twist and module-pullback definitions.
LeanSearch returned affine coordinates and structure-sheaf sections;
LeanFinder returned `Proj.awayToSection` and related structure-sheaf maps;
the logged Mathlib grep returned no hit. The project-source search found the
exact existing coordinateSection. DAG definition scanning and
`blueprint_refs.py search 'coordinate section'` found no definition owner;
`def-pc-projective-space-twist` defines the twist, while
`def-weil-pbc-symmetric-product-sections` constructs different product sections.
Thus this is an ownership record only, not a new mathematical construction.
For an empty index set there is no i, hence no coordinate to specify; a singleton
gives the usual generator of O(1) on projective zero-space. The empty base scheme
is allowed. No field, Noetherianity or characteristic hypothesis is added.

## Second reading by Q17

This repair self-check reread the node, the complete delivered module, the
returned findings and the newly cited definition interfaces. No additional agent
was invoked. The hypothesis/clause tables in Worker report above give the full
matching: the DVR and maximal-ideal generator binders are unchanged; n>=1
remains the local-model range and n>=2 the blowup range; every model and smooth
local property, pointed etale comparison, saturated chart and covering formula,
exceptional-fibre case, complement isomorphism, etale pullback and reduced-point
assertion remains. The only theorem-signature edits rename the elementary
quotient constants and coordinates and their generated ideal to the item's
own helpers. Expanding these helpers gives exactly the former expressions.
In particular rs=1 at n=2, the false singularity condition at n=2,3, its unique
middle origin for n>=4, the characteristic-two conic and nonrational etale
points all retain the interpretations recorded above.

I found and repaired the two ownership mismatches explicitly: the symmetric
blowup theorem was being cited for plain definitions, and five definition owners
were absent. I checked the new coordinate-section node against the existing body:
`pullbackObjUnitIso.inv` followed by the pullback of `Proj.unitToTwist` is exactly
the stated section, with no arbitrary map chosen. Existing dependency nodes were
not edited; the new node cites exactly its three bracketed definition references.
All definitions use real data. All seven theorem proofs remain `by sorry`.
The final server compile and delivery dry run are recorded below after execution.


### Final validation of the repair

`scompile.py Q17 lem-sfb-dvr-nodal-chart-blowup-calculus` compiled the delivered
module cleanly in sandbox and library modes (11.9 s and 10.8 s), with no errors
or unexpected warnings. There are seven postponed theorem proofs, no line over
100 characters, and both automatic-implicit options are false. A direct JSON
comparison with the live node confirms that only `stmt_deps` and `lean` change;
`lean.statement` matches the file signature verbatim. The symmetric-theorem
import and statement dependency are absent.

`deliver2.py Q17 lem-sfb-dvr-nodal-chart-blowup-calculus --no-push` then reported
`OK (dry run): commit 5aa98a627b5 passes the preflight and compiles; nothing pushed`.
The final delivery repeats the required preflight/compile before pushing.
