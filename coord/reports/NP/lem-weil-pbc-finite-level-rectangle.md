## Worker report

`Sheaf.Paper.FiniteLevelRectangle` states
`AlgebraicGeometry.Scheme.properBaseChangeFiniteLevelRectangle`, with `sorry`.
It asserts the equality of the two composites of the **specified** four arrows
of `properBaseChangeFourArrows`. It does not quantify over arbitrary arrows or
assume commutativity as an input. No definition of a corner, coefficient, or
exchange is duplicated in the item module.

Hypothesis and clause audit:

- The square and proper morphism inherited from the four corners are
  `{X' X Y' Y : Scheme.{t}}`, the four explicitly bound morphisms,
  `sq : ChosenCartesianSquare g' f' f g`, and `[IsProper f]`.
- The adic datum is `d : ProEtaleAdicCoefficientDatum A`, with
  `{A : Type (t + 1)} [CommRing A]`. This is the completed-coefficient datum used
  by the delivered corner and arrow modules, including finite perfect quotients.
  The generator presentation is `r : ℕ`, `a : Fin r → A`, and
  `ha : Ideal.span (Set.range a) = d.ideal`.
- The given complex is `K : fourCornerDerived X (adicDatumRing X d)`.
  `C : CochainComplex (proEtaleRingModules X (adicDatumRing X d)) ℤ` and
  `eC : DerivedCategory.Q.obj C ≅ K` present the same object for the existing
  intrinsic-completion predicate; they do not replace K by a different object.
  Derived completeness is
  `hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC`.
- The finite-coefficient origin data retained by the four-arrow definition is
  `W n : ProEtale.FiniteCoefficientDerivedCategoryPlus X (fourArrowQuotient d n)`,
  `w n : ProEtale.EtaleOriginWitness X (fourArrowQuotient d n) (W n)`, and the
  coefficient-presentation isomorphism
  `e n : (fourArrowOriginTransport X d n).obj (W n).obj ≅
  (adicDatumReduction X d n).obj K`.
  These are exactly the existing definition's inputs. There is no uniform
  lower-bound assumption and no compatibility assumption on different witnesses.
- “For every n” is the arbitrary binder `(n : ℕ)`. Throughout the actual tower,
  this index denotes the positive paper exponent `n + 1`, including exponent one.
- Write F for the expression
  `properBaseChangeFourArrows sq d r a ha K C eC hK W w e n` solely in this
  explanation. Its projections `F.1`, `F.2.1`, `F.2.2.1`, and `F.2.2.2` are,
  respectively, h, h', v, and v'. Thus the conclusion
  `F.1.hom ≫ F.2.2.2.hom = F.2.2.1 ≫ F.2.1.hom` renders exactly
  `v'_n h_n = h'_n v_n`. The source file repeats the full expression, with no
  local notation, implicit arrow choice, or hidden let binder.
- The four corners are the four projections of
  `properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n`.
  All composites are in the derived category over the **finite quotient ring
  sheaf on Y'**. Ordinary, uncompleted pullback is retained. The right arrow's
  underlying morphism is `fourArrowFiniteExchange sq d K n`; W, w, and e only
  prove that canonical morphism invertible.

Dependencies used and read in full:

- `Sheaf.Paper.ProperBaseChangeFourCorners`,
  `AlgebraicGeometry.Scheme.properBaseChangeFourCorners` and its canonical
  `fourCornerCoefficientIso`, `fourCornerReductionPullback`, and
  `fourCornerEReductionIso` helpers. This is the interface delivered by Q06 and
  reused in the NG four-arrows delivery.
- `Sheaf.Paper.ProperBaseChangeFourArrows`,
  `AlgebraicGeometry.Scheme.properBaseChangeFourArrows`, particularly the
  actual definitions `fourArrowProjection` and `fourArrowFiniteExchange`.
- `Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange`,
  `AlgebraicGeometry.Scheme.finiteConstantRingedExchange_isIso`, supplies the
  exact canonical finite mate used by `fourArrowFiniteExchange_isIso`.
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`,
  `AlgebraicGeometry.Scheme.proEtaleProjectionFormulaMate` and its general
  Cartesian-square compatibility; the module is a proof import. The ambient
  exchange and profinite-coefficient modules are proof imports as well.
- The perfect-projection-formula node has no published Lean record in the shared
  base. I checked its Q13 delivery, including `perfectProjectionFormula_locus`
  and its exact signature and docstring. The item type needs the existing
  horizontal isomorphisms from `properBaseChangeFourArrows`, whose named
  `fourArrowProjection_isIso` has this perfect-projection-formula proof plan.
  The general thick-locus theorem is not a new object required to form the
  rectangle, and is not restated here with a competing coefficient interface.

The source was checked against the blueprint node and Stacks
[0E48](https://stacks.math.columbia.edu/tag/0E48),
[0B56](https://stacks.math.columbia.edu/tag/0B56), and
[07A7](https://stacks.math.columbia.edu/tag/07A7). The docstring carries both proof steps: first identify all four canonical
maps, then specialize projection-formula/base-change compatibility to the
perfect finite quotient. No additional commutativity or invertibility hypothesis
is imposed on v.

Edge cases were checked at the level of the statement and definitions: n = 0
means quotient exponent one; zero complexes, the empty scheme, the zero ring,
and zero quotient coefficients are not excluded. Empty generator lists r = 0
remain allowed when ha holds. For I = A the quotients are zero, and for I = 0
one still supplies the datum's finite-quotient hypotheses. No positivity of r,
nonempty scheme, nonzero coefficient ring, boundedness of integral K, common
lower bound on all W n, or equality of the site's object/morphism universes is
added. The small-site universe convention t+1 for objects and t for morphisms
is inherited unchanged from the dependency declarations.

Searches (recorded also in searches.jsonl):

- LeanFinder via msearch.py: “The canonical projection formula map commutes with
  the base change exchange map on derived categories of sheaves at every finite
  coefficient level”. Eight results concerned ordinary module-sheaf pullback,
  free objects and related comparisons; none states this rectangle.
- Loogle via msearch.py: `"projectionFormula"`, zero results.
- Mathlib grep via msearch.py, CategoryTheory:
  `projection.*[Bb]ase[Cc]hange|finiteLevelRectangle`, zero results.
- rg over upstream WeilConjectures and shared lean/Sheaf, and the literal node-id
  search in WeilConjectures: no implementation of this finite-level theorem.
  Existing general naturality supplies the proof, rather than this exact
  finite-coefficient equality.
- Server delivery-branch search found NG/def-weil-pbc-four-arrows,
  Q06/def-weil-pbc-four-corners, and Q13/lemma-weil-pbc-perfect-projection-formula.
  I read the delivered signatures and reused the NG/Q06 modules verbatim,
  instead of defining another version of their notions.

No statement correction, new definition node, or mathematical dispute is needed.
The independent second reading remains for the next worker, as requested.

## Dependency modules

`def-weil-pbc-four-corners`: the shared node has no usable published Lean record.
This delivery includes the exact `Sheaf.Paper.ProperBaseChangeFourCorners` source
from the delivered NG branch, itself reusing Q06's definition. Its actual
coefficient tower, profinite comparison, uniquely normalized ordinary mate and
K-flat reduction comparison fix all four corners, retaining quotient actions.
Only the dependency node's lean record is changed.

`def-weil-pbc-four-arrows`: the shared node has no usable published Lean record.
This delivery includes the exact `Sheaf.Paper.ProperBaseChangeFourArrows` source
from NG's delivery. It defines precisely the finite projection adjuncts, their
canonical isomorphisms, the reduction of integral exchange, and canonical finite
exchange. Its origin witness is used only for invertibility. Only lean changes.

`thm-weil-pbc-finite-level-proetale`: NG's delivered
`Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange` avoids the unusable legacy
coefficient/duplicate-notation interface and states proper base change for the
same finite commutative constant ring sheaves and the same actual ringed exchange
mate, transporting the recorded bounded-below etale-origin witness. Its source
is reused verbatim and only lean changes.

Validation: the prescribed scompile.py file-only run compiled all four modules
separately, in dependency order, both in sandbox checks and as their library
module names. It exited zero with no errors or warnings. No global build was
run. The first dry run compiled all four modules and the existing-declaration probe
without warnings. Preflight rejected an unnecessary transitive metadata
attachment for the already available projection-formula mate. That attachment
was removed; no Lean file changed. The corrected dry run is required before READY.

## Second reading by NP

I read the item node, its original statement and two proof steps, and the complete
four-corners, four-arrows and finite ringed base-change modules independently.
The item has no `statement_change`. Its TeX statement is the commutativity of the
specified square; the objects and hypotheses are inherited from its two definition
nodes, rather than arbitrary corners or arrows. The following is my object,
hypothesis and conclusion list, with the corresponding Lean and verdict.

| Node object, hypothesis or clause | Lean rendering and verdict |
| --- | --- |
| Four schemes and four square edges | Explicit `{X' X Y' Y : Scheme.{t}}` and `{g' f' f g}` variables with the displayed sources and targets. Exact. |
| Cartesian square, with f proper | `sq : ChosenCartesianSquare g' f' f g`, `[IsProper f]`. I opened the structure: its chosen pullback iso respects both projections. Exact. |
| Commutative Noetherian adic ring, finitely generated ideal, torsion A/I, finite perfect positive quotients | `{A : Type (t + 1)} [CommRing A]`, `d : ProEtaleAdicCoefficientDatum A`. I read its extension of `CompleteCoefficientDatum`: `noetherian`, `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`, and `quotientFinite` are the required hypotheses. Exact; no field or nonzero condition. |
| A chosen finite generating list of I | `r : ℕ`, `a : Fin r → A`, `ha : Ideal.span (Set.range a) = d.ideal`. This presents the finitely generated ideal for the recorded Koszul-completion predicate. Exact. |
| K in the ordinary unbounded derived category over the completed ring sheaf on X, derived I-complete | `K : fourCornerDerived X (adicDatumRing X d)` and `hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC`. I opened `adicDatumRing`, `adicDatumReduction`, and the intrinsic predicate: they use the actual inverse limit and invertibility of its specified completion unit. `C` and `eC : DerivedCategory.Q.obj C ≅ K` present the same K and impose no boundedness assumption. Exact. |
| Positive finite levels | `(n : ℕ)` and `fourArrowQuotient d n = A ⧸ d.ideal ^ (n + 1)`. This is a bijective reindexing of n ≥ 1. Exact. |
| Retained etale origins at every level, with no common bound or interlevel witness compatibility | `W`, `w`, `e` quantify over every natural index. `W n` is bounded below; I opened `EtaleOriginWitness`, whose fields are the bounded-below etale object `L` and its `alpha` iso. `e n` is the iso from the normalized finite coefficient transport to the actual reduction of K. Exact. |
| A_n | First corner: finite `g` pullback of reduction of integral `f` direct image of K. The actual tuple definition is precisely this formula. Exact. |
| B_n | Second corner: finite `g` pullback of finite `f` direct image of reduction of K. Exact. |
| C_n | Third corner: reduction of integral `f'` direct image of ordinary `g'` pullback of K. Exact; the pullback is uncompleted. |
| D_n | Fourth corner: finite `f'` direct image of finite `g'` pullback of reduction of K. Exact. All four lie over the same finite ring sheaf on Y'. |
| h_n | Arrow projection `.1.hom`: finite `g` maps the actual `fourArrowProjectionIso f d K n`. `fourArrowProjection` is explicitly the finite adjunction applied to chi followed by scalar reduction of the integral counit. Exact canonical projection map. |
| h'_n | Arrow projection `.2.1.hom`: projection for `f'` and E, followed by finite direct image of the specified `fourCornerEReductionIso`. Exact, including delta and its direction. |
| v_n | Arrow projection `.2.2.1`: `fourArrowReductionPullback g` followed by reduction of the actual integral `proEtaleAmbientRingedExchange` component. Exact, and no invertibility is assumed. |
| v'_n | Arrow projection `.2.2.2.hom`: `asIso` of `fourArrowFiniteExchange`. Its forward morphism is defined before and independently of W, w, e. Their only use is `fourArrowFiniteExchange_isIso`. Exact canonical finite exchange. |
| Every n, equality of the two routes | The theorem ends with `.1.hom ≫ .2.2.2.hom = .2.2.1 ≫ .2.1.hom`, using the same full four-arrow expression each time. Lean composition order therefore states exactly v'_n h_n = h'_n v_n. Exact, without a commutativity input. |

Source check: the shared clone has no Stacks `.tex` files. I obtained the official
`sites-cohomology.tex` and `proetale.tex` into this sandbox's `scratchpad/` and read
`remark-compatible-with-diagram` (0E48), the preceding projection-formula section
and `equation-projection-formula-map` (0B56), `remark-base-change` (07A7), and
`theorem-proper-base-change` (09C9). I also opened the public tag pages:
[0E48](https://stacks.math.columbia.edu/tag/0E48),
[0B56](https://stacks.math.columbia.edu/tag/0B56),
[07A7](https://stacks.math.columbia.edu/tag/07A7).
The general compatibility has arbitrary unbounded complexes and no properness or
completeness condition. This node intentionally specializes it to the inherited
adic datum and four-arrow construction. No additional source-wide hypothesis is
missing. The finite proper base-change application uses the retained etale origin
and its boundedness, not a claim for arbitrary pro-etale objects.

Dependency-module reading (H12/H13): there are no new nodes. I checked all three
dependency node records and their full modules, including the actual definitions,
not merely their primary names. `def-weil-pbc-four-corners` constructs the four
objects directly. Its coefficient comparisons use the fixed profinite comparison,
compatible with projections, transitions, identity and composition. Its ordinary
comparison is the adjunction conjugate of the identity on direct-image sections;
the derived comparison is uniquely normalized on every flat K-flat representative.
Thus the existence choices determine canonical data; none chooses an arbitrary
iso from a bare existence claim. `def-weil-pbc-four-arrows` defines exactly the four
formulas in its node, including the specified finite adjunction and delta.
`thm-weil-pbc-finite-level-proetale` states the finite commutative-coefficient theorem
on the actual canonical ringed exchange, transporting the existing origin witness
through `adicDatumFiniteCoefficientIso`; its map has no witness argument. These
are the required dependency interfaces, with the reasons for supplying them in
`lean.note`. I checked the current shared records: the two definition nodes still
have no published Lean record. The finite-theorem legacy interface is the one
whose incompatible imports the worker recorded. The new ring-sheaf presentation
retains its mathematics. The source wrapper also confirms that
`Sheaf.Paper.PerfectProjectionFormula` is not yet available; its pending Q13 source
is proof material, not an additional object needed to type this rectangle.

Edge cases: `n = 0` is exponent one, so there is no accidental exponent-zero
quotient or omitted first level. The generator index `Fin r` is empty at r = 0;
`ha` then enforces I = 0. Zero K, zero coefficients, the zero ring, empty schemes,
identity squares, arbitrary characteristic and non-Noetherian schemes are not
excluded. No positivity of r, field hypothesis, nonempty scheme, bounded integral
K, common lower bound for the W n, or compatibility between w n is introduced.
The schemes have arbitrary universe t; coefficients and module carriers use t+1,
and the existing small site retains object universe t+1 and morphism universe t.
No extra equality between site universes or index universe restriction is used.

Independent duplicate searches, with query digests in `searches.jsonl`:

- LeanSearch through msearch: “The canonical projection formula morphism is
  compatible with base change for a commutative square of ringed topoi”. The
  service returned Internal Server Error; this is recorded as unavailable,
  rather than evidence of absence.
- LeanFinder through msearch: “Projection formula morphism compatible with base
  change commutative square derived tensor ringed topoi”. Eight ordinary
  scheme-pullback/tensor results, none the derived finite-level rectangle.
- Loogle through msearch: `"baseChange"` returned twelve module/linear-map
  extension-of-scalars results. An earlier two-string query was invalid and was
  replaced by this valid query; its zero hits were not used as evidence.
- Mathlib grep through msearch: `projection.*exchange|exchange.*projection|finite.*rectangle`
  returned four measure-theory rectangle comments, no matching declaration.
- Independent rg over upstream `WeilConjectures/`, shared `lean/Sheaf/`, and
  Mathlib for `rectangle`, exchange/projection, base-change/projection, and
  the item and helper names. I opened
  `Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap` and its
  compactification variant: their etale fixed coefficients, lower-shriek
  operations and ambient tensor targets differ from the quotient-linear
  pro-etale four-corner theorem. They are not this statement. The shared
  `proEtaleProjectionFormula_baseChange` is the general proof ingredient; I
  read its complete signature and its source and target comparisons. No exact
  existing finite-coefficient rectangle was found.

Mismatch found and repaired: the supplied four-arrows node omitted its helpers
from `lean.declarations`, although its module exposes fourteen named declarations.
I recorded all fourteen, including the main definition. No Lean term, signature,
mathematical statement, dependency list or docstring needed correction. Each
module has its source/blueprint docstrings; the item's two proof steps identify
the specified maps and then apply the general compatibility. All postponed
properties are named theorems with `sorry` and source/proof docstrings; definitions
have real data or uniquely characterized construction choices. Every theorem
proof remains `sorry`. I checked every node's `lean.statement` is a verbatim
substring of its module and every delivered Lean line has at most 100 characters.

Second-reader validation: the prescribed four-file scompile run exited zero.
The local attempt encountered a disappearing shared-cache artifact; the wrapper's
authorized server confirmation then compiled all four delivered modules and their
current dependency overlay, each separately at nice 19, two threads, 60 seconds.
The server confirmation reported no Lean errors or warnings. No timeout was raised
and no global build was run.

Concurrent-landing update: after the successful four-module dry run, the push
attempt's preflight detected that Q06's four-corners module had landed in the
meantime. I reopened its current node and obtained the current module using
`scompile.py --source`. The published source is byte-for-byte identical to the
four-corners module audited above. I removed the redundant four-corners module
and node copy from this delivery, preserving them only in scratchpad. The final
delivery now imports the landed `Sheaf.Paper.ProperBaseChangeFourCorners` and
leaves its node's published Lean record intact; the mathematical audit above
applies verbatim. The remaining dependency modules are the four-arrows and finite
ringed base-change modules. No mathematical signature changes were needed.
