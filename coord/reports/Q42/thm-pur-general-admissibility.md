## Worker report

The delivery states `WeilConjectures.PurityFiniteSetting.general_admissibility` in `lean/Sheaf/Paper/PurityGeneralAdmissibility.lean`. It formalizes the source's two preservation clauses with an explicit finite chart cover `C`, chart constants `cU`, and the open-complement hypothesis `hC`. The first conjunct maps finite-torsion constructible cohomological interval `[a,b]` on `Y` to `[a-2D,b-2D+c]` on `X`; the second maps finite-Tor constructible objects with Tor interval `[a,b]` to the same shifted interval and preserves finite-Tor constructibility.

The chart cover notion is supplied in `Sheaf.Paper.PurityAffineChartCover`: `PurityAffineChartCover` binds the finite affine base cover, finite affine chart covers, closed immersions into `AffineSpace`, the projection factorization, and the complements. `maxEmbeddingDimension` renders `D`; `preservationConstant` renders `c`; `openComplementConditions` renders the chartwise condition at the coefficient ring. The empty-family behavior is the `Finset.univ.sup` default `0`, as required by the source.

For the theorem hypotheses: the fixed purity setting is `P : PurityFiniteSetting`; finite-type-over-`k` structure maps are the `Over`, `LocallyOfFiniteType`, and `QuasiCompact` binders on `X` and `Y`; `f.IsOver`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` render the separated finite-type `k`-morphism; `C`, `cU`, and `hC` render the chosen charts and open-complement constants; `a b : ℤ` and `hab : a ≤ b` render the interval bounds. The first conclusion uses `finiteTorsionConstructibleIn` and the transported `P.exceptionalInverseImage`; the second uses `finiteTorConstructible`, `HasProEtaleTorAmplitude`, and the same exceptional inverse image. Integer casts and subtraction render the displayed signed bounds exactly.

Dependency declarations used: `WeilConjectures.PurityFiniteSetting` and `coefficientPrime_isUnit_stalk` from `Sheaf.Paper.PurityFiniteSetting`; `AlgebraicGeometry.Scheme.sfIntrinsicExceptionalInverseImage` and `WeilConjectures.PurityFiniteSetting.exceptionalInverseImage` from `Sheaf.Paper.ConstructibleExceptionalInverseImage`; `AlgebraicGeometry.Scheme.finiteTorsionConstructibleIn` from `Sheaf.Paper.ConstructibleIntervals`; `WeilConjectures.finiteTorConstructible` and `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` from `Sheaf.Paper.FiniteTorAmplitude`/the pro-etale Tor module; `AlgebraicGeometry.Scheme.HasOpenComplementCondition` from `Sheaf.AlgebraicGeometry.OpenComplementCondition`; and Mathlib's `AlgebraicGeometry.AffineSpace`, `IsAffineOpen`, `IsClosedImmersion`, `QuasiCompact`, and `Finset.sup`.

Edge cases checked: `Fin 0` chart families make both finite suprema zero; `embeddingDimension = 0` uses `AffineSpace (ULift (Fin 0))`, whose projection is the canonical zero-dimensional affine-space map; and the theorem's interval casts remain well typed for negative `a` and `b`. The source's empty-source convention is represented by the zero supremum defaults.

Searches made: `msearch.py Q42 thm-pur-general-admissibility leanfinder "finite affine chart cover closed immersion relative affine space"` (eight generic affine-cover hits, none with the closed presentations); `msearch.py ... loogle "AffineSpace, IsAffineOpen, IsClosedImmersion, QuasiCompact, Finset.sup"` (zero hits; the service reported unknown identifier `AffineSpace`); grep/`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` for `PurityAffineChartCover`, `maxEmbeddingDimension`, `preservationConstant`, `finiteExceptionalInverseImage`, and `general_admissibility` (the chart bundle was absent; the exceptional transport existed only in an unusable unstated dependency interface). The initial four-module packet compiled cleanly through `scompile.py`. The final dry run recompiles the revised files and runs the server preflight.

## New nodes

`def-pur-affine-chart-cover` is a new definition node because no existing node, Mathlib declaration, or project declaration bundles the finite affine covers, closed affine-space presentations, complements, and maxima required by the source theorem. Its source is the affine-chart choice paragraph of `thm-pur-general-admissibility`; its component searches are recorded in the node's `mathlib_searches`.

## Dependency modules

Maintainer correction for landing at immutable head 3d2a3c907ec1: the parent already
records `Scheme.finiteExceptionalInverseImage` in `Sheaf.Paper.FiniteExceptionalInverseImage`.
It uses intrinsic constant-ring modules and is usable with the theorem's hypotheses.
The earlier descriptions below of a fixed-scalar-only recorded interface describe an
older base and are superseded by this correction. The fixed
`ConstructibleExceptionalInverseImage.lean` imports and transparently aliases that
published functor. It no longer repeats its realization, inverse realization or
exceptional composite. `sfIntrinsicExceptionalInverseImage` is a compatibility alias
at positive quotient coefficients; `PurityFiniteSetting.exceptionalInverseImage` is
its setting specialization, and the two finite instances remain actual constructions.
The module's refitted record takes its new signature and declaration list from this
replacement file. The historical `lean.note` about the older legacy import is not a
claim that the parent commit's intrinsic declaration is unusable.

The interval dependency's snapshot record names the fixed-scalar upstream
`constructibleIn`. This theorem uses the already published intrinsic counterpart
`Scheme.finiteTorsionConstructibleIn` from `Sheaf.Paper.ConstructibleIntervals`.
Both were independently opened: bounded constructibility and inclusive cohomological
vanishing are the same notion under the canonical finite-coefficient equivalence.
The theorem introduces no private interval definition. The intrinsic predicate is
used directly because the intrinsic Tor predicate and exceptional output have that
presentation; the local-unit theorem supplies its source-implied invertibility argument.


`def-weil-finite-tor-amplitude`: this earlier record-only repair is now already on
the current base (NW). The second reader verified its intrinsic `finiteTorConstructible`
declaration and removed the redundant sandbox node copy. This delivery simply imports
`Sheaf.Paper.FiniteTorAmplitude`; it does not overwrite the landed dependency record.

`def-pur-conventions`: the recorded module did not expose the source-implied local-unit witness needed by the existing interval declaration. The delivery preserves the setting and adds the named theorem `PurityFiniteSetting.coefficientPrime_isUnit_stalk`.

`def-weil-exceptional-inverse-image`: the current recorded fixed-scalar exceptional declaration cannot be imported alongside the intrinsic finite-coefficient framework (the duplicate UpperLowerStar declaration reported in return L). The delivery supplies `sfIntrinsicExceptionalInverseImage` and its `PurityFiniteSetting.exceptionalInverseImage` specialization, the finite coefficient comparison transport of the ordinary etale exceptional adjoint used by the theorem.

The original master blueprint theorem and its `_section.md` are available under the read-only
`/home/ubuntu/work-bp/sheaf/literature/` mirror. I read both: their finite-type k-scheme setting,
affine-chart choice, open-complement constants and both bounds agree with the current DAG.
The DAG already makes the empty-chart convention explicit; no statement correction is needed.

The chart fields map each choice literally: `baseOpen`, `base_affine`, `base_cover` are the
finite affine cover of Y; `chartOpen`, `chart_affine`, `chart_contained`, `chart_cover` are the
finite affine covers of the inverse images; `embeddingDimension`, `embedding`,
`embedding_closed`, `embedding_over` are the natural dimensions, closed presentations, and
projection factorization. Equality after the base inclusion is equivalent to equality in V
because that open immersion is a monomorphism. `complement_eq` fixes the open complement
exactly. `complement_quasiCompact` is the condition required by the recorded complement
predicate and holds automatically for these Noetherian affine spaces. Empty chart opens
are permitted; they are not silently removed, and their dimensions still enter the maxima.
A nonempty chart family on an empty X is allowed and uses the stated maxima, whereas a
truly empty chart family gives D=c=0.

The coefficient carrier in the complement condition is `P.Coefficient = ULift P.Ring`,
the standard site-size lift. The exceptional construction uses this same lifted carrier
and the canonical intrinsic constant-ring equivalence to return to `P.Ring` modules.
The two coefficient presentations encode precisely the same ring and sheaves; no new
coefficient action or arbitrary comparison map is supplied.

The second semantic search for exceptional inverse-image constructibility and Tor bounds
returned eight unrelated affine-limit/cohomological-support declarations. LeanSearch for
the chart bundle returned `Internal Server Error`; this is recorded as unavailable, not
as mathematical evidence. The successful exact grep over Mathlib's AlgebraicGeometry
returned no chart-bundle names. The corresponding grep over the upstream and shared
side sources also returned no matches. `tools/blueprint_refs.py search 'affine chart'`
returned uses of charts but no prior chart-cover definition. Full real query records are
in `searches.jsonl` and in the new node's `mathlib_searches`.

All nine natural-language proof steps are preserved in the theorem docstring. All stated
proof-dependency modules identified in the current DAG are imported without `public`;
statement dependencies are public imports. The only new sorries are
`PurityFiniteSetting.general_admissibility` and the source-implied
`PurityFiniteSetting.coefficientPrime_isUnit_stalk`; the previously recorded convention
module retains its existing postponed theorems. Definitions contain actual data.

## Earlier second reading (a previous round; superseded)

I independently read the sandbox node and all four modules, the seven original
statement-dependency nodes, and the new `def-pur-affine-chart-cover` node. I read the
original theorem and its unit `_section.md` from the read-only
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-six-functors/`
`sk-prop-sf-rf-shriek-preservation/` mirror. The source throughout assumes finite-type
schemes over the fixed algebraic closure of the finite field; it does not assume
separatedness of X or Y individually. The current DAG makes the transported adjoint,
the source restriction in open base change, and the empty-chart convention explicit.
These agree with the source's intended statement, so no statement correction is needed.
I also read the Stacks .tex for Tags 08FZ (`sites-cohomology.tex`,
`definition-tor-amplitude`) and 09AK (`proetale.tex`, `lemma-compare-constructible`):
the former tests every module sheaf, and the latter assumes a Noetherian coefficient
ring (automatic for this finite quotient), with no extra regularity on schemes.

The statement checklist and its exact Lean rendering are:

| Node object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| The fixed finite field and its algebraic closure k | `P.field : FiniteFieldDatum`; I opened `FiniteFieldFiber.lean`: prime p, positive a, q=p^a, the cardinality of k0, and `IsAlgClosure k0 k` are all fields of the recorded structure. Correct. |
| Prime ell distinct from characteristic k, finite E in its fixed algebraic closure, positive n, and A=O_E/(varpi^n) | `P.coefficients`, `P.extension`, `P.finiteExtension`, `P.level`, and `P.level_pos`; `P.Ring` is exactly `Padic.coefficientExtensionRing`. `CoefficientDatum.different` is ell≠p. Correct, including ramified finite extensions and every positive level. |
| X,Y finite-type k-schemes | The two `Over (Spec (.of P.field.k))` instances and each structure morphism's `LocallyOfFiniteType` and `QuasiCompact` instances. Correct; no separatedness or smoothness on the schemes is added. |
| f a separated finite-type k-morphism | `(f : X ⟶ Y)`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, and `QuasiCompact f`. Correct. These are the Mathlib notions selected by the collection dependency. |
| The actual constructible exceptional inverse image | `(P.exceptionalInverseImage f).obj K`; it obtains compactification by Nagata from the finite-type field-base hypotheses, and finiteness from the recorded quotient theorem. It conjugates the published etale adjoint and canonical comparison functors by the recorded coefficient equivalence, spelling out the comparison composite because the packaged pro-etale functor has incompatible imports. Correct; no unrestricted pro-etale adjoint hypothesis or assumed constructible-preservation property. |
| Finite affine cover V of Y | `C.baseCount`, `baseOpen`, `base_affine`, `base_cover`. Natural finite indexing represents any finite family by reindexing. Correct. |
| Finite affine covers U of each preimage of V | `chartCount`, `chartOpen`, `chart_affine`, `chart_contained`, `chart_cover`. Correct; both containment and coverage are required. |
| Natural d_U and closed immersions into the actual affine spaces | `embeddingDimension`, `embedding` into `AffineSpace (ULift (Fin d)) V`, and `embedding_closed`. I opened Mathlib `AffineSpace`: its definition is the stated pullback of the integral polynomial model. Correct. |
| U→V factors through the affine-space projection | `embedding_over`. Equality after composition with `V.ι` is equivalent to the equality over V because `V.ι` is monic. Correct. |
| The specified complement W_U | `complement` and `complement_eq`, whose set is the complement of the range of the same embedding. Correct; an unrelated open or closed subset cannot be substituted. |
| Each complement inclusion is quasi-compact | `complement_quasiCompact`; this is already required by `HasOpenComplementCondition`, and also follows here because the affine spaces over the finite-type field base are Noetherian. No extra mathematical hypothesis. |
| Nonnegative constants c_U and the two-clause etale complement condition at A | `cU : ... → ℕ` and `hC : C.openComplementConditions P.Coefficient cU`. I opened `OpenComplementCondition.lean`: all module sheaves and every q>c are quantified in the vanishing clause; every constructible sheaf and every integer q in the constructibility clause. Correct. The ULift is the existing coefficient size convention. |
| D=max d_U; c=max(c_U+1+2(D-d_U)); both zero on an empty chart family | `maxEmbeddingDimension` and `preservationConstant` use `Finset.univ.sup` over the dependent finite chart index. Every d_U≤D, so natural subtraction has exactly the displayed signed-integer meaning after casting. Correct. |
| All integers a≤b | `(a b : ℤ) (hab : a ≤ b)`. Correct, with the constants fixed before this quantification. Moving independent universal interval binders before the conjunction is logically equivalent to the two source clauses. |
| Clause 1 has arbitrary bounded constructible input in [a,b] | The first `∀ K, Scheme.finiteTorsionConstructibleIn ... a b hab K → ...`. I read its definition: intrinsic bounded constructibility intersected with cohomology vanishing outside `Set.Icc a b`. Correct; no finite-Tor premise is present. |
| Clause 1 produces constructibility and exactly the shifted interval | The conclusion uses the same predicate on X with `a - 2 * (C.maxEmbeddingDimension : ℤ)` and `b - 2 * ... + (C.preservationConstant cU : ℤ)`. The supplied inequality follows from hab and c≥0. Correct. |
| Clause 2 has finite-Tor constructible input with Tor interval [a,b] | The second `∀ K` has `finiteTorConstructible ... Y K` and `Scheme.HasProEtaleTorAmplitude Y P.Ring K a b`. I opened both definitions; the first is intrinsic bounded constructibility and existence of one finite Tor interval, and the second tests all degree-zero intrinsic module sheaves using K-flat representatives. Correct; etale-origin test sheaves alone are not used. |
| Clause 2 produces bounded constructibility and the displayed Tor bounds | The result is `finiteTorConstructible ... X ((P.exceptionalInverseImage f).obj K) ∧ HasProEtaleTorAmplitude ...` with the identical signed endpoints. Correct. |
| In particular the functor preserves D^b_ctf | The explicit `finiteTorConstructible ... X` conclusion gives this after taking any interval witnessing finite Tor amplitude of the input. Such an ordered interval is part of the opened definition. Correct; no choice of a fixed uniform interval for all K is imposed. |

I checked the dependency modules as well. `PurityFiniteSetting.lean` preserves the
landed structure and its existing declarations; its only new theorem,
`coefficientPrime_isUnit_stalk`, expresses the unit image of ell along the structure
map. Its proof docstring explains characteristic p, nonzero ell in k, and preservation
of units; it replaces an extra invertibility assumption with the source consequence.
The exceptional module supplies the intrinsic coefficient-presentation interface
missing from the recorded node. Its equivalence inverse is the inverse of the
specified realization functor, whose unit determines the action; it is not an arbitrary
`Nonempty` choice. The finite quotient instances call the existing finiteness theorem.
The final exceptional composite reuses the existing etale adjoint and comparison functors; the packaged pro-etale declaration cannot be imported with the required finite coefficient framework, as checked below. All of its data
are real constructions. The other coefficient stages mentioned by the convention node
remain the existing imported operations and are not used or replaced by this finite
coefficient statement.

For the new definition node I checked its source paragraph, every field and every
Lean declaration. It packages exactly the chosen finite charts, closed presentations,
complements, maxima, and the existing complement predicate. The node is in the item's
chapter and unit, cites precisely its three component notions, has empty proof fields,
null mathlib match, three search kinds, the creation record, blueprint ancestry,
none audits, and its own Lean module. The item's `stmt_deps` cites it. Generic Mathlib
affine covers alone do not package the presentations, complements or maxima, so this
is not another definition of Mathlib's affine cover notion.

Edge cases: `baseCount=0` forces Y empty by `base_cover` and then X empty. A nonempty
base family with every `chartCount=0` also forces X empty, and both dependent suprema
are zero. Empty individual chart opens are allowed and still enter the maxima; an
empty X may also have nonempty chart families, exactly as in the node. No nonempty
instance excludes these cases. For d_U=0, the index of the affine space is the lifted
empty type and the canonical projection is the zero-dimensional affine-space
isomorphism. Negative a,b and a=b are allowed. The zero derived object is not excluded.
The n=0 case is excluded precisely by the source's n≥1, and every allowed coefficient
characteristic is retained. The single universe u is the existing scheme/coefficient
size convention; every finite coefficient field extension and finite chart family can
be placed at that level. The small site keeps object universe u+1 and morphism
universe u, while module carriers use u+1. No independent smaller testing universe or
extra equality of site universes was introduced. `autoImplicit false` and the clean
compiles confirm all binders are explicit.

Independent searches (in addition to the author's records):

- LeanFinder through `msearch.py`, query `exceptional pullback preserves bounded
  constructible complexes finite Tor dimension with affine chart bounds`: eight
  morphism-property/pullback results; none states this preservation theorem.
- Loogle through `msearch.py`, query `"AffineCover"`: twelve component-cover hits.
  I opened `Mathlib.AlgebraicGeometry.Cover.MorphismProperty`, lines 189ff; its
  `AffineCover` has rings, maps, covering and map property, with none of the closed
  presentations or complement constants. It is not the new bundled notion.
- LeanSearch through `msearch.py`, query `Finite affine open coverings with closed
  immersions in relative affine spaces and open complements`: unavailable with
  Internal Server Error; this is not evidence for absence.
- `rg` across Mathlib, slopmaster2 `WeilConjectures`, and the shared `lean/Sheaf`
  for `affine.*chart.*cover|general_admissibility|PurityAffineChartCover|preservationConstant`
  found no exact statement or chart bundle; other chart-cover comments concern
  blowups/descent. Searching `admissib`, `ChartPresentation`, `Exceptional`, and
  `UpperShriek` led to the published pro-etale transported functor, which I opened.
  I also opened the etale `exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`:
  it is on the other site, combines a Tor premise with its cohomological premise,
  and existentially forgets the chart constants; it is not an exact existing match.
  The condensed module-object exceptional functor uses another coefficient category.
- Current-source checks with `scompile.py --source` found no published
  `Sheaf.Paper.PurityAffineChartBounds` or
  `Sheaf.Paper.ConstructibleExceptionalInverseImage` to reuse; older unpublished
  sandboxes are not imports. The canonical realization and its inverse already
  exist in the recorded dependency and are used directly.

Mismatches repaired: (1) the chart module's module docstring lacked the required
`#` heading; (2) the item and exceptional node signatures were whitespace normalized
rather than verbatim, so their records now retain the multiline file signatures.
I also tested replacing the explicit comparison composite by the published
`ProEtale.rightDerivedUpperShriek`. Compilation diagnosed an incompatible import:
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` and the required
`FiniteCoefficient.UpperLowerStar.Defs` both declare
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. I restored the correctly typed original
composite rather than introduce the conflicting API. This justifies the dependency
transport interface and is recorded in its `lean.note`. No mathematical hypothesis, conclusion, node statement, proof, or proof
dependency was changed. All nine proof steps remain in the statement docstring.
Every theorem body remains `sorry`; definitions have no postponed data, local notation,
private duplicate, or extra axioms. All four original constructions compiled individually and cleanly with `scompile.py`.
The incompatible-import experiment was reverted. The required delivery dry run
recompiles and checks the final packet, including the corrected header and records.

## Repair of return L (immutable head 070f518fecb9)

The returned duplicate `AlgebraicGeometry.ProEtale.«term(_)_*[_]»` is an import
collision between the legacy and finite-coefficient UpperLowerStar modules. I read
the current server source of `Sheaf.Paper.FiniteTypeExceptionalInverseImage` with
`scompile.py --source`: it imports the legacy derived exceptional functor and returns
fixed-scalar module sheaves. The theorem's constructible intervals instead use
intrinsic modules over the constant ring sheaf. I retain the canonical intrinsic
comparison composite in `ConstructibleExceptionalInverseImage`, rather than import
the incompatible legacy exceptional module. Its inverse realization now imports
`ProEtaleFiniteModuleIntrinsicComparison` directly and uses the specified realization's
`asEquivalence.inverse`; it no longer imports the unrelated extension-by-zero module.
This inverse is definitionally the inverse previously obtained through
`sfIntrinsicModuleEquivalence`, with the very same equivalence instance from
`finiteCoefficientIntrinsicRealization_exact`. All theorem signatures, hypotheses,
conclusions, chart definitions and nine proof steps are unchanged.

The current `def-weil-finite-tor-amplitude` record was also changed to the legacy
fixed-scalar presentation after the original delivery. Its lean-only dependency
repair records the already existing `WeilConjectures.finiteTorConstructible` from
`Sheaf.Paper.FiniteTorAmplitude`, used verbatim by this theorem and checked against
the server source. That declaration is intrinsic bounded constructibility intersected
with existence of a Tor interval against all module sheaves. No new module or
private Tor predicate is needed; the integral and field declarations remain available.

Validation for the repair is recorded below after compiling every delivered module
and running `deliver2.py Q42 thm-pur-general-admissibility --no-push`. No delivery
is pushed by this worker.

Repair validation: `scompile.py Q42 thm-pur-general-admissibility` compiled all four
delivered modules successfully with no errors or unexpected warnings. The canonical
exceptional module and the main theorem both passed separately as importable modules.

The first repair dry run passed every compilation and declaration probe. Preflight
requested that the Tor dependency explanation appear in the original exact
`## Dependency modules` section; that report layout is repaired for the next dry run.

## Second reading by Q42

I read the current DAG node against the original master blueprint theorem (order
2078), its preservation-unit `_section.md`, and Stacks sources `sites-cohomology.tex`
Definition `definition-tor-amplitude` (08FZ) and `proetale.tex` Lemma
`lemma-compare-constructible` (09AK), in the read-only work-bp literature mirror.
The unit fixes finite-type schemes over the algebraic closure of the finite field;
it does not assume that either scheme is separated over the field. The current DAG
already repairs the source's ill-typed abbreviated open-base-change formula and
specifies the empty-chart case. No further statement correction is needed.

Here is my object/hypothesis/conclusion checklist, read with the declarations open:

| Node item | Lean rendering and verdict |
| --- | --- |
| Fixed finite field and algebraic closure k | `P.field : FiniteFieldDatum` has prime `p`, positive exponent, cardinality `p^a`, and `IsAlgClosure k₀ k`; correct. |
| Prime ell different from characteristic, finite extension E in the fixed coefficient closure, n≥1, A=O_E/(varpi^n) | `P.coefficients.different`, `P.extension`, `P.finiteExtension`, `P.level_pos`, and `P.Ring`; the opened `CoefficientDatum` and quotient definitions give exactly these data. Correct. |
| X,Y finite type over k | `X.Over`, `Y.Over`, with `LocallyOfFiniteType` and `QuasiCompact` for each structure morphism; correct, without extra separatedness, regularity or smoothness. |
| f a separated finite-type k-morphism | `f`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`; correct. The collection node points to the Mathlib component notions used here. |
| The constructible exceptional inverse image | `P.exceptionalInverseImage f` specializes `sfIntrinsicExceptionalInverseImage`; its actual composite is inverse realization, `Rnu_*`, the published etale exceptional adjoint, `nu^*`, and realization. Correct; no ambient pro-etale right adjoint is assumed. |
| Finite affine opens V covering Y | `C.baseCount`, `baseOpen`, `base_affine`, `base_cover`; correct. Every finite family can be indexed by `Fin baseCount`. |
| Finite affine opens U covering each f⁻¹(V) | `chartCount`, `chartOpen`, `chart_affine`, `chart_contained`, `chart_cover`; correct, including both containment and coverage. |
| Natural d_U and closed embeddings U→A^(d_U)_V | `embeddingDimension`, `embedding`, `embedding_closed`; correct. Mathlib `AffineSpace` is the pullback of the polynomial integral model, and `ULift (Fin d)` gives d coordinates. |
| Projection composite equals U→V | `embedding_over`; correct. Equality after composing with `V.ι` is equivalent to equality over V because the open immersion is monic. |
| W_U is exactly the complement of this embedding | `complement`, `complement_eq`; correct. `complement_quasiCompact` supplies the recorded complement predicate's condition, automatic here for the Noetherian affine-space targets. |
| Nonnegative c_U and both etale open-complement conditions | `cU : ... → ℕ`, `hC : C.openComplementConditions P.Coefficient cU`; correct. The opened predicate quantifies over all module sheaves for vanishing and over all constructible module sheaves for degreewise constructibility. |
| D=max d_U and c=max(c_U+1+2(D-d_U)), zero for no charts | `maxEmbeddingDimension`, `preservationConstant`, each an actual `Finset.univ.sup` over the dependent finite chart index; correct. Since d_U≤D, natural subtraction agrees with the displayed integer difference. |
| Every integer interval a≤b | `a b : ℤ`, `hab : a ≤ b`, after the chart constants; correct. Combining the two universally quantified clauses as a conjunction at each interval is logically equivalent. |
| First input: arbitrary bounded constructible L in [a,b] | First conjunct's `∀ K`, `finiteTorsionConstructibleIn ... a b hab K`; correct. The opened predicate is intrinsic bounded constructibility and homology vanishing outside `Set.Icc a b`, with no Tor assumption. |
| First output: constructible interval [a−2D,b−2D+c] | The same predicate on X and `((P.exceptionalInverseImage f).obj K)`, with precisely these signed endpoints; correct. The proof term supplied to its order argument is a consequence of hab and c≥0. |
| Second input: K in Dᵇ_ctf with Tor amplitude [a,b] | Second conjunct's `finiteTorConstructible ... Y K` and `HasProEtaleTorAmplitude ... a b`; correct. The former intersects intrinsic constructibility with existence of a finite Tor interval; the latter includes a≤b and tests all degree-zero module sheaves on all K-flat representatives. |
| Second output: bounded constructibility and the shifted Tor interval | `finiteTorConstructible ... X ... ∧ HasProEtaleTorAmplitude ... (a−2D) (b−2D+c)`; correct. The first conjunct is equivalent to bounded constructibility here because the second explicitly supplies finite Tor amplitude. |
| In particular Dᵇ_ctf preservation | Taking the interval witnessing the input's finite Tor amplitude in the second clause gives this assertion; correct, without an additional choice or assumption. |

I independently opened every delivered dependency module. `PurityFiniteSetting`
preserves the actual finite setting and adds only the local-unit theorem for ell.
Its proof docstring derives the unit from characteristic p, ell≠p and the structure
map. `ConstructibleExceptionalInverseImage` uses the existing canonical
`finiteCoefficientIntrinsicRealization`, whose scalar map is the constant-sheaf
unit. Its inverse is the inverse of that specified equivalence, not an arbitrary
map or a bare `Nonempty` choice. Nagata supplies compactification using the finite-type
field base. The finite quotient theorem supplies the finite instances. The existing
fixed-scalar exceptional module is unusable for this intrinsic coefficient category
and has the documented legacy/finite-coefficient notation collision; the delivered
transport supplies precisely the finite-level part needed here. The higher coefficient
constructions are not redefined. The finite-Tor dependency reuses the already published
intrinsic `finiteTorConstructible` and introduces no private Tor predicate.

I read the new `def-pur-affine-chart-cover` as a stage-1 definition node. Its source
paragraph introduces exactly the finite covers, closed presentations, complements
and maxima packaged by its four Lean declarations. It has the required source,
ancestry, creation record, empty proof fields, null Mathlib match, three search
kinds, none audits and matching chapter/unit. Its component dependencies are exactly
the three cited notions. A generic Mathlib affine cover has no closed presentations,
complements or maxima, so this bundle does not duplicate that notion. The item cites it.

Edge cases: an empty base index forces Y empty and hence X empty; an empty dependent
chart index forces X empty, with both suprema zero. Empty chart opens are allowed,
including nonempty chart families on empty X, and their dimensions still enter the
maxima. For d_U=0, `ULift (Fin 0)` gives the canonical zero-dimensional affine space.
No zero derived object is excluded. All negative endpoints and a=b are allowed.
The case n=0 is excluded precisely by the source's positive level, while all allowed
characteristics and ramified coefficient extensions remain present. The single
universe u is the established scheme/coefficient size convention: small pro-etale
objects have universe u+1 and morphisms universe u; module carriers use u+1. No
independent smaller test universe or extra equality of site universes occurs.

Fresh independent searches in this reading:

- LeanFinder via `msearch.py`: `exceptional inverse image preserves constructible
  complexes explicit cohomological bounds affine charts` returned eight generic
  affine-limit and homology-support results, no exact theorem.
- Loogle via `msearch.py`: `"AffineSpace"` returned the genuine Mathlib affine-space
  definition and its component declarations, which I opened; none is the chart bundle.
- LeanSearch via `msearch.py`: `finite covers by affine opens with embeddings into
  affine spaces and exceptional pullback bounds` succeeded with eight affine-cover
  component results. I opened Mathlib `AffineCover` fields at lines 196–208; these
  lack the closed presentations, complements and maxima. Earlier service failures
  therefore are not the sole search evidence.
- `rg` across Mathlib, slopmaster2 `WeilConjectures`, and shared `lean/Sheaf` using
  `preserv.*Shriek`, `Shriek.*preserv`, `constructibleTorAmplitudeIn_rightDerived`,
  `PurityAffineChartCover`, and the maxima names found the etale stability theorems.
  I opened `exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek` and
  `boundedConstructible_rightDerivedUpperShriek`: the former has a Tor premise and
  existential symmetric bounds, and the latter has no chart bounds. Neither states
  these two pro-etale intrinsic clauses. DAG searches found uses of chart arguments
  but no existing node for the bundled chart data.

Mismatches found and repaired in this reading: two dependency copies retained stale
`reviewed_lean` metadata after concurrent landings. I restored every non-`lean` field
from the current read-only node records, as H2 requires. No Lean declaration, node
mathematical statement, hypothesis, conclusion or proof step needed changing.
All four module signatures recorded in the nodes are verbatim substrings of their
files. All nine proof steps remain in the theorem docstring; definitions contain real
data, all theorem bodies remain `sorry`, and every delivered line is at most 100
characters. Validation evidence follows below after the final wrappers finish.

A further current-base check found that NW has already landed exactly the intrinsic
finite-Tor record required here. I removed our redundant record-only dependency copy
rather than overwrite NW's complete declaration list and metadata. The dependency
module paragraphs above now identify this as an already-landed repair. Thus the final
packet changes only two dependency nodes, each solely in its `lean` record.

I also corrected three exceptional-dependency source citations from blueprint order
1467 to its actual node order 1489. Declaration signatures and constructions are
unchanged; the final dry run compiles the files with these corrected docstrings.

Validation: `scompile.py Q42 thm-pur-general-admissibility` completed successfully
for all four modules, individually in sandbox and library form, with no errors or
warnings. The transcript is `scratchpad/second-reading-compile.log`. The final
delivery dry run also compiles the corrected source-citation docstrings and checks
the records and report against current server preflight.

Final dry run: `deliver2.py Q42 thm-pur-general-admissibility --no-push` printed
`OK (dry run): commit c7ccad7267 passes the preflight and compiles; nothing pushed`.
The wrapper preserved a concurrently updated dependency `reviewed_lean` field from
the server; that reviewer metadata is not part of this delivery. Transcript:
`scratchpad/second-reading-dry-run.log`. The second reader proceeds with the
prescribed delivery wrapper.


## Maintainer landing corrections

The independent immutable review found no mathematical mismatch in the two clauses,
the chart maxima, or their quantifiers. It replaced the redundant exceptional composite
by transparent aliases to the usable recorded intrinsic construction, correcting the
stale interface account above. It also added the chart module's main-definition list.
The theorem's signature and all nine natural-language proof steps are unchanged.
The narrower specialization alias requires X and Y finite type over the fixed field;
these are already hypotheses of `general_admissibility`, so no theorem assumption changes.

The read-only context also contains `SfAffineChartPresentation` in the downstream
`PurityAffineChartBounds` module. It packages the common cover/presentation data,
but not the specified complements, quasi-compactness witnesses, arbitrary c_U or the
conditional open-complement predicate required here. Its assembly removes empty source
charts, unlike this theorem, which retains them. It is not an exact attachment for
`def-pur-affine-chart-cover` or this conditional theorem; no downstream theorem is used
as a prerequisite of the present statement.

Validation of the immutable originals: scompile.py compiled all four files individually
in sandbox and library forms, exit 0, without diagnostics. The fixed files passed the same wrapper, alongside both unchanged sibling modules,
with exit 0 and no errors or warnings; see review.md for the final timings. No lake build, live Lean write, delivery, merge or Git mutation was run.


The immutable interval dependency record names the fixed-scalar upstream
`ProEtale.DerivedCategory.constructibleIn`, whereas this theorem uses the already
published intrinsic `Scheme.finiteTorsionConstructibleIn` in
`Sheaf.Paper.ConstructibleIntervals`. Both definitions were opened: each is bounded
constructibility intersected with inclusive cohomological vanishing, in the two
canonically equivalent finite-coefficient module presentations. The intrinsic
predicate is reused, not defined by this delivery. The finite-Tor predicate and
exceptional operation in this theorem use that same intrinsic category. This is
not an additional Tor premise in clause (1), nor a change to coefficient rings.
