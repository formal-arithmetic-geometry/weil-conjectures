## Worker report

Q65, 2026-10-22. This is a stage-2 statement delivery, not a proof delivery.
The live item's stage-1 split and maintainer review are retained. They do not
supply a Lean statement; the previous dispatcher's reported stage-1 review is
therefore not a reason to abandon stage 2.

The main module is `Sheaf.Paper.IteratedReturnTransportScalarCalculus`, with
main declaration `WeilConjectures.iteratedReturnTransportScalarCalculus`.
Its definitions construct the iterates I, the actual return comparisons v,
and t = I followed by the point-functor image of v. Its conclusion states
naturality, the two scalar identities, and their unit and tower compatibility.
All helper declarations are recorded in their owning node's `lean.declarations`.
Definitions have real terms; the main theorem has `sorry` and a six-step
natural-language proof.

The source is the final Frobenius-transport sentence of the current blueprint's
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
together with the explicit six-step local-normalization calculation in this
DAG node. The item statement, proof, source, and reviewed stage-1 data are
unchanged. Two definition nodes now own the finite-pullback presentation comparison
and the constructible/rational forms of the normalized comparison family; no mathematical statement correction is needed.

Hypotheses and objects, clause by clause:

- Global finite-field datum: `D : FiniteFieldDatum.{u}` supplies p, a, q,
  k0 and the fixed algebraic closure k. `c : D.CoefficientDatum` supplies
  the prime ell as `c.l`, its prime instance, the fixed Qbar, and
  `c.different : c.l ≠ D.p`.
- The finite coefficient fields in that fixed closure are
  `F G H : Padic.FiniteCoefficientFields c.l c.Qbar`. The actual field E
  is `F.val`; M and the next field are `G.val` and `H.val`.
  `hFG : F ≤ G` and `hGH : G ≤ H` give the actual inclusions through
  `IntermediateField.inclusion`. They cover both identity and successive
  extensions. The third field is a universally quantified tower parameter,
  not an added restriction on the first extension; equality of fields is allowed.
  The recorded coefficient construction supplies its valuation ring,
  uniformizer and `Padic.coefficientExtensionRing l E (n + 1)`.
- `X₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType X₀.hom]`,
  `[QuasiCompact X₀.hom]`, `[IsSeparated X₀.hom]` say separated and finite
  type over k0. The source's X is `(D.geometricFiber X₀).left`, and s is
  `Spec (.of D.k)`.
- The actual Frobenius maps are `(D.geometricFrobenius X₀).hom` and
  `(frobeniusPointIso D).hom`. No arbitrary automorphism replaces them.
- `r : ℕ` represents every positive period m by `r + 1`.
  `z : Over.mk (𝟙 (Spec (.of D.k))) ⟶ D.geometricFiber X₀` is a k-point,
  not merely an unqualified scheme morphism. The equality `w` is
  `g_s^(r+1) ≫ z.left = z.left ≫ g_X^(r+1)`; this is precisely the
  source's equality in Lean's left-to-right composition convention.
- `C : IntegralComparisonSystem c.l` and `_hC :
  IntegralComparisonRealizationCoherence c.l F.val G.val (inclusion hFG) C`
  bind the specified simultaneous normalized comparison family of the
  recorded realization node. They do not replace it by arbitrary isomorphisms.
  That node supplies existence of such a family. All comparisons below
  are constructed from its named formulas, not from the coherence assertion.
- The prime-invertibility instances needed by the recorded pullback API are
  supplied inside `Properties` using `frobeniusPointPrimeInvertible` and
  `sfWeilPrimeInvertible`. They add no assumptions to the theorem.

Conclusions and constructions, clause by clause (helper names below are in
`WeilConjectures.IteratedReturnTransport`):

- `iterate U 0 = 𝟭 _` and `iterate U (j+1) = iterate U j ⋙ U` give U^j.
  `pointIterate` has the actual terms `𝟙 _` at zero and
  `pointIterate ... N j ≫ iota ((iterate U j).obj N)` at the successor.
  `finiteI`, `integralI`, and `rationalI` instantiate this recursion with
  the recorded point transport at the three coefficient stages.
- Finite categories are the recorded intrinsic bounded constructible full
  subcategories; `FiniteNaturality` quantifies over those objects and all
  their morphisms. The equations are written after their fully faithful
  inclusions into the ambient derived module category. This reflects the
  same equality. `n : ℕ` uses the quotient exponent `n+1`, so exactly all
  positive quotient exponents are covered.
- Integral inputs are `sfIntegralConstructibleCategory`; its definition
  includes derived completeness, bounded constructibility and the common
  reduction interval. Rational inputs and all their Hom spaces are those
  of `sfRationalConstructibleCategory`, the raw localization. No Karoubi
  objects or morphisms occur.
- P, U and G are respectively `finiteDerivedPullback`,
  `constructibleIntegralPullback`, or `rationalDerivedPullback` at z, g_s,
  and g_X. The point functors are the recorded finite sections-derived
  functor, `pointIntegralFibre`, and `pointRationalFibre`.
- `powerComparison` iterates the specified compositor. `finiteComposition`
  transports the recorded finite canonical compositor through the recorded
  `pointPowerPullbackModel`; it does not choose a second compositor.
  `finiteReturn`, `integralReturn`, and `rationalReturn` construct v as:
  inverse point-power compositor, inverse composite-map compositor,
  `eqToIso` for w, composite-map compositor along the other side,
  and P applied to the space-power compositor. Thus the middle comparison
  is the given equality of scheme maps, not a free return isomorphism.
- `FiniteNaturality`, `IntegralNaturality`, `RationalNaturality` each have
  two universally quantified clauses. First, for every point morphism f,
  `I_N ≫ B.map ((iterate U m).map f) = B.map f ≫ I_N'`.
  Second, for every space morphism f,
  `t_K ≫ B.map (P.map ((iterate G m).map f)) = B.map (P.map f) ≫ t_K'`.
  These are exactly both requested naturality assertions. The definitions
  of `finiteTransport`, `integralTransport`, `rationalTransport` are
  `I_(P K) ≫ B.map (return K).hom`. Rational f ranges over the whole Hom
  space, not only images of integral maps or pure tensors.
- `scalarIterate` starts at `Iso.refl` and uses
  `alpha_(U^j N) ≪≫ U_M.mapIso (previous)`. The three `*PowerScalar`
  definitions instantiate it with the specified one-step system, integral,
  and rational scalar comparisons. These are delta on s and d on X.
  The uniterated scalar comparison along z is a. The rational comparison
  is the unique natural transformation whose components are localizations
  of the actual normalized integral comparison (definition-owned helper interface below).
- `ReturnScalarEquation` is literally
  `delta_(P K) ≫ U_M^m.map(a_K) ≫ v_M(T_X K) =
  T_s.map(v_E K) ≫ a_(G_E^m K) ≫ P_M.map(d_K)`.
  `SystemScalarEquation`, `IntegralScalarEquation` and
  `RationalScalarEquation` substitute the actual constructions just named.
  `systemReturn` uses `integralComparisonSequencePullback` on whole
  `coefficientSequenceModules` diagrams, before derived localization and
  integral realization. Thus the assertion before realization is present
  as an equality on entire simultaneous diagrams, not only at each level.
- `RationalPointScalarEquation` substitutes the same
  `rationalPowerScalar` at g_s into `PointScalarEquation`. Its beta is
  `((pointRationalFibreScalarIso ...).app N).symm`, the inverse of the
  actual sections comparison. The tensor functor is
  `DerivedCategory.pointFdScalarExtension inclusion.toRingHom`.
  The displayed equation is literally
  `V.map(I_N) ≫ beta_(U^m N) ≫ B_M.map(delta_N) = beta_N ≫ I_(T_s N)`.
  In particular there is no second independently chosen delta.
- `ScalarEquations` conjoins the three return-square identities and that
  point identity. `Properties` conjoins this with naturality at all levels.
- `SystemPowerNormalization`, `IntegralPowerNormalization` and
  `RationalPowerNormalization` are included on both s and X. They state
  compatibility of the same iterated delta/d with the actual scalar unit
  and with direct versus successive extension. `PowerScalarUnit` is
  `delta_N ≫ U^m.map(unit_N) = unit_(U^m N)`.
  `PowerScalarTower` is
  `S.map(delta_T N) ≫ delta_S(T N) ≫ Z^m.map(assoc_N) =
  assoc_(U^m N) ≫ delta_direct N`.
  The unit and associator are the recorded simultaneous-sequence ones,
  the integral completion-normalized ones, and their rationalizations
  `sfRationalScalarUnit` and `sfRationalScalarComp`. The uniterated a is
  already the owning dependency's specified normalized scalar family, so
  its unit and tower coherence is supplied there.
- `PointScalarNormalization` states the beta unit and tower identities
  using `DerivedCategory.fieldScalarUnit` and `pointFibreFdTensorTower`.
  These are the module multiplication unit and point-sections tensor
  associator. Together with the preceding normalization clauses and the
  owning family's coherence, they make both scalar equations compatible
  with identity and successive extensions using exactly the prescribed
  associators.
- There is no finite Tor-amplitude, perfectness, or extra bounded-reduction
  hypothesis. Only the existing integral constructible category is used.
  No idempotent completion is introduced anywhere.

Dependency declarations used (namespace `WeilConjectures`, unless qualified):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`,
  `geometricFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imports:
  `Padic.FiniteCoefficientFields`, `Padic.coefficientExtensionRing`,
  the recorded valuation-ring and uniformizer constructions.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`, `rationalDerivedPullback`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteFibre`,
  `pointIntegralFibre`, `pointRationalFibre`, `pointRationalFibreScalarIso`,
  `pointFiniteSections`, `pointFibreFdTensorTower`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its
  topology, through the recorded coefficient/derived categories. The
  object universe u+1 and morphism universe u are retained.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, through `pointFiniteFibre`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `sfRationalScalarExtension`; only the raw category is used.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, `IntegralComparisonRealizationCoherence`,
  `integralComparisonComposition`, `integralComparisonScalar`,
  `integralComparisonConstructibleScalar`, the sequence comparison family,
  the scalar unit, and `integralComparisonScalarAssociator`.
  The three definition-owned helper declarations restrict and rationalize those exact
  maps, in the new definition-owned module, with no change to the dependency record or module.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralFiniteCanonicalPullbackComposition`, the recorded finite
  presentation/composition interface.
- `Sheaf.SixFunctors.FrobeniusPointTransport`:
  `frobeniusPointIso`, `frobeniusPointTransportFinite`,
  `frobeniusPointTransportIntegralConstructible`, and the rational recipe.
- `Sheaf.Paper.PointSectionsScalarExtension`: the actual point sections
  scalar comparison and its normalization, used through the size-transported
  `pointRationalFibreScalarIso` and the point tensor tower.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPointTransport` (the prescribed
  rational point transport with its object identification), and
  `localPullbackObjectIso` (the raw-localization coordinate identification).
- `Sheaf.TraceFormula.PointTransportComposition`: `pointPowerPullbackModel`,
  recorded through `def-trf-finite-pullback-presentation-comparison` (existing: true).
  The theorem `point_transport_composition` is not a statement dependency: this
  item uses only the existing plain definition from that module.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarUnit`,
  `sfRationalScalarComp`, the completion-normalized unit and associator.
- `Sheaf.Paper.FieldDerivedScalarTower`:
  `DerivedCategory.fieldScalarUnit` and the derived field tensor tower.
- Proof-only imports retain `Sheaf.SixFunctors.FrobeniusPointTransportNatural`
  (`frobeniusPointTransport_natural`) and
  `Sheaf.Paper.PointAutomorphismTransportScalarExtension`
  (`point_automorphism_transport_scalar_extension`). The six-step theorem
  docstring explains each use.

The three applicable landed statement dependencies (local trace, scalar extension
composition, derived field scalar tower) and the new existing-definition node were
added to the item's `stmt_deps`. Their source interfaces were read. The two scalar
composition nodes supply choices of their uniquely specifying theorems; the plain
finite-pullback definition is cited through its definition node instead.

Edge cases checked before finalizing the statement:

- r=0 is m=1, with no minimal-period condition; all nonminimal positive return
  periods remain allowed. The recursion also defines I^0 as identity.
- n=0 represents A_(E,1); no positive quotient is omitted or replaced by A_(E,0).
- Zero objects and zero morphisms are included in all three categories and
  require no auxiliary nonvanishing or perfectness condition.
- Identity inclusions F=G=H and mixed identity/nonidentity towers are permitted
  by the non-strict inclusion binders and the canonical multiplication units.
- The base point and z=id are allowed. The empty scheme has no k-point z,
  exactly as in the source; no separate nonemptiness hypothesis was added.
- The invertibility requirement is derived from ell not equal to p rather
  than imposed again. Pro-etale and coefficient universes follow the recorded
  categories; no equality of site object/morphism universes is imposed.
- Arbitrary rational point and space morphisms are quantified over directly,
  including sums of tensor morphisms. No lift to an integral map is assumed.
- The finite target equations are in a fully faithful ambient derived category;
  that transport changes neither objects permitted as inputs nor the equality.

Searches for an existing exact statement (actual searches in this work):

- `msearch.py ... leanfinder`, query
  "Iterated natural point Frobenius transport and return square pullback
  commute with coefficient field extension": 8 hits, headed by
  `IsPurelyInseparable.iterateFrobenius` variants and field Frobenius maps.
  None concerns the actual derived point and return comparisons.
- `msearch.py ... loogle "CategoryTheory.NatTrans.naturality"`: 9 hits,
  including generic naturality, pullback/pushout cone isomorphisms and
  Grothendieck map composition. They do not state the normalized mixed
  scalar identities on simultaneous pro-etale diagrams.
- `msearch.py ... grep "Frobenius.*(scalar|transport)|return.*pullback"`:
  no Mathlib hits for this combined comparison.
- `msearch.py ... leansearch`, query "Naturality of iterated natural
  transformations and scalar extension of derived pullback compositors":
  8 hits, including `NatTrans.leftDerived_comp`, `NatTrans.rightDerived_comp`,
  and categorical pullback naturality. None is this specialized statement.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf` and Mathlib for the
  item id, proposed names, iterated-return, Frobenius transport/scalar, and
  natural-transformation iteration found no exact existing theorem.
  `LocalFrobeniusWeilMorphismNaturality` supplies only the overlapping
  rational naturality result. `LocalFrobeniusTransportNormalization`
  contains the existing scalar existence theorem reused in the current repair.
  Its theorem lists this item as a proof dependency; the closing proof import must
  be omitted under stages/2-statements.md §3.7. The existing helper itself does not
  depend on the present calculus theorem.
- Direct inspection of Mathlib's endomorphism multiplication and `pow_succ`
  checked the order in `powerComparison`; the recursion uses the specified
  compositor at g and g^j in the correct contravariant order.

No counterexample or unresolved statement dispute was found. No source
statement is corrected. The earlier finite target universe elaboration
problem was repaired by specifying the recorded derived-category instances
and target module universe, without adding a universe equality hypothesis.

## Repair of the independent return at 4b4736b74c96

1. H13: the dependency JSON for
   `lem-trf-integral-pullback-comparison-realization` is removed from this packet.
   Its live N2 record remains byte-identical, including the primary theorem and
   all 20 declarations. No dependency module is delivered. The former interface
   module is removed. Its four needed declarations are now in the new definition module
   `Sheaf.Paper.RealizedPullbackComparisons`, carry that definition node's
   blueprint identifier and are included in its `lean.declarations`: `integralComparisonConstructibleComposition`,
   `integralComparisonRationalComposition`,
   `integralComparisonRationalScalar_existsUnique`, and
   `integralComparisonRationalScalar`. The unnecessary fifth declaration
   `integralPullbackComparisonRealizationFunctorial` is dropped. Thus none of the
   original comparison interfaces or their landed consumers is rebound.
2. The item no longer lists `lem-trf-point-transport-composition` in `stmt_deps`.
   Its only use of that module, the plain definition `pointPowerPullbackModel`,
   is recorded by the new definition node described below. This uses its existing
   module and declaration, with `existing: true`; it copies no Lean construction.
3. The accepted scalar-unit/tower dependencies remain as reviewed:
   `sfRationalScalarUnit` and `sfRationalScalarComp` choose their uniquely
   specifying theorem, and `fieldScalarUnit` does the same. The accepted
   mathematical formulas, main theorem signature and hypotheses are unchanged.

The definition-owned constructible composition helper is `ObjectProperty.isoMk` of
`integralComparisonComposition`. The rational composition helper localizes that
same map and conjugates by `localPullbackObjectIso`. The scalar existence/uniqueness
helper pins every component by HEq to the localization of
`integralComparisonScalar`; its definition selects from that uniquely determined
formula. Its source and full natural-language proof are in its docstring. It is
part of the actual rational comparison construction in this item's statement,
not a replacement assertion about the owning integral comparison system.

## New nodes

`def-trf-realized-pullback-comparisons` owns the three comparison definitions in
`Sheaf.Paper.RealizedPullbackComparisons`: the full-subcategory lift of the
specified integral compositor, its raw rationalization with the prescribed
object comparisons, and the unique rational scalar natural isomorphism with
components pinned to the localized integral comparison. It postpones no new proof: the scalar definition uses the existing
`LocalFrobeniusTransport.rationalScalar_existsUnique` theorem, which states the
required localization/naturality/uniqueness assertion. The module preserves the helpers' types and bodies.
The original integral comparison node is absent from the packet and remains
unchanged. The item cites this new node. Searches retained in `searches.jsonl`
and the node's `mathlib_searches` include LeanSearch (8 generic comparison hits),
Loogle (`integralComparisonRationalScalar`, 0 hits), Mathlib grep (0 hits),
project/DAG grep (no existing declaration or owning node), and blueprint reference
searches (no exact owning definition). The source is the same final common-stage
Frobenius transport sentence, with Stacks 099N, 0D6D and 06YY for its constructions.
Its endpoints impose exactly the prime-invertibility assumptions of the recorded
pullbacks; identity morphisms, zero objects, and equal coefficient fields remain
allowed. HEq pins the canonical localized components under the existing object
formulas; it supplies no free comparison data.


`def-trf-finite-pullback-presentation-comparison` records the already-landed
`WeilConjectures.pointPowerPullbackModel` in
`Sheaf.TraceFormula.PointTransportComposition`, with `existing: true` and no
new Lean module. It defines the canonical natural isomorphism from intrinsic
finite derived pullback to constant-ring tensor derived pullback by applying
`Functor.mapDerivedCategoryNatIso` to the composite of the inverse intrinsic
adjunction comparison and the unit-normalized module comparison. The source is
Stacks 03D3/0D6D and the finite return comparison in the blueprint's common-stage
Frobenius transport sentence. The new node explicitly introduces the prime,
finite extension, positive quotient exponent n+1, schemes and morphism. Its
statement cites the coefficient, site, finite-derived-pullback and constant-ring
operation definitions, and the recorded unique unit-normalized comparison.
It adds no finite-field or invertibility assumptions to the existing declaration.

Actual repair searches:

- `blueprint_refs.py search pointPowerPullbackModel` and
  `blueprint_refs.py search "finite pullback presentation"`: both 0 matches.
  `blueprint_refs.py ancestor` identifies `prop-trf-karoubi-independence`.
- Direct `rg -l pointPowerPullbackModel dag/nodes` finds six records, all users
  or the theorem owning the helper, with no separate definition node. The recorded
  definitions in `def-trf-iterated-weil-map` concern strict Weil iterates and are
  not this arbitrary-morphism presentation comparison.
- `msearch.py ... leansearch`, query "Unit normalized comparison of intrinsic finite
  coefficient derived pullback and constant ring tensor derived pullback": 8 hits,
  including `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`
  and unrelated polynomial/seminorm/vector-field pullbacks, no exact comparison.
- `msearch.py ... loogle "Functor.mapDerivedCategoryNatIso"`: 0 hits, unknown identifier.
- `msearch.py ... grep
  "pointPowerPullbackModel|inverseImageFiniteIntrinsicPullbackComparison|integralFinitePullbackModel"`:
  0 Mathlib hits. Direct project searches find the existing plain definition at
  `lean/Sheaf/TraceFormula/PointTransportComposition.lean:178` and no declaration
  with this name under `lean/WeilConjectures`.

No existing definition is redefined. The new DAG node supplies the precise
statement dependency requested by the return. Edge cases of its existing
construction: n=0 is the first positive quotient; f may be an identity or an
arbitrary scheme morphism; empty schemes are allowed; no point, Frobenius,
prime-invertibility or constructibility premise is imposed on the natural
isomorphism between the ambient finite derived functors.

## Second reading by Q65

This is the dispatcher's requested self-check of the repaired packet; no separate
agent was started. The maintainer's independent review remains the acceptance
review. I reread the item statement, helper signatures, new definition record,
and the returned findings side by side. The main signature and all its formulas
are unchanged from the mathematically accepted version. In particular, positive
m is r+1, the return equality w is retained through eqToIso, I starts at identity,
t is I followed by the fibre image of the actual v, and each naturality predicate
quantifies over every morphism of its recorded category. The first scalar identity
remains on simultaneous systems, integral realization and rationalization; the
second uses the same delta and inverse point-sections comparison. Identity and
tower clauses still use the accepted completion and point tensor associators.

The new definition's two endpoints are precisely `finiteDerivedPullback l E n f`
and `proEtaleConstantRingDerivedPullback (coefficientExtensionRing l E (n+1)) f`.
The existing definition contains exactly the two adjunction/presentation factors
specified in the new node. The four moved helpers retain their bodies and types;
only their module ownership and blueprint docstrings change. The only removed
helper was the unused extra existence theorem. The independent return's two
ownership mismatches are repaired without changing the underlying mathematics.

## Validation

The saved packet first passed `deliver2.py --no-push` as requested (temporary
commit 4facf637b39); this mechanical pass did not discharge the independent return.
The repaired item is compiled through `scompile.py` and the final packet is then
checked with `deliver2.py --no-push` before delivery. Results are recorded below.

## Compile performance repair

The retained packet failed its first dry run with a 60-second main-module
timeout; the comparison definition module compiled. A scratch trace identified
repeated expensive attempts to unify the point and space residue-field instance
families. Explicit scheme arguments were supplied to `powerComparison`, the
return compositors, and the `congrArg` functions defining the map-equality
transport. The main module now sets both
`backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to `true`, avoiding the unnecessary
unfolding in instance search. A scratch copy then compiled in 8.1 and 10.2 seconds
in sandbox and library modes. No theorem signature, construction, equation,
coefficient universe or hypothesis changed; no time limit was raised. The final
main module is compiled and the full packet dry-run below before pushing.

Final `scompile.py` result: both delivered modules compile without errors or
non-sorry warnings. `RealizedPullbackComparisons` took 25.3 seconds in library
mode (42.2 in its sandbox check); `IteratedReturnTransportScalarCalculus` took
21.0 seconds in library mode (40.3 in its sandbox check), all below 60 seconds.
The main node record's signature matches the file verbatim; both modules have
no line over 100 characters. Exactly two postponed theorems remain: the unique
rational-scalar comparison existence theorem and the main calculus theorem.


## Repair of the independent return at ed72133efac7

The saved packet was inspected and its mandatory initial dry run was started
before any edit. The independent return identifies an actual duplicate theorem,
regardless of the mechanical dry-run outcome. The duplicate
`WeilConjectures.integralComparisonRationalScalar_existsUnique` has now been
removed completely from `Sheaf.Paper.RealizedPullbackComparisons` and from its
node's `lean.declarations`. This module publicly imports
`Sheaf.Paper.LocalFrobeniusTransportNormalization`; its scalar definition uses
`WeilConjectures.LocalFrobeniusTransport.rationalScalar_existsUnique` directly.
The three remaining definition helpers and the main calculus statement are
unchanged.

Binder comparison: both theorem texts quantify over `l : ℕ`, `[Fact l.Prime]`,
`E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
`[FiniteDimensional ℚ_[l] E]`, `C : IntegralComparisonSystem.{u} l`,
`M : Type u` with its same three field/coefficient instances,
`ι : E →ₐ[ℚ_[l]] M`, `{X Y : Scheme.{u}}`, `f : X ⟶ Y`, and the
prime-invertibility instance on every residue field of X and Y. The earlier
section variables D, hl and X₀ in the existing module do not occur in this
signature. The unique-isomorphism type and every HEq component formula are
verbatim identical. In particular, this reuse adds no finite-field or point
hypothesis and preserves arbitrary schemes, identity maps and coefficient
extensions, zero objects and every rational morphism.

The existing helper's module does not import the calculus module. The DAG's
local-normalization theorem names the calculus as a proof dependency; its future
closing proof import is omitted under stages/2-statements.md §3.7. This repair
reuses its independent helper, not its downstream normalization conclusion.
No live module or existing dependency record is edited. No statement correction,
new hypothesis or new postponed theorem is introduced. This section supersedes
the historical references above to four helpers and two postponed theorems.
The repaired packet contains only the main calculus theorem as a new `sorry`.

Self-check: I reread the existing theorem's full signature and docstring, the
removed theorem, its replacement call, the helper node's declaration inventory,
and the unchanged main theorem. The repair resolves the return's duplicate
exactly by using the existing theorem. Final server compile and dry-run results
will be recorded below.

Validation for the ed72133efac7 return: the initial saved-packet dry run passed
mechanically at temporary commit 10397e0866e. The duplicate was then repaired
as required. The explicit `scompile.py` invocation for both repaired modules
exited 0 without errors or non-sorry warnings. Signature and line-width checks
confirm both node signatures are verbatim, both files have no line over 100
characters, and only the main calculus theorem contains `sorry`.
