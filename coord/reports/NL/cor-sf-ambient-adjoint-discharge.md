## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.AmbientAdjointDischarge`, declaration
`AlgebraicGeometry.ProEtale.exists_boundedConstructibleAdjointDischarge`.
The unstated comparison-class prerequisite is supplied in
`Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`, declaration
`AlgebraicGeometry.ProEtale.exists_comparisonClassAdjunction`, together with the fully
specified helper structure `ComparisonClassAdjunction`. Both theorems have only `sorry`
proofs. The structure is an ordinary structure with all its data and equations explicit;
there are no hollow definitions, selected arbitrary maps, axioms, or proved theorems.

Read the item, all six immediate dependencies, their source statements, and the unit
`sk-prop-sf-existence`. Read the source markdown and unit section in the server
blueprint replica under `sec-smooth-purity/sk-prop-sf-existence/`. Its corollary proof explicitly
allows bounded-below targets, and restricts the input to the comparison class; the item
specializes that input class to bounded constructible objects.

Hypotheses and clauses:

- The global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`. Its
  `D.k` is the fixed algebraic closure. The coefficient prime is `l`, `[Fact l.Prime]`,
  with `_hl : l ≠ D.p`.
- The finite extension is `E`, `[Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The integer stage is `n : ℕ`, `_hn : 1 ≤ n`.
  Every coefficient category uses exactly
  `ModuleCat.{u+1} (Padic.coefficientExtensionRing l E n)`. This is the existing
  quotient by the power of the existing chosen uniformizer. No arbitrary finite ring
  is substituted. `E : Type (u+1)` puts the coefficient ring in the standard larger
  universe of module-valued sheaves; schemes remain in `Scheme.{u}`, whose small site
  has object universe `u+1` and morphism universe `u`. These site universes are not
  equated.
- The finite-type schemes over `D.k` are `aX` and `aY`, each with
  `[LocallyOfFiniteType] [QuasiCompact]`. The morphism `f` has these two properties
  and `[IsSeparated f]`, and `_hf : f ≫ aY = aX` says it is over the field.
- The chosen compactification is `c : Compactification f`. Its fields give the open
  immersion, proper part `c.g`, and factorization. The finite-type structure map on
  `c.Z` is `c.g ≫ aY` and follows from properness and finite type of `aY`.
  The nonnegative dimension bound is `d : ℕ` and
  `_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)`.
- The vanishing input is the first conjunct
  `HasCohomologicalDimensionLEOnEtaleOrigin ... c.g (2*d)`. The imported definition
  includes both the original-source vanishing for every integer `r > 2*d` and every
  etale-origin sheaf, and the same vanishing for its restriction along every small
  pro-etale base change. It neither asks for nor concludes the all-sheaf bound.
- The etale right adjoint is the existential functor `G` together with
  `Nonempty (Etale.rightDerivedLowerShriekOfCompactification ... c ⊣ G)`.
  This is an ordinary unbounded ETALE adjunction, which exists unconditionally here;
  it is a conclusion, not an additional hypothesis. Keeping a right adjoint together
  with its adjunction is the source's choice of `f^times`, unique up to the unique
  adjunction-compatible isomorphism.
- The exceptional inverse-image formula is literally
  `R(ν_*(Y)[A]) ⋙ G ⋙ D(ν^*(X)[A])` in `ComparisonClassAdjunction.homEquiv`.
  Functor composition is in diagrammatic order, so this is exactly
  `ν_X^* f^times Rν_Y,*`. There is no second `Rν_X,*` and no arbitrary pro-etale
  right functor in its place.
- In the item, `P` is the existing
  `ProEtale.DerivedCategory.boundedConstructible A X`; `Q` is the canonical
  t-structure's `plus`. Thus every bounded constructible input and every
  bounded-below target is quantified over, including in particular the bounded
  constructible targets of the corollary. At these finite coefficient stages the
  upstream constructible predicate is the comparison image of bounded constructible
  etale complexes, as its docstring specifies. This use does not identify arbitrary
  etale-origin sheaves with constructible ones.
- The field `homEquiv` is an actual equivalence of the specified Hom sets.
  `naturality_left` and `naturality_right` impose naturality for every allowed morphism
  in both variables. The left functor is the existing derived compact-support
  functor `rightDerivedLowerShriekOfCompactification`, so it is `Rp_* Dj_!`, not the
  right derived functor of the composite underived functor.
- The helper takes the finite coefficient ring `Λ`, and uses `ModuleCat.{u+1} Λ`
  throughout. Both theorem conclusions pass `Padic.coefficientExtensionRing l E n`
  and the existing proof `Padic.finite_coefficientExtensionRing l E n _hn` explicitly
  to `@ComparisonClassAdjunction`; finiteness is derived from the existing positive
  stage hypothesis, rather than added as a hypothesis.
- The field `comparison` gives isomorphisms between these compact-support functors
  after restriction to `P`. The added `comparison_normalized` equation requires its
  component at every `D(ν^*) K` in `P`, for every bounded-below étale representative
  `K`, to be exactly `(rightDerivedLowerShriekOfCompactificationOriginIso Λ c d).hom.app K`.
  This is a reference to the fixed existing definition, with no arbitrary map or
  replaceable comparison dictionary. Its definition transports the canonical
  `Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ c d` through the two
  compact-support comparisons. Naturality then determines components at all objects
  isomorphic to those representatives, precisely the two input classes used here. `comparison_refl` and `comparison_trans` give identity
  comparisons and the cocycle law. `comparison_homEquiv` identifies the chosen Hom
  bijections under those comparisons, so these are comparisons of the relative
  adjunctions, not unrelated functor isomorphisms. They are indexed by all pairs of
  compactifications (the usual common-refinement normalization), hence include every
  refinement and its compositions. The right functor is normalized to the same
  `ν_X^* G Rν_Y,*` throughout, so its comparison is identity; transporting an arbitrary
  etale right-adjoint choice to this normalization is the unique adjunction-compatible
  comparison. This is the standard equivalent presentation of coherent right-adjoint
  comparisons.
- The three ambient definition dependencies name the stronger notion and explain
  the scope warning. They are not used as predicates or hypotheses in this Lean
  statement: the corollary does not assert that datum or exceptional-adjoint
  admissibility. The finite-stage exceptional functor is expressed by its displayed
  composite, using existing comparison and derived functors. No separate copy of
  an ambient datum, an admissibility predicate, or the coefficient-stage construction
  of the exceptional functor is introduced. In particular the module does not try
  to formalize the other coefficient stages of those definition nodes as part of a
  finite-stage corollary.
- The elliptic-curve sentence is the scope warning from the source, retained in the
  module and proof docstrings. It prevents an ambient interpretation of the conclusion;
  the theorem makes no all-object nonadjunction or constructibility/Tor-preservation
  claim. Those assertions are separate nodes/results, not hypotheses smuggled into
  the class-restricted result.

Dependency declarations and sources actually inspected:

- `WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension`:
  `HasCohomologicalDimensionLEOnEtaleOrigin`, `etaleOrigin`,
  `etaleOrigin_upperStar_obj`, `hasCohomologicalDimensionLEOnEtaleOrigin`, and
  `isZero_homology_rightDerivedComparisonLowerStar`. Read their full docstrings and
  section binders, and confirmed the current published source using `scompile.py --source`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, the exact extension-by-zero descent
  followed by derived proper direct image, on the ordinary derived categories.
- `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`:
  `DerivedCategory.plusEtaleOrigin`, the bounded-below comparison essential image;
  the derived comparison functors and their canonical adjunction.
- `WeilConjectures.SixFunctors.ProEtale.Derived.Constructible`:
  `DerivedCategory.boundedConstructible` and
  `DerivedCategory.boundedConstructible.plusEtaleOrigin`. Their source explicitly
  restricts agreement with intrinsic constructibility to finite coefficients.
- `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek`:
  `rightDerivedUpperShriek` and `rightDerivedUpperShriekHomEquiv`, their full signatures,
  docstrings, and naturality lemmas. Its interface assumes
  `Etale.HasBoundedBelowUpperShriek`; that hypothesis is not added to our geometric
  theorem. Instead the needed ordinary etale adjoint is asserted in the conclusion.
- `WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint`:
  `HasUniformCohomologicalDimensionLE`, `HasAmbientExceptionalRightAdjoint`, and
  `IsExceptionalAdjointAdmissible`. These are stronger ambient predicates and are not
  used as substitutes for this comparison-class statement.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` and `Scheme.proEtaleSiteComparisonModules`.
  Its recorded module is imported. The available recorded proof-dependency modules
  `EtaleExceptionalAdjoint` and `EtaleCompactSupportComparisons` are imported as proof
  imports. The recorded `ProEtaleSiteComparisonDerived` proof import was tested but
  collides with the legacy upstream pro-etale notation environment; the same comparison
  input is available through the upstream `Comparison.FullyFaithful` proof import.
  This follows the instructed preference for upstream in a duplicate-import failure.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`;
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the existing
  `Padic.coefficientExtensionRing` and its valuation-ring/ideal constructions.
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement`,
  its identity and composition, and `Compactification.category`; these refine the
  existing `Compactification` used in the signatures.

Additional source inspected in this repair:

- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence`:
  `rightDerivedLowerShriekOfCompactificationOriginIso`, its full definition and
  `rightDerivedLowerShriekOfCompactificationOriginIso_trans`. Confirmed the current
  published source with `scompile.py --source`. It transports the canonical étale
  comparison via the existing compact-support comparisons, so no new comparison
  construction or helper node is needed.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence`:
  `rightDerivedLowerShriekOfCompactificationPlusIso` and
  `rightDerivedLowerShriekOfCompactificationPlusιIso`, including their common-refinement
  and bounded-below/unbounded compatibility definitions.

Edge cases checked: zero input and target Hom sets; empty source and its empty
compactification (take `d=0`, without treating the dimension of the empty scheme as a
nonnegative integer); a zero-dimensional compactification, including the identity of
`Spec k`; all positive coefficient stages including `n=1`, while `n=0` is excluded by
`_hn`; arbitrary bounded-below targets without etale-origin or constructibility
assumptions; any compactification, not only dense ones; and identity/composite
refinements. The elliptic curve in the source is a negative test of replacing the
restricted bound by the ambient one.

Searches performed for this delivery:

- `msearch.py leanfinder`, query `bounded constructible exceptional adjunction etale
  proetale class restricted full cohomological dimension`: eight hits, on etale sites,
  etale morphisms, derived t-structure, and light profinite sheaves; none states this
  relative adjunction and vanishing corollary.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.Functor`: twelve general Hom-equivalence and adjunction construction
  lemmas. They require an adjunction, and do not provide the geometric class result.
- `msearch.py grep`, query
  `FullCD|fullCohomologicalDimension|ambientAdjoint|exceptionalAdjoint`: no Mathlib hits.
- `msearch.py leansearch`, query `class restricted exceptional adjunction of etale
  origin sheaves and cohomological dimension`: the service returned Internal Server
  Error; recorded as unavailable, not as evidence of absence.
- `rg` of the upstream project, the side `WeilConjectures` sources, and `lean/Sheaf`
  for `ambientAdjoint|Ambient.*Adjoint|ambient.*adjoint|FullCD|fullCD|fullcd|
  exceptionalInverseImage|exceptional.*[Aa]djoint` found the existing full-CD definition,
  vanishing theorem, comparison Hom equivalences and stronger ambient interfaces.
  Read these declarations rather than duplicating them. The exact item id has no
  upstream declaration, nor does `thm-sf-ambient-adjoint-class` have a combined exact
  theorem. Final-name searches in upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no collision.

No item statement correction, new definition node, or disputed assertion about this
corollary was needed. Both delivered Lean files compiled cleanly through `scompile.py`
with explicit universes and `autoImplicit false`; only postponed theorem proofs remain.

## Dependency modules

`def-sf-fullcd-class`: its Lean record was absent. Recorded the published existing
`AlgebraicGeometry.ProEtale.HasCohomologicalDimensionLEOnEtaleOrigin`, whose two
vanishing clauses exactly implement the displayed definition, specialized to the
coefficient category used here. No duplicate definition module was written.

`thm-sf-fullcd-class`: its Lean record was absent. Recorded the published existing
`AlgebraicGeometry.ProEtale.hasCohomologicalDimensionLEOnEtaleOrigin`. Its explicit
section variables give the bound under the stated properness, field, finite coefficient,
exponent invertibility and dimension hypotheses. Specialization to the datum in our
statement is exactly the source's finite-level vanishing input. Its explanatory source
comment identifies the `M=0` comparison contribution. No duplicate theorem was written.

`thm-sf-ambient-adjoint-class`: its Lean record and Mathlib match were absent. Its new
module supplies the unconditional geometric statement, with exactly the same hypotheses
as the item, full-CD bound `2*d`, the ordinary etale adjoint in the conclusion, and
`ComparisonClassAdjunction` for `P = plusEtaleOrigin`, `Q = plus`. The helper structure
belongs to this node's comparison-class adjunction notion and is listed in
`lean.declarations`; its fields are real data and equations, and every declaration has
its source and blueprint docstring. The item specializes `P` to bounded constructible
objects, rather than duplicating the prerequisite theorem. The proof docstrings specify
the comparison/adjunction chain and the uniqueness argument for coherent comparisons.

STATEMENT-DISPUTED (inherited explanatory assertion of `def-sf-fullcd-class`, not this
item): the assertion identifying ALL etale-origin sheaves with constructible sheaves is
false. On the spectrum of an algebraically closed field with finite field coefficients,
the constant etale sheaf with infinite-dimensional stalk is of etale origin after
pullback and is not constructible. The displayed FullCD definition and the valid
inclusion of constructible sheaves in the comparison class are sufficient here. The
existing definition has precisely those displayed clauses, and does not encode the
false converse. This defect was also recorded in the stage-1 Q37 review. Dependency
text is outside the permitted lean-only dependency changes and is left unchanged.

## Repair of H3/H13 return

The return at immutable head `dde2fa25c670` found that coherence and Hom compatibility
alone permitted compactification-dependent scalar twists. The previous second reading
missed this; it does not certify this repaired version and is superseded.

Repaired `ComparisonClassAdjunction` by requiring `comparison_normalized`, an equality
with the fixed published `rightDerivedLowerShriekOfCompactificationOriginIso` at every
bounded-below étale representative whose image is in `P`. This is the exact comparison
in clause (3) and the last paragraph of the source proof, not merely the existence of
some coherent isomorphisms. The helper takes the finite ring `Λ` directly, so its right
hand side uses the published definition with its actual finite-module coefficient type.
There is no `canonicalComparison` data field, arbitrary-map class, or selected dictionary.
Both theorem statements pass the fixed ring `A_{E,n}` and its existing positive-stage
finiteness proof; all geometric and coefficient hypotheses and both input classes are
unchanged. The node changes are only in `lean`; their natural statements are unchanged.

Scalar-twist test: replacing a component by `(s_d/s_c)` times the canonical comparison
must now satisfy literal equality with that canonical component for every representative.
For a nonzero coefficient module on the geometric point, the canonical component is
invertible and this forces the scalar factor to act as the identity. Hence the previous
nontrivial twists fail the new equation. For zero objects or a zero ring there is no
nontrivial automorphism, and the normalization still makes sense. Identity and cocycle
fields are retained, as is compatibility with the natural Hom bijections. Essential-image
membership and naturality extend the fixed representative components to all permitted
inputs, including the bounded constructible inputs of this corollary.

Repair searches: `rg` for `rightDerivedLowerShriekOfCompactificationOriginIso` in the
older upstream tree and side `lean/Sheaf` found no local occurrence; the exact declaration
was found in the published side `lean/WeilConjectures/.../LowerShriekIndependence.lean`
and confirmed through `scompile.py --source`. Read its entire definition and the étale
comparison definitions it uses; reused them instead of constructing a duplicate. The
original three kinds of notion search remain recorded above and in `searches.jsonl`.

Validation is performed with the required `scompile.py` on each of the two modules,
then `deliver2.py --no-push`. A fresh independent second reading remains for the next
worker, as required by the brief.

## Second reading by NL

I independently read the repaired delivery, not the superseded second reading mentioned
in the worker report. I opened the item and all six immediate dependency nodes, both
complete Lean modules, and the dependency declarations used by their signatures. Source
places were read in the launcher's replica of `literature/blueprint/master/blueprint/`:
`sec-smooth-purity/sk-prop-sf-existence/{cor-sf-ambient-adjoint-discharge,
thm-sf-ambient-adjoint-class}.md`, the enclosing existence unit and
`wholeblueprint-final.tex:6577–6675`, the FullCD definition/theorem source files, and the
three exceptional-operation definitions. These are blueprint sources, not Stacks-tag
statements; their standing hypotheses are finite-type schemes over the fixed algebraic
closure, invertible coefficient prime, finite extension and positive coefficient level.

My statement checklist and its Lean rendering, with verdicts:

1. Global finite-field datum and its fixed algebraic closure: `D :
   WeilConjectures.FiniteFieldDatum.{u}`, with structure maps to `Spec (.of D.k)`.
   Read `FiniteFieldFiber`: `D.k` has the specified algebraic-closure structure.
   Verdict: the source's base field, without a substituted special field.
2. Prime distinct from the characteristic, finite extension and positive stage:
   `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`, `E`, `[Field E]`,
   `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`, `(n : ℕ)` and
   `(_hn : 1 ≤ n)`. Every coefficient category is
   `ModuleCat.{u+1} (Padic.coefficientExtensionRing l E n)`. Opened the coefficient
   construction and `finite_coefficientExtensionRing`; the finite-ring proof passed
   to the helper is derived from these hypotheses. Verdict: exactly `A_{E,n}`;
   no arbitrary ring, regularity assumption or extra finiteness hypothesis.
3. Finite-type source and target over the base: `aX`, `aY`, each with
   `[LocallyOfFiniteType] [QuasiCompact]`. The separated finite-type base morphism
   is `f`, `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`, with
   `_hf : f ≫ aY = aX`. Verdict: the full geometric hypotheses, without smoothness,
   properness of f, or an added separation assumption on X or Y.
4. Chosen compactification and nonnegative dimension bound: `c : Compactification f`,
   `d : ℕ`, `_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)`.
   Read the compactification fields: `c.i` is open, `c.g` proper, with factorization.
   Finite type of `c.Z` over the field follows from properness and finite type of Y.
   Verdict: every compactification allowed by the source, including non-dense ones.
5. Vanishing input: first conjunct
   `HasCohomologicalDimensionLEOnEtaleOrigin ... c.g (2*d)`.
   Opened its definition: the first clause quantifies over all original-source
   etale-origin sheaves and every integer r greater than the bound; the second
   quantifies over every `V : Y.ProEt`, each pullback square, and the pullback of
   each such original sheaf. Verdict: both displayed FullCD_cls clauses, exactly.
   Opened `hasCohomologicalDimensionLEOnEtaleOrigin` with its section binders;
   it supplies this bound on specialization. Its `M=0` explanation is the actual
   comparison vanishing statement, not a positive lower bound on comparison CD.
6. Ordinary etale exceptional adjoint: `∃ G, ∃ adj :
   Etale.rightDerivedLowerShriekOfCompactification ... c ⊣ G, ...`.
   The left functor is the existing ordinary etale compact-support functor. This
   adjunction is a conclusion. Verdict: the source's choice of f^times, with no
   ambient pro-etale adjunction or bounded-below-adjoint instance assumed.
7. Right-hand formula: `ComparisonClassAdjunction.homEquiv` uses literally
   `R(ν_*(Y)[A]) ⋙ G ⋙ D(ν^*(X)[A])`. Diagrammatic composition reads
   `ν_X^* f^times Rν_Y,*`. Verdict: the formula of
   `def-weil-exceptional-inverse-image`, with no second Rν_X,* or arbitrary map.
8. Allowed objects and all Hom sets: the item passes
   `DerivedCategory.boundedConstructible A X` as P and
   `_root_.DerivedCategory.TStructure.t.plus` as Q. `homEquiv` quantifies over
   every K, membership proof hK, L and hL, and is an equivalence, with both
   `naturality_left` and `naturality_right`. The dependency passes
   `DerivedCategory.plusEtaleOrigin A X` as P, retaining all bounded-below
   etale-origin inputs. Opened both definitions and
   `boundedConstructible.plusEtaleOrigin`: these are the finite-coefficient
   constructible class and the full comparison class, respectively. Verdict:
   exactly the input specialization and unrestricted bounded-below targets of
   the corollary proof; no constructibility or etale-origin condition on L.
9. Compact-support functor and its comparisons: the left functor is the existing
   `rightDerivedLowerShriekOfCompactification`, namely `D(j_!) ⋙ Rp_*`.
   `comparison` is a natural isomorphism on P, `comparison_normalized` fixes
   its value at every bounded-below etale representative to the existing
   `rightDerivedLowerShriekOfCompactificationOriginIso`, and `comparison_refl`
   and `comparison_trans` impose identities and cocycles. Opened that definition:
   it transports `Etale.rightDerivedLowerShriekOfCompactificationPlusιIso`
   through the two existing compact-support comparisons. Verdict: canonical
   comparisons on all representatives and, by naturality, their whole essential
   image, including the constructible inputs. All-pairs indexing includes every
   refinement, its identity and every composite, with the same canonical maps.
10. Compatibility with the actual adjunction: I found one remaining gap in the
    repaired helper. It received G but not the chosen etale adjunction; its Hom
    equivalences were still unrelated to that witness at the distinguished
    compactification. I changed the helper to take `c₀` and `adj`, replaced the
    separate `Nonempty` adjunction conjunct in both theorem statements by an
    existential adjunction witness, and passed that witness into the helper.
    The new `homEquiv_normalized` field requires, at c₀, that the Hom bijection
    applied to the canonical compact-support comparison followed by the inverse
    site-adjunction image of a equals `D(ν_X^*).map (adj.homEquiv a)`.
    This is exactly the source proof's three Hom identifications; it specifies
    the forward map without choosing an inverse to full faithfulness.
    `comparison_homEquiv` then fixes the other compactifications' bijections.
    Verdict after repair: both the comparison family and the relative adjunction
    are tied to the actual canonical constructions. A global twist with the
    chosen adjunction held fixed now fails this equation; changing the adjunction
    itself is the legitimate existential choice of f^times and its adjunction.
11. Scope: the source's elliptic-curve paragraph excludes an ambient interpretation.
    Both module/proof docstrings retain that warning. None of
    `HasAmbientExceptionalRightAdjoint`, exceptional-adjoint admissibility, or
    constructibility/Tor preservation is asserted or assumed. The three definition
    dependencies name the stronger optional notion and explain the formula; they
    are not missing predicates in this restricted conclusion. Verdict: source
    scope retained; this finite-stage corollary does not restate the other stages
    of the exceptional-inverse-image definition.

Edge cases: zero K and L are included and the normalization maps have the same
zero Hom types; an empty X and empty compactification satisfy the WithBot bound
with d=0; dimension-zero compactifications and identities are included. No density,
nonemptiness or chosen affine-chart hypothesis is imposed. The level n=1 is included,
n=0 is excluded exactly by the positive-level convention, and l=p is excluded exactly
as in the source. There is no index-set restriction; identity and composite refinements
are covered by the all-pairs family. Schemes have universe u, coefficient modules
universe u+1, and the small sites keep object universe u+1 and morphism universe u.
No equality between those site universes or bound on the number of sheaves is added.
All variables and universes are explicitly bound under `autoImplicit false`.

The prior scalar-twist counterexample was rechecked with the geometric point and
its two non-dense compactifications over F_3 coefficients. The repaired
`comparison_normalized` rules out a nontrivial relative factor between the two
canonical comparisons. The new `homEquiv_normalized` additionally rules out changing
all Hom bijections while keeping the actual chosen etale adjunction fixed. Essential
image membership provides representatives in both P's; naturality extends these
normalizations to isomorphic objects, so no non-representative loophole remains.

Independent searches used different wording from the worker: LeanFinder query
`natural hom set equivalence compact support pushforward etale origin bounded derived
proetale sheaves` returned eight etale-site/module-pullback facts, none this statement.
Loogle query `CategoryTheory.Adjunction.mkOfHomEquiv` returned the generic constructor
and its three projection equations, none the geometric result. Mathlib grep
`comparisonClass|CompactificationOriginIso|homEquiv.*Shriek` returned zero hits.
Direct rg on Mathlib, the older `WeilConjectures` tree and the current `lean/Sheaf`
with `ClassAdjunction`, `class.*[Aa]djunction`, `homEquiv.*[Oo]rigin`, and
`[Aa]djunction.*[Oo]rigin` found no exact combined theorem or helper. I opened the
existing upstream `rightDerivedUpperShriekHomEquiv` and its section assumptions:
it requires `Etale.HasBoundedBelowUpperShriek`, which this geometric node must
establish rather than assume. It therefore cannot replace this delivery by an
`existing: true` record. Existing comparison definitions are reused in both
normalization equations, not copied. No new definition node is needed; the structure
is the dependency node's own explicitly specified relative-adjunction data.

The three dependency repairs were checked individually. `def-sf-fullcd-class` and
`thm-sf-fullcd-class` record the exact existing displayed FullCD notion and theorem,
read with their actual section binders. `thm-sf-ambient-adjoint-class` has the same
hypotheses as the item, the larger P of all bounded-below etale-origin inputs, and
all three conclusions of its node, now with the chosen-adjunction normalization.
Its proof docstring follows the vanishing, Brown representability, comparison,
full-faithfulness and canonical-independence chain. Its helper structure has actual
data and equations, and is in `lean.declarations`. No definition has sorry data,
no new axiom or arbitrary comparison dictionary is introduced, and both theorem
proofs remain only `sorry`.

The inherited claim in the FullCD definition's explanatory prose identifying ALL
etale-origin sheaves with constructible sheaves remains false (an infinite-dimensional
constant F_l sheaf on an algebraically closed point). The worker already flags it.
The recorded definition's two formulas do not assert that converse; the valid
constructible-to-origin inclusion is what this item uses. No item statement correction
or new node was needed, so no `statement_change` or citer audit applies. I changed
only the dependency helper's missing normalization, the corresponding existential
adjunction binders and helper applications in both theorem signatures, the source
explanation of that equation, and the Lean records. The signatures are kept verbatim
in their node records. The worker report's description of the earlier `Nonempty`
conjunct is superseded by this explicit chosen witness.

Validation: the explicit two-file `scompile.py` run typechecked both revised statements;
its single long-docstring-line warning was repaired. The subsequent exact-file
`deliver2.py NL cor-sf-ambient-adjoint-discharge --no-push` run compiled both full sibling
modules and checked both existing dependency declarations without warnings, and printed
`OK (dry run): commit fab7e94ab2 passes the preflight and compiles; nothing pushed`.
Both theorem `lean.statement` strings were independently compared to the complete file
signatures before `:= by` and are verbatim equal. All lines meet the 100-character
convention. No library-wide build, live source edit, or proof completion was performed.
