## Worker report

Q152 states `AlgebraicGeometry.Etale.relativeKummer_normalized_stalks` in
`Sheaf.AlgebraicGeometry.RelativeKummerNormalizedStalks`. All postponed proofs are
named theorems with dedicated DAG statement nodes and source/proof-plan docstrings; all construction data is supplied.
The item statement is unchanged. There is no statement dispute.

Hypotheses: `(k : Type u) [Field k] [IsAlgClosed k]` is the algebraically closed
base; `ℓ N`, `hℓ`, `_hN`, `hℓk` mean prime ℓ, N ≥ 1 and ℓ invertible.
`[CommRing A] [Algebra (ZMod (ℓ ^ N)) A] [Module.Free ... A]
[Module.Finite ... A]` gives precisely the finite free commutative coefficient
algebra, including rank zero. `ζ` and `hζ` fix its primitive root. `B` and `p`
are an arbitrary k-scheme and its named structure map, with no finiteness,
connectedness or Noetherian hypothesis. `b : Bool` ranges over the polynomial
and Laurent polynomial curves of the existing `KummerLine.curve`. The exponent,
its positivity, annihilator and invertibility are the existing
`relativeKummerPositive`, `relativeKummerAnnihilator`, and
`relativeKummerFieldExponentUnit` terms. `Ω`, its field and algebraic closure
instances, and `s : Spec Ω ⟶ B` quantify over all geometric points.

The existing `Scheme.finiteEtaleTateLine` and `relativeKummerLinePlus` represent
L_T, with no new copy of the root sheaf, tensor product, or derived category.
The actual pullbacks define C_B, C_S and their projections. S is the existing
`Scheme.strictHenselizationScheme s`, the small affine pointed-neighbourhood
limit, with its existing structural morphism.

Clause correspondence:

- `RelativeKummerNormalizedStalk` first asserts invertibility of the canonical
  `normalizedKummerH`, then supplies Φ in D+(ModuleCat A).
  `Φ.hom ≫ normalizedKummerH = normalizedKummerTheta` specifies Φ uniquely as
  restriction/exchange/Leray followed by inverse h*. No fibre base-change
  isomorphism is a parameter, assumption or definition.
- `normalizedKummerTheta` calls `moduleStrictLocalTheta` with the canonical
  `relativeKummerLinePullback` coefficient isomorphism. Its factors are the
  derived germ restriction, `derivedBaseChangeMapPlus`, and `moduleLerayPlus`.
- The `∀ q : ℕ` equality of cohomology morphisms in that predicate is the
  displayed all-global-classes identity, composed with the invertible Hq(h*).
  Equality of A-linear maps includes every x, not only constants or generators.
  `normalizedKummerEdgeGerm` is the derived global-germ map after inverse Leray;
  its Hq is precisely the germ of the Leray edge section.
- The final equation of that predicate identifies the stalk unit (with the
  canonical constant-stalk identification) with `normalizedKummerGlobalSection`
  of `normalizedKummerConstantMap`. The latter sends a to ζ tensor a; it is
  constructed by the ordinary section on 1 and A-linearity.
- The `true` case of the final dependent match in
  `RelativeKummerNormalizedStalk` states directly on the same existential Φ:
  `normalizedKummerGeneratorPlusMap ... C_B t ≫ H¹(edgeGerm) ≫ H¹(Φ) =
  normalizedKummerGeneratorPlusMap ... C t`.
  Its generator is the unique module-derived realization of the ordinary
  abelian boundary followed by scalar insertion, transported to bounded-below
  derived sections by the inverse of `rightDerivedFunctorPlusCompatibility`.
  Thus both sides and H¹(Φ) live in exactly the same module cohomology model.
  The previous abelian-pullback-only predicate has been removed.
- The second conjunct of the theorem is conditional on the absolute line
  constant map being invertible and every positive absolute degree vanishing.
  Its conclusions give the actual twisted derived unit, the ζ-untwisted
  derived unit, the degree-zero relative map, and every other relative degree.
- The third conjunct uses the absolute constant map and
  `normalizedKummerGeneratorMap` and vanishing outside 0,1; it concludes
  invertibility of the relative constant and `normalizedKummerRelativeGenerator`
  maps and vanishing of all the remaining relative cohomology sheaves.
  The generator maps are the actual derived realization/edge of the specified
  ordinary boundary, not arbitrary maps or chosen isomorphisms.
- The last `∀ a : A` equation is ordinary cohomology pullback along the actual
  relative punctured inclusion; it preserves the same ζ tensor a constant.

Dependency declarations used: `KummerLine.curve`, `structureMap`, `inclusion`,
`coordinateUnit` (Sheaf.AlgebraicGeometry.KummerLineGeometry);
`relativeKummerLinePlus`, `relativeKummerLinePullback`, `relativeKummerUnit`,
`relativeKummerGlobalPullback`, `relativeKummerCohomologyPullback`,
`relativeKummerConstant`, `relativeKummerClass` and the exponent witnesses
(Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance);
`kummerExchangeConstant`, `kummerExchangeEdge`, `kummerExchangeLower`
(Sheaf.AlgebraicGeometry.RelativeKummerExchangeGenerators);
`ordinaryFiniteClass` (Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer) and
`ordinaryFiniteClass_bijective_arbitraryBase`
(Sheaf.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase);
`moduleLerayPlus` (Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback);
`strictLocalNeighbourhoodSection` (Sheaf.AlgebraicGeometry.StrictLocalSectionCone);
`Scheme.strictHenselizationScheme`, `strictHenselizationStructuralMap`
(WeilConjectures.AlgebraicGeometry.StrictHenselization);
`Scheme.pointSmallEtale`, `sheafFiber`, its germ and constant-sheaf comparison;
`derivedBaseChangeMapPlus` (WeilConjectures.SixFunctors.BaseChange.Derived).
The generic derived single, exact functor, adjunction, shift, and homology
constructions are Mathlib's existing APIs. The recorded abelian strict-local
interface is publicly retained rather than shadowed.

Edge cases checked against these signatures: empty B imposes no geometric-point
existence and the relative assertions are assertions of sheaves on the empty
site; disconnected and non-quasi-compact B are allowed; the affine projections,
not B, are qcqs. Rank-zero A is allowed (no Nontrivial A instance). Degree 0 is
separate, degree 1 is retained for the punctured curve, higher degrees are
conditional rather than assumed; negative degrees are zero by connectivity of
right derived functors on a sheaf. The strict localization is the specified
small model, not the differently sized official strictLocalization object.
No extra equality between site and coefficient universes is imposed.

Searches: msearch LeanFinder query “Canonical derived strict henselization stalk
comparison for affine and punctured lines preserving global edge classes and
Kummer generators” returned eight unrelated scheme-stalk lemmas; Loogle
`"stalk", "cohomology"` returned zero; Mathlib grep
`stalk.*(cohom|[Dd]erived)|[Ee]dge.*[Ss]ection` returned zero. LeanSearch
“Canonical module strict henselization germ restriction and normalized derived
Kummer stalk comparison” returned eight structure-sheaf germ results. The later
LeanSearch query on canonical derived global realization of an ordinary Kummer
class and its relative edge generator returned field Kummer-extension results;
Loogle `"Kummer", "derived"` returned zero. Direct rg on the proposed arrow
names in WeilConjectures and Sheaf returned no declarations; DAG name search
returned none, and blueprint_refs search “normalized Kummer generator” found
zero nodes. Existing generic class and edge APIs found by source rg are reused.
Full msearch result summaries are recorded in each new node.

Validation: every delivered module is compiled individually through scompile.py
in dependency order. The initial cohomology-arrow expansion exceeded the limit;
explicit codomains and smaller specialized interfaces removed that failure.
No limit was raised and no live library was edited.

## Second reading by Q152

This dispatcher forbids starting other agents, so this is a separate second pass
by the same worker; the maintainer provides the independent review. Re-read the
unchanged node, current blueprint Step 2, and all eight repaired files. The first pass
lacked the conditional conservative-stalk consequences; the final theorem now
states both units and all relative degree claims explicitly. Checked that the
coordinate equality now uses the same existential Φ directly, with both generator
maps canonically transported to D+ cohomology. The old abelian-only identity was
insufficient and has been removed. Checked the Kummer generator uses the inverse
of the bijective *specified* ordinary-class comparison; no mere Nonempty choice
occurs. Extracted proof obligations for exact module stalks and strict-local
sections as named theorems and installed instances from those terms. The new
arrows do not replace existing root, tensor, cohomology or curve definitions.
All hypotheses and clauses are matched above; no mathematical statement change
was needed.

## New nodes

`def-pur-normalized-kummer-global-arrows` owns the specialized family, global-germ,
Leray-edge-germ, ζ-constant, untwisted-unit and stalk-unit arrows. Source: current
blueprint Step 2. The global section-to-stalk transformation and its exact
normalized composites were absent; generic germ, Leray and adjunction APIs are
reused. LeanSearch, LeanFinder/Loogle, Mathlib grep, source/library rg, DAG search
and blueprint search are recorded above and in its JSON.

`def-pur-normalized-kummer-cohomology-arrows` owns the unique derived realization
of the ordinary scalar-extended Kummer boundary and its global realization.
Source: Step 2 ordinary-Kummer normalization, Stacks 03PL and 072W. The existing
ordinaryFiniteClass is a map; its existing bijectivity supplies a uniquely pinned
inverse, not a second cohomology definition. Searches found the existing generic
comparison but no such specialized canonical arrow.

`def-pur-normalized-kummer-generator-arrows` owns H0 of that shifted global
realization, the actual relative edge generator, and the base-changed inclusion.
Source: Step 2 generator and restriction clauses. Searches found the generic
kummerExchangeEdge but no scalar-normalized specialization; this definition
applies that API to the already specified class and actual coordinate.

`def-pur-relative-kummer-canonical-arrows` is an existing:true attachment to the
plain definitions in `RelativeKummerStrictLocalInvariance`. It records the finite
root line, normalized inverse-image comparison, actual unit/global pullback,
ordinary cohomology pullback, constant and Kummer classes, and arithmetic
witnesses. Source: Step 2 and the declarations' original source docstrings. It
introduces no Lean file or declaration and invokes no invariance theorem.

`def-pur-kummer-exchange-class-arrows` is an existing:true attachment to
`kummerExchangeConstant`, `kummerExchangeLower`, `kummerExchangeEdge` and their
adjunction helpers in `RelativeKummerExchangeGenerators`. Source: Step 2's Leray
edge construction and Stacks 072W. It imports no exchange-generators assertion
into statement dependencies. The theorem remains a proof dependency of the item.

`def-pur-module-strict-local-section-restriction` owns the actual module section
restriction along each representative affine pointed-neighbourhood limit leg.
It reuses `strictLocalNeighbourhoodSection`, inverse-image unit, the geometric
germ and the canonical terminal/global-section comparison; no uniqueness or
exactness is assumed in this definition.

`def-pur-module-strict-local-restriction` owns the uniquely specified natural
module germ restriction, its derived transformation and the specified
exchange/Leray/coefficients composite. It consumes the dedicated properties
statement through its finite-limit, finite-colimit and unique-existence proof
terms. This new node replaces the attempted overwrite of Q1's abelian node.

The searches recorded in these new nodes include LeanSearch on module strict
localization germ restriction and Kummer edge arrows (eight unrelated module or
topological-germ results), Loogle on `PreservesFiniteLimits` and `sheafFiber`
(two existing generic finite-limit instances), Mathlib grep (zero specialized
hits), source and library rg (existing plain definitions found and reused), DAG
rg (only the theorem nodes carried those plain definitions) and blueprint search
(zero matches for strict local module restriction).

## Helper statement nodes required by R2

`lem-pur-module-strict-local-restriction-properties` owns
`moduleStrictLocalRestriction_properties` in its own module. The statement is
exactly the conjunction of finite-limit preservation by the module stalk,
finite-colimit preservation by strict-local module sections, and existence of a
unique natural transformation with every specified affine pointed germ equation.
Its proof plan records filtered colimits, the strict-henselian section argument,
cofinality, cocone descent and uniqueness. The former three sorried helpers are
replaced by this single theorem and projections from it; the def modules contain
no sorry.

`lem-pur-kummer-line-inclusion-over` owns `normalizedKummerInclusion_over` in its
own module and states the equality of the actual structure maps after the
polynomial-to-Laurent inclusion, for every field. Its proof is postponed with
the coefficient-preserving ring-map proof plan. The generator definition consumes
this equation to form the actual relative pullback map.

Both statement nodes are explicitly requested by return R2. They have genuine
statement kind, proof steps and source; they have not been disguised as
definition nodes to fit a gate.

## Returned delivery repair

Compared the retained aa7f7fed0acf delivery with the current read-only node and
source records. The item and all named helper definitions remain the same
canonical mathematical objects. The wrapper rebases the repaired sandbox on the
current server branch when constructing the review commit.

R1: Added existing:true definition nodes for the plain declarations in the two
published Kummer modules. Replaced the item and all three normalized-arrow nodes'
references to `lem-pur-relative-kummer-strict-local-invariance` and
`lem-pur-relative-kummer-exchange-generators` in stmt_deps with these definition
nodes. The original theorem nodes stay in the item's unchanged proof_deps. There
is no `.choose` of either invariance/exchange theorem and no copied definition.

R2: Removed the sandbox copy of
`def-weil-pbc-strict-henselization-restriction`; its landed Q1 existing:true
record, seven declarations, note, and citers remain untouched. Added new module
restriction definition nodes and the two helper statement nodes above. Every
module has exactly one owning node; each postponed theorem now has its own
matching statement node. The module still publicly imports the old interface,
without repointing its node record.

R3: Removed `RelativeKummerNormalizedCoordinate`, which only stated an abelian
pullback identity. Added the explicit equality on H¹ of the same canonical Φ
inside `RelativeKummerNormalizedStalk`. The `false` case has no coordinate
condition; the `true` case is the actual generator/edge/Φ equation. The new
`normalizedKummerGeneratorPlusMap` is defined by composing the already specified
generator with H¹ of the inverse of the canonical total/bounded-below derived
sections comparison. The unique ordinary-class realization pins its input to
the ordinary scalar-extended Kummer boundary. No unstated comparison is used.

The other clauses and all hypotheses, including empty bases, rank-zero A,
arbitrary bases and coefficient/site universes, have been retained unchanged.
No source-statement correction or target modification was required.

Repair validation: scompile.py compiled all eight delivered modules separately in
dependency order, with no errors or warnings other than the expected sorry warnings.
The repaired packet passed deliver2.py --no-push (d7f16c98f8a). The reported
modules have one owner each; both existing:true attachments were checked against
the published sources, and Q1's dependency record is absent from this delivery.

## Repair of returned head 5915004dfe4b

The two new helper theorem nodes
`lem-pur-kummer-line-inclusion-over` and
`lem-pur-module-strict-local-restriction-properties` now have `status: unsplit`.
They retain their actual statement kind, their complete source/proof plans,
and the recorded Lean theorem signatures with postponed proofs.
`stages/1-dag.md` section 3 requires new statement nodes to enter as unsplit;
`tools/review_split.py` lines 165–171 allows split status only for the stage-2
definition-node exception. The previous split status incorrectly applied that
definition exception to these theorem nodes. No Lean declaration, dependency,
mathematical statement, or existing node status changed in this repair.
The wrapper constructs a fresh commit against the current server branch.

Second reading of this repair: checked the two files against the returned
5915004dfe4b records; only their status fields changed. The eight Lean modules
remain those compiled in the preceding repair, including the explicit equation
on H¹(Φ), existing-definition attachments, and untouched Q1 restriction record.
