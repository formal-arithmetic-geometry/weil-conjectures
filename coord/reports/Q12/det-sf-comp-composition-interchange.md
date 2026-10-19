## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.properOpenInterchange`
in `Sheaf.Paper.ProEtaleProperOpenInterchange`. Only this theorem is postponed;
its proof is `sorry`. Its docstring contains the complete seven-step DAG argument,
grouped under the three source clauses. The node's natural-language statement and
its dependency lists are unchanged. The stage-1 repair note is resolved and concerns
the proof split, not an outstanding Lean interface repair.

Hypothesis and clause correspondence:

* The standing setting is rendered by `ℓ`, `Fact ℓ.Prime`, a field `k : Type u`,
  `Fact (ringChar k).Prime`, and `Fact (ringChar k ≠ ℓ)`. Each of `X`, `Y`,
  `Ybar`, and the compactifying scheme has an `Over (Spec (.of k))` structure
  and locally finite type, quasi-compact, and separated structure morphism.
  All four named arrows have `IsOver` instances. `X` denotes the paper's Xbar.
* `Λ` is an internal commutative ring in condensed abelian groups. The `_hΛ`
  disjunction spells out admissibility rather than replacing it by an arbitrary
  commutative condensed ring: finite discrete commutative rings killed by an
  ell power, Z_ell, Q_ell, O_E and E for finite intermediate fields, and Qbar.
  `Mon.mk` isomorphisms identify the supplied coefficient with the listed ring
  objects, preserving both its additive and multiplicative structures. Discrete
  finite coefficients may have carriers in `Type u`. The other rings use the
  exact upstream constructors. In particular the final case is
  `Profinite.padicAlgClRingObj`, whose sections take values in a finite
  subextension; it is never the full continuous-function ring of Qbar.
* `p : X ⟶ Y` has `[IsProper p]`. `i : Y ⟶ Ybar` has
  `[IsOpenImmersion i] [QuasiCompact i]`.
* `c : Compactification.BoundaryCompactification (p ≫ i)` uses the dependency's
  exact notion. `c.obj.obj` is its upstream compactification: Z is W,
  `.i` is j', `.g` is r, and `.comm : p ≫ i = j' ≫ r` is its triangle.
  The full-subcategory object property retains quasi-compactness of j'.
  Scheme-theoretic density is `[IsSchemeTheoreticallyDominant c.obj.obj.i]`,
  precisely the density definition of sk-def-nagata-sketch-data.
* Clause (1) is `c.obj.obj.g ⁻¹ᵁ i.opensRange = c.obj.obj.i.opensRange`.
  These are `Scheme.Opens`, so this is equality of open subschemes with their
  restricted structure sheaves. The assertion that r restricts to p is already
  the compactification triangle `.comm`, under this open identification; it is
  not an additional unsupported identification of schemes or only a point-set
  equality.
* Clause (2) quantifies over every `A` of the ambient unbounded
  `DerivedCategory (CategoryTheory.Mod ... (condensedRingObj Λ X))`.
  The existential arrow has source `D(i_!).obj (Rp_*.obj A)` and target
  `Rr_*.obj (D(j'_!).obj A)`, with precisely the existing functors.
  `compositionInterchangeIsNormalized ... A m` is identity on restriction:
  write η_i and η_j for the canonical derived open units and β for the
  canonical restriction mate. Its equation is
  `(η_i(Rp_*A) ≫ i^*(m)) ≫ β(j'_!A) = Rp_*(η_j(A))`.
  The displayed code uses the existing open adjunction's `homEquiv` for the
  left parenthesis. After the two invertible open units and open restriction
  base change, this is exactly the identity of `Rp_*A`. The next conjunct
  quantifies over every arrow m' satisfying the same equation and asserts
  `m' = m`. Uniqueness is required among normalized arrows on the entire
  unbounded category, independently of any localizing hypothesis.
* Clause (3) is the final implication
  `localizingClosureProEtale Λ X A → IsIso m`, for that same unique arrow.
  It uses the landed definition's actual constant-model constructible finite-Tor
  class and ambient localizing closure; it imposes no derived completeness.

The three auxiliary definitions belong to the interchange notion and are listed
in `lean.declarations`. `compositionInterchangePullback` applies the existing
`upperStarComp` comparisons and the triangle equality through the existing
`mapDerivedCategoryNatIso`/`mapDerivedCategoryCompIso` constructions.
`compositionInterchangeRestriction` is its mate through
`derivedUpperStarLowerStarAdjunction`, transported by the existing exact-pullback
identification, using the actual counit. `compositionInterchangeIsNormalized`
is the equation above. These contain real data and require neither a choice
from `Nonempty` nor a new postponed theorem. Their blueprint/source docstrings
identify their use in source proof (2).

Dependency declarations read and used:

* sk-def-sfb-dc-setting: the setting binders and the upstream
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its
  docstring fix the same separated finite-type scheme convention. This item
  accepts an arbitrary supplied compactification, so does not replace c by that
  chosen compactification.
* sk-def-localizing-closure: `Sheaf.Paper.LocalizingClosure`,
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale` and
  `CategoryTheory.localizingClosure`.
* sk-def-nagata-sketch-data: `Sheaf.Compactification.BoundaryRefinement`,
  `AlgebraicGeometry.Compactification.BoundaryCompactification`, its
  `QuasiCompactObjects` and `DenseBoundaryCompactification` conventions.
* sk-def-sfb-qlbar-condensed has no lean record but its closed upstream audit
  supplies `Profinite.padicAlgClCondensedRing` / `padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. Their full
  definitions explicitly use finite-intermediate-field-valued functions.
* The coefficient constructor for a finite carrier of universe u is the already
  published `Profinite.continuousCoefficientRingObj` with its commutativity
  instance from `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`.
  Q_l and Z_l use upstream `continuousMapRingObj`; O_E and E use upstream
  `padicIntegersRingObj` and `padicSubfieldCondensedRing` followed by the existing
  `sheafCompose` forgetful functor. No second coefficient construction is added.
* Derived push/pull and their adjunction are the recorded
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`
  declarations. Open extension and its exact derived adjunction are the existing
  `openImmersionLowerShriek` and
  `derivedOpenImmersionLowerShriekUpperStarAdjunction`.

All available proof-dependency modules are imported, including the localizing
isomorphism locus, ring-sheaf open/closed sequence and detection, termwise
homotopy adjunction, localization adjunction, and scheme properness facts.
The proper-image-localizing-open, comp-coherence-single, and three coefficient
proper-base-change nodes have no recorded modules at this snapshot; no nonexistent
imports are added. The cartesian-coefficient closed/upstream declarations and
constructible definition are already reached by public imports. No import-cycle
exception is needed.

Edge cases checked: the zero coefficient ring is admitted (n = 0 can kill 1);
all finite ell-power-torsion rings are allowed, not only residue fields or
quotients of one chosen valuation ring. E = Q_l is allowed and gives the usual
integral/rational cases. The Qbar branch uses finite-subextension sections even
on an infinite profinite set. The zero complex is included; no boundedness or
Tor assumption is placed on clause (2). Empty source/open schemes are permitted:
with density the corresponding compactifying scheme is empty, and the unique
arrow is between zero objects. Identity opens and identity proper arrows are
permitted. Nonreduced schemes retain scheme-theoretic density, and equality in
Scheme.Opens retains their structure sheaves. The localizing clause admits
unbounded coproducts of generators and does not impose completeness. No arbitrary
indexing universe or equalities between site object/morphism universes are added.

Searches (2026-10-18):

* msearch.py leanfinder: "Extension by zero commutes with proper derived pushforward
  in a cartesian open immersion square on pro etale module sheaves". Eight hits:
  ordinary scheme/module pushforward composition components, module pullback free
  formulas, and sheaf pushforward adjunction formulas. No match.
* msearch.py loogle: "CategoryTheory.Adjunction". Twelve generic adjunction
  constructors and identity/equivalence adjunctions; none is this statement.
* msearch.py grep: "lowerShriek|extensionByZero|proetale", subdirectory
  AlgebraicGeometry. Ten pro-etale-site/ell-adic-sheaf hits; no interchange.
* rg in upstream WeilConjectures/SixFunctors for interchange/Interchange found
  the etale finite-coefficient exchange module. It is a different site and
  different coefficients, and cannot state this module-object pro-etale result.
* grep -rn for the exact item id in upstream WeilConjectures returned no hits.
* rg in the project's Sheaf sources for interchange and the proposed declaration
  names found finite etale interchange, coefficient/system variants and their
  consumers, but no pro-etale condensed-module proper/open interchange.
  The full proposed declaration names are fresh in Mathlib and upstream.

No statement dispute, statement correction, new independent notion, or dependency
repair is required.

## Second reading by Q12

The dispatcher expressly forbids starting another agent; this is the worker's
separate second pass, with the node, its four dependency statements, the source
section and the final Lean file open. The maintainer performs the independent
review of the delivery.

The second pass caught and repaired the density interpretation: the dependency
specifies scheme-theoretic density, so the final signature uses
`IsSchemeTheoreticallyDominant`, rather than merely `DenseRange`. It also retained
an explicit `[QuasiCompact i]` binder. It checked all four standing scheme
structures and all four over-field arrow structures, proper p, the supplied
quasi-compact compactification, its triangle, and the complete six-case
coefficient disjunction. The O_E and E alternatives include all finite
intermediate fields, not a fixed coefficient extension. The Qbar constructor
is exactly the dependency's finite-subextension ring.

For clause (1), equality of opens is scheme-level and the restriction triangle
is carried by the compactification. For clause (2), the domains and codomains of
the constructed pullback comparison, adjoint restriction map, and normalization
equation were checked successively: both sides of the equation are maps
`Rp_*A → Rp_*j'^*j'_!A`. Thus it compares the desired identity using the exact
canonical open units. It does not assume the conclusion by taking a comparison
isomorphism as input. Existence and uniqueness hold for all unbounded A; the
localizing hypothesis occurs only in clause (3), for the same arrow. Definitions
contain no sorry or arbitrary-map parameter. The only postponed theorem matches
the original node. No independent second-reader claim is made.

Validation: the final theorem signature, including the scheme-theoretic-density
binder, passed `scompile.py Q12 det-sf-comp-composition-interchange` in both
sandbox and library module modes with no errors or warnings. There is one
`sorry`, in `properOpenInterchange`, and all Lean lines are at most 100 characters.
The copied node differs from the base only in `lean`; its `lean.statement` is the
verbatim theorem signature. Delivery preflight additionally compiles the exact
submitted source, including the final documentation-only main-declaration list.
