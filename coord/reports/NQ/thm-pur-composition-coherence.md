## Worker report

This repairs the substantive faults in returned head 621f42b0dca3. I inspected the
retained packet and ran the prescribed initial dry run before changing it. That run
failed at the 60-second compile limit. The packet already contained the corrected
canonical-map formulation, but two unfinished helpers supplied isomorphism data by
`sorry`; those helpers and the expensive instance comparisons are now repaired.
The returned arbitrary-arrow theorem is not retained.

The statement is the current main-20261015 composition-coherence statement in
`sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.md`, read with
`def-pur-conventions` and `def-pur-smooth-purity-map`. No natural-language statement
is changed. The canonical source-identification helpers belong to this very display;
they do not define a replacement purity map or a second exceptional functor.

Hypothesis correspondence:

- `P : PurityFiniteSetting.{u}` contains the global finite-field datum, ell distinct
  from p, the literal finite extension of the fixed coefficient closure, and the
  positive level. `P.Ring` is O_E/(varpi_E^n), and `P.Coefficient` is its standard ULift
  for the fixed-module coordinates. No ramification restriction is imposed.
- The three `Over` instances give X,Y,Z over k; the locally finite type, quasi-compact
  and separated structure morphisms give the standing separated finite-type schemes.
  These binders are in `section Geometry` and are generalized into the theorem.
- `f`, `g`, and their `IsOver` instances are the two composable k-morphisms.
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` give their standing domain.
- `d e : ℕ` and `SmoothOfRelativeDimension d f`, `SmoothOfRelativeDimension e g`
  give exactly the two smooth relative dimensions. The composite smoothness instance
  of dimension d+e is inferred. Compactifications are supplied internally by the
  finite-type-over-field construction. Neither is a new hypothesis.
- `K : Scheme.proEtaleDerivedCategory Z P.Ring` and
  `hK : finiteTorConstructible ... Z K` give the original small-pro-etale D^b_ctf
  object. There is no ordinary-etale replacement for K and no invertible-exponent
  or arbitrary Tate-twist instance binder.

Conclusion correspondence, in order:

1. `P.smoothPurityMap (f ≫ g) (d + e) K hK` is the specified gamma_gf.
2. `compositionSourceIdentification` is a definition, not an argument. It maps
   `compositionSourceFixed` through the canonical intrinsic realization. That fixed
   identification first uses `smoothPurityReassociation`, the exact pullback
   compositor, `compositionPowerAdd`, and the tensor associator; it then uses inverse
   Tate pullback and inverse monoidal pullback, the two shift reassociations, and
   the realization unit at Y. Each of these factors is individually fixed by its
   normalization equation, with both intermediate objects recorded.
   `compositionPowerAdd` comes from the ordered shifted
   root-line powers via recursive unit/associator concatenation and derived symmetry.
   The symmetry uses even shifts, so the Koszul factor is +1.
3. `(compositionShiftedPullback f d).map (P.smoothPurityMap g e K hK)` is exactly
   Lf*(gamma_g,K)(d)[2d]. The functor is inverse realization, exact fixed-scalar
   pullback, tensor with A(d) and shift 2d, then realization.
4. `P.smoothPurityMap f d ((compositionExceptional g).obj K) ...` is gamma_f at
   Rg!K. Its finite-Tor constructibility is the theorem `compositionExceptional_ctf`,
   not a hypothesis supplied by the caller. Its proof plan transports the existing
   final clause of `smooth_exceptional_preservation` through the canonical exact
   realization and derived-composition comparisons.
5. `(compositionExceptionalIso f g K hK).inv` is c inverse. Its forward map is
   `standingExceptionalComposition P f g` at the bounded constructible inverse
   realization of K, followed only by the intermediate realization unit and the
   outer realization. `compositionInput_bounded` states the intrinsic/fixed domain
   transport. `isIso_compositionExceptionalMap` states the invertibility of precisely
   this mate using alpha inverse and the adjunction triangle identities. `asIso`
   uses that proof; it does not select an unconstrained isomorphism.

Every definition contains actual data. Each presentation transport has a named
normalization predicate requiring HEq to the complete published canonical isomorphism,
including its map and inverse. Its named existence-and-uniqueness theorem postpones
only the proof that the presentations match. Choice of that unique normalized value
therefore does not choose an unconstrained isomorphism. The same technique is already
used by smoothPurityTensorShift. The finite ring's Noetherian property is a named
proof, obtained from finiteness, and is not a hypothesis of the main theorem.

The source identification's eight factors have their intermediate objects written
out in `compositionSourceStage`. `CompositionSourceNormalized` fixes each factor by
HEq to, respectively, shift reassociation, pullback composition with power splitting,
tensor associativity, inverse Tate pullback, inverse tensor pullback, inverse outer
shift reassociation, inverse inner shift reassociation, and the realization unit.
It fixes the resulting isomorphism to their ordered composite. The named uniqueness
theorem has the complete endpoint and uniqueness proof in its docstring; the
`compositionSourceFixed` definition extracts exactly this normalized composite.
Splitting the former fourth factor into Tate pullback and tensor pullback avoids
repeated normalization of the coefficient-category instances. This keeps all data
fixed independently of gamma and c and compiles within the existing limit.

The zero and successor equalities expose the existing ordered tensor-power recursion;
`eqToIso` transports their endpoint equalities in the recursive concatenation.
Each postponed theorem is named, is listed in this node's lean.declarations, carries
the node's source and blueprint tag, and has its natural-language proof. These
helpers state the interfaces of the very identification in this node's display;
they are not independent replacement notions. Only proofs are postponed in stage 2.

Dependency declarations actually used:

- `Sheaf.Paper.SmoothPurityMap`: `smoothPurityMap`, `smoothPurityPullback`,
  `smoothPurityExceptionalOver`, `smoothPurityReassociation`,
  `smoothPurityComparisonTensor`, and `smoothPurityUnitIso`.
- `Sheaf.Paper.StandingExceptionalComposition`:
  `AlgebraicGeometry.ProEtale.standingExceptionalComposition`, including its
  specified compact-support comparison and composite standing Hom bijections.
- The publicly retained finite coefficient twist interface:
  `diagonalTwistEtale`, `diagonalTwist`, `diagonalExponent_annihilates`,
  `diagonalExponent_isUnit` and `Etale.affineLinearBaseCoefficient`.
- `Sheaf.AlgebraicGeometry.VectorBundleIntegration`:
  `Etale.vectorIntegrationBaseCoefficientPullback`; `ProjectiveLineTrace`:
  `Etale.projectiveLineTraceTransport`, normalized by roots/pure-tensor equations.
- FiniteCoefficient upper-star monoidality and exact-derived comparisons,
  `ProEtale.upperStarComp`, `Functor.mapDerivedCategoryNatIso`,
  `Functor.mapDerivedCategoryCompIso`, and `sfDerivedComparisonPullbackIso`.
- `Sheaf.Paper.SmoothExceptionalPreservation`: the preservation theorem underlying
  the named transport statement. The finite-Tor predicate is
  already supplied through the recorded smooth-purity-map and convention dependencies.
  The existing preservation theorem is imported for the transport helper's proof;
  no new statement dependency or natural-language statement change is needed.

Proof-only imports were checked. The former category-valued pro-etale comparison
imports reached by `CohomologicalSmoothnessTheorem`/`CohomologicalSmoothComposition`
collide with the finite-coefficient paths used by the canonical gamma. In particular
compiling that closure reports both modules declaring
`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`. The working module therefore
uses the smaller finite-coefficient interfaces actually needed for this statement.
The proof plan still explicitly names the tensor-formula, DNC and gluing dependencies.

Edge cases checked against the source and the definitions:

- f=g=id and d=e=0: no arbitrary gammaGF=0 can be substituted; all three arrows are
  the specified purity arrows and c is the specified standing counit mate.
- d=0 or e=0: the ordered power concatenation uses the tensor unitor, and all shift
  cancellations and exact pullback units remain defined. No positive dimension binder.
- K=0: all functor values and maps are the zero-object values of the same constructions.
- Empty schemes: no point, nonempty chart or maximum over a cover is used in these
  definitions. Invertibility of the annihilating exponent is obtained from the k-map.
- Ramified E with n=1, or n not divisible by the ramification index: the existing
  exponent ell^n annihilates A and is invertible on every k-scheme. No chosen root.
- The small pro-etale site's object universe u+1 and morphism universe u are retained;
  the inverse/forward realization changes only the module presentation.

Searches repeated for this repair:

- `msearch.py ... leanfinder "canonical smooth purity compatibility under composition
  on finite Tor constructible pro etale complexes"`: 8 hits, smoothness and etaleness
  permanence, including `isSmoothOfRelativeDimension_comp`; no purity-map coherence.
- `msearch.py ... loogle "smoothPurityMap, standingExceptionalComposition"`: 0 hits,
  unknown `smoothPurityMap` in Mathlib. The two actual project declarations were read.
- `msearch.py ... grep "smoothPurity.*[Cc]omposition|standingExceptionalComposition"
  Mathlib`: 0 hits.
- `rg` in the upstream and project source: the upstream
  `nonempty_iso_dualizingComplex_comp` is only existence of a dualizing-object iso,
  with ordinary-etale objects and additional twist data; it is not this specified-map
  equality. No existing declaration states this theorem. Existing tensor-power,
  twist-pullback, monoidal and coefficient-realization helpers were reused as above.

No STATEMENT-DISPUTED issue remains. The return concerned the old Lean rendering,
not the mathematical statement in the node or current blueprint.

## Second reading by NQ

This is the dispatcher's requested self-check, not a claim that another agent read
this packet; the maintainer supplies the independent review. I reopened the node,
the current source display, the recorded gamma and standing mate definitions, and
the replacement file together. The old statement was false for exactly the return's
identity/zero counterexample; the new signature has no gammaG, gammaF, gammaGF,
sourceIdentification or c parameter. All three purity arrows and the final mate now
occur by their recorded definitions. I checked each of the five arrows and its
source/target against the correspondence above, including the realization unit at
Y that accounts for inverse-realization after realization. I checked hK is retained
on the original intrinsic pro-etale K, and that gamma_f's domain is a theorem's
conclusion, not an extra assumption. I checked the removed compactification,
composite-smoothness, Tate-twist and invertible-exponent binders. The source
identification is built independently of gamma and c, so the equality is neither
tautological nor a universal claim about arbitrary maps. I checked that the node's
natural statement and blueprint_update were not edited and that lean.statement is
copied from the delivered signature. This replaces the former placeholder reading
with the specific H3/H4/H5/H11 checks requested in the return.

Final repair self-check: I checked the explicit intermediate objects 0 through 8
against the eight normalization clauses and the endpoint of gamma_gf. In particular
stages 3--5 undo Tate pullback first and tensor pullback second, and stages 6--8
restore the shifted presentation and the inverse-realization unit at Y. Every factor
is fixed to an existing canonical map; the existence-and-uniqueness statement fixes
the full composite, not just its endpoints. The two former data-valued `sorry`
helpers are gone. The node was refreshed from the current shared base with only
its lean record replaced; no extra stmt_deps, statement, or proof changes remain.
The final signature in lean.statement was extracted verbatim from the module.
