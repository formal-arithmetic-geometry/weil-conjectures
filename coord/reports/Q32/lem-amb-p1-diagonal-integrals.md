## Worker report

Item: `lem-amb-p1-diagonal-integrals`, group Q32, stage 2, 2026-10-16.

The module `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` states
`AlgebraicGeometry.Etale.projectiveLine_diagonal_integrals`. Its only theorem has
proof `sorry`. Four helper definitions spell out the two projections, their
canonical projective-line charts, the transported traces, and the canonical source
identifications. Every helper has real data and belongs to this node; none states
another DAG theorem. The node changes only in `lean`.

Hypothesis and clause correspondence:

* The integer N at least one is `(N : ℕ) (hN : 0 < N)`. The finite commutative
  coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`, and NA = 0 is
  `(hA : (N : A) = 0)`. In a unital ring, annihilating one by N is equivalent to
  annihilating every element. No field, nonzero-ring, or flatness hypothesis is added.
* The base is `(S : Scheme.{u}) [IsNoetherian S]`, with invertibility of N rendered
  by `(hS : IsUnit (N : Γ(S, ⊤)))`. A global integer is a unit exactly when it is
  invertible on the scheme. Every subsequent invertibility witness is obtained by
  applying the actual structural ring map to hS.
* P is the recorded `AlgebraicGeometry.ProjectiveLine S`, definitionally
  `ProjectiveSpace (ULift.{u} (Fin 2)) S`. This has exactly two homogeneous
  coordinates, in the scheme universe u. W is the recorded Mathlib
  `pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)`.
* Delta is `pullback.diagonal (ProjectiveLine S ↘ S)`. Its closed-immersion
  structure follows from separatedness of the proper structural projection.
  `projectiveLineDiagonalProjection S false` is `pullback.fst`, and the value at
  `true` is `pullback.snd`. Thus `∀ a : Bool` asserts exactly the two requested
  identities.
* All derived objects and functors use the dependency's ordinary small-etale
  `DerivedCategoryModule A T`. `ordinaryFiniteConstant A T` is the constant module
  sheaf, `ordinaryFiniteUnit A T` its degree-zero derived image, and
  `ordinaryFiniteLine A N hA T` the degree-zero image of
  `Scheme.finiteEtaleTateLine T N A hA`. That is the recorded roots-of-unity
  scalar-extension twist, with powers as residue-class action, not an adic twist.
  `⟦(2 : ℤ)⟧` is the requested cohomological shift.
* The declaration exhibits `hI : Delta.ker.IsInvertible` and an Ext class κ
  satisfying the dependency's `SupportedKummerBoundary A N hA Delta hI hW κ`.
  This is the supported Kummer class, rather than an unconstrained arrow. The
  uniqueness clause of `ordinary_supported_kummer` proves that the predicate
  determines κ uniquely. Exhibiting this characterized class is an explicit
  rendering of "let delta be the supported Kummer morphism"; there is no extra
  hypothesis on the theorem and no arbitrary choice of a morphism.
* The actual delta in the integral is
  `supportedExactDerivedMap (lowerStar (ModuleCat A) Delta) A_P A_W(1) κ`.
  This is precisely the derived arrow specified by `ordinary_supported_kummer`.
  Its source is `RDelta_* A_P`. The implementation is the canonical exact
  degree-zero direct-image comparison followed by the Ext realization κ.hom.
  Consequently it also implements the node's explanatory last clause identifying
  `RDelta_* A_P` with `Delta_* A_P` for the exact closed direct image.
* `projectiveLineDiagonalAlpha A S a` is `supportedDerivedUnit A p_a` followed
  by `Rp_a.map (supportedDerivedUnit A Delta)`. The composite-adjunction unit
  formula, after constant pullback comparisons, identifies it with the canonical
  map from the identity composite to `Rp_a_* RDelta_*`, since
  `Delta ≫ p_a = 𝟙 P`. This is the canonical alpha in the direction of the
  displayed integral. It is not a parameter that a caller may choose.
* `projectiveLineDiagonalChart S a` uses
  `ProjectiveSpace.isPullback_map (ULift (Fin 2)) (P ↘ S)`, flipped for the
  first projection. `IsPullback.isoPullback` gives an actual scheme isomorphism
  e from `ProjectiveLine P` to W with the equation `e.hom ≫ p_a = (P1_P ↘ P)`.
  Thus there is no unidentified model of the fibre product.
* `projectiveLineDiagonalTrace` transports the dependency's
  `projectiveLineTrace N hN A hA P hP` along that chart. The transport is, in
  order, `Rp_a` of the canonical adjunction unit for e, the canonical
  `rightDerivedLowerStarComp`, the congruence for the chart's structural-map
  equation, and `Rq` of `ordinaryFiniteShiftedLinePullback`. The latter uses
  exactly `projectiveLineTraceTransport N hN A hA`, fixed on roots and pure
  tensors. Since e is an isomorphism, these are the canonical identifications
  with the standard projective-line projection, and hence give exactly t_{p_a}.
  The helper constructs the Noetherian structure on P from finite type and
  compactness; this is not an added hypothesis.
* Finally the conclusion is the specified alpha, then the specified derived
  pushforward of delta, then the specified trace, equal to
  `𝟙 (ordinaryFiniteUnit A P)`. A single κ is used for both projections.

Recorded statement dependencies, read with their signatures and docstrings:

* `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace`, its structural `over`, `ProjectiveLine`,
  and the canonical base-change square `ProjectiveSpace.isPullback_map`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and
  `pullback.diagonal`. The associated universal-property isomorphism is used
  from Mathlib's `IsPullback` API.
* `Sheaf.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, implemented by the upstream
  ordinary constant-module-sheaf derived category.
* `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`:
  `AlgebraicGeometry.Etale.projectiveLineTrace` and
  `projectiveLineTraceTransport`, with the normalized datum and trace equation
  read to check their interpretation.
* `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`:
  `AlgebraicGeometry.Etale.ordinary_supported_kummer`; its existing
  `SupportedKummerBoundary`, `supportedExactDerivedMap`, and
  `supportedDerivedUnit` are reused, not copied.
* `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`. This supplies the
  general composition theorem in the proof plan. The helper maps use its existing
  constant-coefficient specialization `Etale.rightDerivedLowerStarComp` from
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`, whose full
  definition as the conjugate of exact inverse-image composition was read.
  No site-universe restriction from the general ringed-topos interface is imposed.

Every stated proof-dependency module is imported, with proof-only imports nonpublic.
For Mathlib leaves whose `mathlib_match` contains several files, the relevant
files are imported individually. The theorem docstring carries all seven DAG
proof steps, including the nonreduced chart calculation, both coordinate choices,
the exchange mate's unit normalization, and detection of equality only for the
degree-zero sheaf endomorphism. No dependency interfaces are changed.

Edge cases checked before writing:

* N = 1 forces A to be the zero ring. All coefficient objects and maps then give
  the unique identity in the zero category; no `Nontrivial A` is imposed.
* The zero ring is allowed for every positive N, as is the empty base scheme.
* S need not be connected, reduced, regular, or affine. The Cartier chart
  equations in the proof work over rings with nilpotents.
* Both projection indices are present; the same supported class is used in both.
  The canonical charts exchange moving and base coordinates in the specified order.
* The fibre divisor at infinity has the same O(1) transition convention as a
  finite point, so no sign or rational-point case is excluded.
* No independent coefficient or site universe is forced to equal u. Coefficients
  have the recorded u+1 size and all schemes have universe u, as the dependencies
  require. All variables and universes are explicitly bound.

Searches made:

* `msearch.py`, LeanFinder, "integrating the supported Kummer class of the
  diagonal on the projective line along either projection gives identity": eight
  irrelevant hits about Weierstrass variable changes, projective evaluations and
  `Proj.one_apply`; no match.
* `msearch.py`, LeanFinder, "projective line diagonal Kummer class integrates
  to one": eight unrelated Weierstrass/Proj/Eisenstein hits; no match.
* `msearch.py`, Loogle, `"diagonal", "trace"`: three matrix trace lemmas;
  their signatures are about matrix traces, not etale sheaves, so no match.
* `msearch.py`, LeanSearch, "projective line diagonal supported Kummer class
  trace identity": eight hits on algebraic field traces and matrix trace;
  no supported etale or projective-line identity.
* `msearch.py`, grep, `diagonal.*(trace|integral)|trace.*diagonal|projectiveLineTrace`:
  twelve Mathlib hits, all about linear algebra/matrix traces; no match.
* `rg` of that concept in the upstream `WeilConjectures` source and `lean/Sheaf`
  found the recorded trace and supported-map modules and downstream references,
  not a declaration of these identities. The corresponding argument in the
  ordinary P1-adjunction docstring is not a theorem statement. The upstream
  `grep -rn lem-amb-p1-diagonal-integrals` found no declaration.
* `rg` of all five proposed declaration names in Mathlib, upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.

No disputed statement, new nodes, dependency modules, or statement correction.

Validation: the prescribed `scompile.py Q32 lem-amb-p1-diagonal-integrals` run
completed with exit 0, no errors and no warnings. Its sandbox compile took 32.1 s
and its final-module compile took 32.8 s, each within the default 60 s limit.
The node's recorded signature was extracted verbatim from the final file; a field
comparison confirms that only `lean` changes. The required `deliver2.py --no-push`
dry run is the final check before the READY response. This worker does not supply
an independent second-reading section or push the delivery.

## Second reading by Q32

Independent reading on 2026-10-16. I opened the item's DAG record, blueprint
source `sec-smooth-purity/sk-prop-sf-cbc/lem-amb-p1-diagonal-integrals.md`,
enclosing unit, delivered module, and all six statement-dependency records
and declaration sources. The item's source is a blueprint lemma, not a Stacks
lemma. For the Kummer/support ingredients I also read Stacks
`etale-cohomology.tex`, labels `lemma-kummer-sequence` (03PL) and
`lemma-cohomology-with-support-triangle` (0A45), with the surrounding roots
definition and exact closed direct image discussion. Neither adds regularity
or reducedness. The explicit ordinary finite coefficients and Noetherian base
in the DAG are retained.

My object/hypothesis/conclusion checklist and verdicts:

1. Integer N at least one: `(N : ℕ) (hN : 0 < N)`. Exact; the node has no
   N = 0 case.
2. Finite commutative A with NA = 0: `(A : Type (u + 1)) [CommRing A]
   [Finite A] (hA : (N : A) = 0)`. Exact. Killing one is equivalent to
   killing every element; no nontriviality or flatness is assumed.
3. Noetherian scheme S with N invertible: `(S : Scheme.{u})
   [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))`. Exact; being a unit
   globally is equivalent to local invertibility of this global section.
4. P: `ProjectiveLine S`. I read upstream `ProjectiveSpace` and
   `ProjectiveLine`; the latter is `ProjectiveSpace (ULift.{u} (Fin 2)) S`.
   Exact two-homogeneous-coordinate projective line, not dimension two.
5. W: `pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)`, using
   Mathlib's recorded fibre product. `projectiveLineDiagonalProjection S a`
   is `fst` for false and `snd` for true. Exact two projections.
6. Delta: `pullback.diagonal (ProjectiveLine S ↘ S)`. Its closed immersion
   instance comes from separatedness. `∃ hI : ...ker.IsInvertible` supplies
   the effective Cartier ideal required by the Kummer dependency. This is a
   conclusion, not an extra hypothesis restricting S; the node's chart proof
   establishes it over every base ring. Exact diagonal and Cartier structure.
7. Categories and constants: I unfolded `DerivedCategoryModule`,
   `ordinaryFiniteConstant`, and `ordinaryFiniteUnit`. They are the derived
   category of `Sheaf T.smallEtaleTopology (ModuleCat A)`, the constant
   sheaf A, and its degree-zero single object. Exact ordinary encoding.
8. Twist and shift: I read `finiteEtaleMuModuleObj`, its restriction maps,
   `finiteEtaleTwistScalar`, `finiteEtaleTateLine`, and `ordinaryFiniteLine`.
   Roots have the ZMod exponent action; the line is their sheafified scalar
   extension. `ordinaryFiniteLine ...⟦(2 : ℤ)⟧` is the requested shifted
   degree-zero twist. Exact; tensor order is canonically symmetric.
9. Specified supported Kummer delta: `∃ κ : Ext ... 2,
   SupportedKummerBoundary ... κ ∧ ...`, realized in the integral by
   `supportedExactDerivedMap ... κ`. I read the boundary's divisor section,
   specified complement frame and extension equation, the exact derived
   realization, and `ordinary_supported_kummer` in full. Its uniqueness
   clause determines this normalized κ. Thus the existential formulation
   says the result for the prescribed canonical class, with no arbitrary
   supported arrow chosen to make the equality hold. The same κ precedes
   `∀ a`, as required. Exact.
10. Exact closed-image identification, the node's last paragraph:
    `supportedExactDerivedMap F X Y κ` is
    `(F.singleFunctorCompRightDerivedFunctorIso.app X).hom ≫ κ.hom`.
    Its source is RDelta_* of the constant, canonically identified with the
    degree-zero exact direct image before κ. Exact; no arbitrary comparison.
11. Alpha: `projectiveLineDiagonalAlpha` composes `supportedDerivedUnit A p_a`
    with `Rp_a.map (supportedDerivedUnit A Delta)`. I read the unit's actual
    definition, including its constant pullback comparison, and upstream
    derived adjunction and `rightDerivedLowerStarComp`. By the composite
    unit formula this is the canonical derived-composition identification
    in the displayed direction; it is invertible since p_a Delta = id.
    Exact fixed map, not a free parameter.
12. Traces: `projectiveLineDiagonalChart` uses
    `ProjectiveSpace.isPullback_map`, flipped for false. I checked its
    structural-map equation and the order of all maps in
    `projectiveLineDiagonalTrace`: isomorphism unit, derived composition,
    congruence for that equation, normalized shifted-line pullback, then
    `projectiveLineTrace` over P. I read `projectiveLineTraceTransport`,
    its roots and pure-tensor normalization, `projectiveLineTraceDatum`,
    and the trace as inverse decomposition followed by second projection.
    Exact canonical transported trace, with no primitive-root or sign choice.
    P's Noetherian structure is constructed from finite type and compactness
    inside the definition, not added as a hypothesis.
13. Both identities: `∀ a : Bool, projectiveLineDiagonalAlpha ... ≫
    (ordinaryFinitePushforward A ...).map (supportedExactDerivedMap ... κ) ≫
    projectiveLineDiagonalTrace ... a = 𝟙 (ordinaryFiniteUnit A P)`.
    Exact alpha, pushforward of delta, then trace, equal to identity for both
    projections and one common supported class.

Edge cases: empty S and the zero coefficient ring are allowed. N = 1 forces
A to be zero and has no `Nontrivial` obstruction. No connectedness, field,
reducedness, regularity, or characteristic restriction beyond invertibility
of N is added. The chart equations work over rings with nilpotents. Bool
has exactly the two required indices. Schemes have universe u and coefficients
the dependency's u+1 size; no equality of independent site universes is imposed.
Every variable and universe is explicitly bound.

Independent searches, using different queries from the first writer:

* LeanFinder via `msearch.py`: "etale cohomology diagonal cycle class
  pushforward projective space equals one". Eight unrelated hits, including
  `Proj.one_apply`, `Rep.diagonal_succ_projective` and Proj pullback lemmas;
  none states the integration identity.
* Loogle via `msearch.py`: `"Kummer"`. Eight field/Kummer-Dedekind results;
  none concerns supported etale classes or projective-line traces.
* LeanSearch via `msearch.py`: "pushforward cycle class of a section of the
  projective line is identity on constant etale sheaf". Eight sheaf
  pushforward construction/section lemmas, no integration identity.
* `rg` in Mathlib, upstream WeilConjectures and this project's `lean/Sheaf`
  for `diagonal.*(integrat|kummer|chern)`, `integrat.*diagonal` and
  `supported.*diagonal`: hits concern kernel transforms, Fourier inversion,
  pro-etale pairings and proof commentary in OrdinaryFiniteP1Adjunction.
  None states this lemma; the latter commentary is not a declaration.
* Exact-name searches for all five delivered declarations in those three
  trees and `dag/lean_names_upstream.json` returned no collision. The four
  helpers reuse dependency maps, without redefining a trace, roots sheaf,
  supported boundary or derived functor.

No new nodes, dependency modules or statement correction are present. I read
the general ringed-topos composition declaration too; this module uses the
already available constant-coefficient specialization, not a new copy or an
extra size restriction from the general theorem. I verified that the sandbox
node differs only in `lean`, and `lean.statement` is verbatim the signature.
All four definitions have concrete data and no `sorry`; the sole theorem's
whole proof is `by sorry`. Its docstring follows all seven DAG proof steps,
including nonreduced charts, exchange-unit normalization and degree-zero
stalk detection. Source/blueprint docstrings and the 100-character limit hold.

Mismatches found: none. Changes: this independent reading/search audit only;
the Lean and node record remain as written. Fresh prescribed `scompile.py`
compilation completed with exit 0 and no warnings or errors: sandbox 29.7 s,
final module 36.6 s, each within 60 s. Delivery preflight follows below.

Delivery validation: `deliver2.py Q32 lem-amb-p1-diagonal-integrals --no-push`
printed OK: the delivery passes preflight and compiles. Only the module, its
node record, and this report were staged. No mathematical or interface repair
was needed.
