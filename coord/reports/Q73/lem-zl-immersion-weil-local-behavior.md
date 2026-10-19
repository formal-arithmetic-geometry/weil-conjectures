## Worker report

The module `Sheaf.Paper.ImmersionWeilLocalBehavior` states both numbered clauses of
`lem-zl-immersion-weil-local-behavior`. All postponed proofs are named theorems,
with the node/source and natural-language proof in their docstrings. Definitions
and instances have real data. The mathematical statement is unchanged.

The finite-field, coefficient, and geometric hypotheses are rendered as follows.

- `D : FiniteFieldDatum.{u}` supplies p, a, q, the finite field k₀ and its chosen
  algebraic closure k. The schemes are `X₀ W₀ : Over (Spec (.of D.k₀))`.
- Local finite type, quasi-compactness and separatedness of their structure
  morphisms express separated finite type. The two principal theorem signatures
  explicitly retain separatedness with `include hsepX hsepW`; the pullback theorem
  also explicitly retains `himm : IsImmersion h₀.left`.
- `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` give the prime and excluded
  characteristic. `immersionWeil_coefficient_unit` retains *both* the prime
  instance and hl explicitly, and supplies the unit proof needed by compact support.
- `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`, and
  `[IsAlgClosure (Padic l) Ω]` give the chosen algebraic coefficient closure.
  The coefficient universe v is independent of the scheme universe u. The finite
  stages use `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L`, the existing
  small model of the actual finite subfield, rather than imposing u = v.
- `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left`
  and the same expression for j₀ are Mathlib’s actual base-change maps. `IsImmersion` is Mathlib's closed-then-open notion; the
  separate open clause assumes `[IsOpenImmersion j₀.left]`. The two universal
  theorems allow independent source schemes (W₀ denotes W in one and U in the other).

Clause-by-clause rendering:

| Node clause | Lean rendering |
| --- | --- |
| Pullback is the specified derived pullback with its induced Weil structure | `ImmersionWeilRationalPullback.comparison`, its `frobenius_formula`, and `IsoAlgebra.mapOfNatIso`; the formula is inverse composition, the actual Frobenius commutation equality, then composition. `ImmersionWeilCommonStagePullback.stage_comparison` fixes the same structure after stage inclusion by requiring the identity underlying arrow. |
| Pullback is t-exact | `comparison.underlying.tExact` on the actual `sfRationalStandardTStructure` / `sfCommonStageStandardTStructure`. |
| Exact functor on constructible Weil sheaves | `ImmersionWeilExactComparison.heart`, `heart_fac`, `heart_limits`, `heart_colimits` on the full heart-carrier fixed-pair subcategories defining the recorded Weil sheaves. |
| Natural Weil Hᵃ comparison for every integer a | `ImmersionWeilExactComparison.cohomology`; `cohomology_underlying` fixes its underlying arrow to the canonical normalized comparison. The source/target Weil Hᵃ functors are `IsoAlgebra.mapOfNatIso` of the Frobenius pullback's canonical cohomology comparison. The displayed isomorphism has the inverse orientation of the node, equivalently the same natural isomorphism. |
| Closed z maps to closed x with the same residue field | `immersionWeil_closed_point`: `h₀.left z ∈ closedPoints X₀.left` and `IsIso (h₀.left.residueFieldMap z)`. This is invertibility of the canonical residue map, so in particular preserves the k₀-structure, degree and cardinality. |
| Canonical pullback stalk formula | `ImmersionWeilRationalPullback.stalk` and `stalk_formula`. The latter fixes the map to degree-zero `coefficientFdCohomology` of point fibre of inverse `localPullbackComposition`, exactly the sheaf stalk. |
| That identification intertwines local geometric Frobenius | `stalk_frobenius`, using the actual `localClosedFrobeniusCohomology` at degree zero on W and `localFrobeniusCohomology` at the compatible composite geometric point on X. The exponent is the closed-point residue degree minus one, exactly the positive-power indexing of the recorded local-operator definition. The equality is directly on the H⁰ stalk modules. The closed-point theorem identifies it with the target's local degree. |
| Rj! is the recorded compact-support functor | `immersionWeilOpenRationalFunctor` specializes `sfCompactSupportFiniteFunctor` to `Compactification.ofIsOpenImmersion`; `ImmersionWeilOpenAction` specializes the published normalized coefficient action. `immersionWeilOpenCommonStageFunctor` is defined to be exactly `S.system.functor`, including normalized actions on all morphisms and scalar comparisons. The two functor wrappers have explicit types and are irreducible so Lean does not expand the strict-tower implementation while checking the statement. |
| Rj! is t-exact and j! is exact with constructible values | `ImmersionWeilRationalOpenExtension.comparison` and `ImmersionWeilCommonStageOpenExtension.comparison`, with the same generic exactness fields. Codomains are the recorded constructible categories/hearts. |
| Induced Weil structure for Rj! | `frobenius_unit` fixes the base-change Frobenius comparison to the open adjunction mate; `unit_weil` and `unit_underlying` retain the actual open unit as a Weil isomorphism. The common-stage `stage_comparison` fixes the included finite-stage structure, with the identity underlying arrow. |
| Natural Weil Hᵃ(Rj!L) ≅ j!Hᵃ(L) | The same `cohomology` / `cohomology_underlying` fields, now for the specified compact-support functor. |
| Original stalk inside the open | Open `stalk` and `stalk_formula`; the inverse map is the actual open unit followed by point fibre of inverse pullback composition. |
| Frobenius and residue size agree on the open | Open `stalk_frobenius` uses the same local operators and common residue degree; `immersionWeil_closed_point` applies to the open immersion and identifies the residue fields. Every compatible residue embedding is quantified. |
| Zero stalk outside the open | `zero_stalk` quantifies every closed x outside `Set.range j₀.left` and every compatible residue embedding. It asserts `IsZero` of degree-zero coefficient cohomology of the actual point complex of the extended Weil sheaf. |
| All the stalk assertions are for Qbar coefficients, not only objects descending at an assumed fixed field | Both common-stage packages quantify **every** finite coefficient stage, have identity-underlying `stage_comparison`, and include `complex_descent` and `sheaf_descent` for every common-stage object. These are presentations of the assertions using the node's common-stage conventions: represent the Weil isomorphism, its inverse, and inverse equations after a common enlargement. Apply the displayed finite-stage stalk maps and local-operator identities and the canonical coefficient extension of the point fibre. No Frobenius-stable integral lattice is assumed. Canonical composition, open-unit, and coefficient-action normalizations fix the resulting maps; the formulas are not merely trace equalities. |

Dependencies read and used:

- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilSheaf`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilSheaf`, the two Frobenius pullbacks,
  `sfWeilPrimeInvertible`, the forgetful functors, and `sfWeilStageObject`.
- `Sheaf.Paper.SfConstructibleHeart`: the rational/common-stage heart properties and
  standard t-structures. These use the current intrinsic coefficient categories.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPullbackComposition`, `localPointComplex`,
  `localClosedPoint`, `localClosedPointDegree`, `localClosedFrobeniusCohomology`,
  `localFrobeniusCohomology`. Their full signatures and defining docstrings were read.
- Mathlib `OpenImmersion`, `Morphisms.ClosedImmersion`, `Morphisms.Immersion`:
  `IsOpenImmersion`, `IsClosedImmersion`, `IsImmersion` and its closed/open
  factorization. Mathlib `ResidueField`: `Scheme.Hom.residueFieldMap`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStageDerivedPullback`, and their literal-stage specifications.
- `Sheaf.Paper.IntegralRationalQbarCompactSupport`: the recorded integral,
  rational and literal common-stage compact-support values. The normalized
  coefficient-action module retains these exact values and fixes all maps too.
- Added already-landed statement dependencies (no new nodes):
  `lem-a1-constructible-pullback-t-exact`, whose
  `ConstructiblePullbackComparison` is reused instead of copied;
  `def-weil-compact-support-coefficient-action`, whose
  `SfCompactSupportCoefficientAction` and `sfCompactSupportFiniteFunctor` supply
  the actual compact-support maps. Both were checked for a dependency path back to
  this item; neither has one. The geometric morphisms use Mathlib’s `Over.pullback`
  functor directly, with no new definition of a fibre map and no import of the much
  larger supported-localization theorem just for its convenience wrapper.
- The module directly imports every recorded statement-dependency module, and
  imports the recorded modules of the stated proof dependencies. Unstated proof
  prerequisites (point-transport naturality, integral open reduction, open tensor
  normalization, completed/integral pullback comparison) are named in the proof
  docstrings but are not fabricated as imports or assumed as extra hypotheses.

Edge cases checked: empty source/target and empty open; the identity open; closed
immersions and their open-then-closed local factorization; zero sheaf; negative,
zero and positive cohomology degrees; closed-point degree one (positive-power
index zero means exponent one); all finite coefficient fields and enlargement of
Weil arrows without an invariant lattice; all compatible residue embeddings;
independent scheme and algebraic coefficient closure universes. No nonempty-scheme,
nonzero-object, positive cohomology-degree, or extra prime-invertibility hypothesis
is introduced. Frobenius equalities are stated directly on the requested H⁰ sheaf stalk modules
using the recorded coefficient cohomology functor.

Searches before writing:

- `msearch.py leanfinder`: “Pullback and extension by zero of constructible Weil
  complexes are t-exact and commute with local geometric Frobenius on stalks”.
  Eight hits concern O_X-module pullback/free modules and pseudofunctoriality;
  none is this common-stage Weil statement.
- `msearch.py loogle`: `IsImmersion, IsOpenImmersion, Functor.IsTExact,
  stalkPullbackIso`. No hits; service reported unknown unqualified `IsImmersion`.
  Its actual Mathlib declaration and factorization were then read directly.
- `msearch.py grep`: `Weil.*[tT]Exact|[tT]Exact.*Weil|extensionByZero.*stalk|stalk.*extensionByZero`:
  zero hits.
- `rg` on the read-only upstream and project sources for immersion/Weil,
  common-stage pullback/cohomology, and local Frobenius found the existing
  fixed-pair, t-exact pullback, local-operator and compact-support action modules
  reused here, not the combined assertion. The exact item-id upstream search
  returned no declaration. The broad immersion search also found unrelated
  scheme-module and étale extension-by-zero lemmas, not a coefficient-compatible
  Qbar-Weil statement. Queries/results are also retained in sandbox searches.jsonl.

No new nodes, dependency repairs, statement correction or statement dispute.
`scompile.py Q73 lem-zl-immersion-weil-local-behavior` compiled the final module
cleanly on the server: sandbox 29.4 seconds, library module 35.7 seconds, exit 0,
no warnings. Profiling identified unnecessary automatically generated SizeOf and
constructor-injectivity declarations for these large witness structures. Their
generation is disabled, following existing comparison-interface modules; the
mathematical fields, recursors, kernel checking, and 60-second limit are unchanged.
The profiling option was removed before this clean compile.

`deliver2.py Q73 lem-zl-immersion-weil-local-behavior --no-push` passed the
server per-file compile and maintainer preflight (dry-run commit b504e2c204).

## Author check

Author's final re-reading; the independent mathematical review is the maintainer's.
Compared the node, source Restriction/Part 2 paragraphs, the fixed-pair dependency,
and the entire module. Checked the table above against each numbered clause and
hypothesis. Found and repaired two interface issues: typeclass elaboration needed
the inherited finite-type/quasi-compact structures on the actual bundled base
changes; section variables unused syntactically would otherwise omit essential
finite-type/quasi-compactness/separatedness/immersion hypotheses (including the
closed-point and quasi-compact-open helper theorems), and the coefficient-unit helper needed explicit
retention of both the prime instance and excluded characteristic. The theorem
signatures now retain these with `include`. Checked that the open theorem has its
own open source universally quantified and does not inherit the unrelated h₀.
Checked direction and normalization of composition, the Frobenius unit square,
Weil cohomology, the two stalk maps, and the complement's degree-zero zero-stalk
clause. Common-stage fields explicitly include finite-stage and heart descent;
there is no hypothesis requiring a stable integral Frobenius lattice. Every new
helper belongs to the same node and carries its blueprint/source docstring.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
