## Worker report

Item: det-thm-sf-pf-adic-open. Group: N8. Stage 2, 2026-10-18.

The delivery states `AlgebraicGeometry.ProEtale.IntegralOpenDirectImage.integral_open_direct_image`
in `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage`, with `sorry` as its entire proof.
Its only auxiliary declaration is `reductionPullbackMap`, whose body is an actual mates
construction from the published exact scalar-restriction square. No data or helper proof is
postponed. The mathematical node statement and proof are unchanged. The already landed
`sk-def-sfb-coefficient-change` is added to `stmt_deps` because the canonical comparison now
uses its recorded coefficient map and compatibility square explicitly.

Source read: main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic/
sk-thm-sf-pf-adic-open.md and sk-thm-sf-pf-adic-open.proof.md. The module docstring identifies
that source and Stacks Tags 099L, 09A6, 09C1; the theorem docstring carries all eleven proof
steps of the current DAG, including its scalar-restriction and residue-linearity arguments.
The resolved stage-1 maintenance note was read; its instruction to preserve the existing
proof route and statement is respected.

Hypothesis-by-hypothesis rendering:

- The prime ell is `(l : ℕ) [Fact l.Prime]` in the section, generalized into both declarations.
- The field k of positive characteristic p different from ell is `(k : Type u) [Field k]`
  with `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]`. A field has prime positive
  characteristic exactly when its ring characteristic is prime; p is not independent data.
- U and X are `Scheme.{u}`. Their structure maps are given by
  `[U.Over (Spec (.of k))]` and `[X.Over (Spec (.of k))]`.
- Finite type over k is rendered separately for each scheme by `LocallyOfFiniteType` and
  `QuasiCompact` on its structure map. Separatedness is `IsSeparated` on each structure map.
- The map j is `(j : U ⟶ X)` with `[j.IsOver (Spec (.of k))]`.
- Its open immersion and quasi-compactness are `[IsOpenImmersion j] [QuasiCompact j]`.
- The finite extension E/Q_l is `(E : Type u) [Field E] [Algebra (Padic l) E]`
  and `[FiniteDimensional (Padic l) E]`. The integer ring and chosen uniformizer are
  those of the recorded `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`; no independent coefficient ring is introduced.
- The ambient K is `DerivedCategory (AdicCompletion.Modules l E U)`.
  `AdicCompletion.Modules` is definitionally internal modules over
  `condensedRingObj (DerivedNakayama.integerRing l E) U`, the pulled-back continuous
  condensed integer ring. In particular this is not the discrete constant O_E ring.
- The bounded constructible hypothesis is
  `hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) U K`.
  This is the recorded condensed-coefficient constructibility convention in
  `sk-def-sfb-constructible` / `det-def-sfb-constructible-tor-amplitude`: canonical
  t-structure boundedness and finite constant scalar local models of every cohomology
  module, with finite constructible stratifications on qcqs schemes.

Clause-by-clause rendering:

- Rj_* is the recorded `CondensedRing.moduleObjectDerivedPushforward`, the total right
  derived functor of the full internal-module pushforward composite, rather than the
  derived pushforward of abelian sheaves followed by a new action.
- The first conjunct is `IsDerivedComplete l E X (Rj_* K)`. Its recorded definition uses
  the actual tensor-unit augmentation of the reduction Roos complex on a K-flat model.
  Thus it asserts invertibility of the canonical completion map, not just existence of
  some isomorphism with a limit. `ProEtaleIntegralCoefficientLimit` supplies the recorded
  continuous-integral / inverse-limit coefficient comparison and is publicly imported.
- Residue reduction is `AdicCompletion.derivedReduction l E T 0` for T = U,X. The index
  0 denotes positive level 1, so its coefficient ring is `DerivedNakayama.quotientRing l E 1`,
  O_E/pi_E. Its quotient morphism is exactly inverse image of
  `DerivedNakayama.reductionRing l E 1`. It is derived extension of scalars, hence the
  relative derived tensor in the displayed formula, retaining the F_E action.
- The second conjunct asserts a unique invertible comparison c with source reduction
  of integral Rj_*K and target residue Rj_* of reduction K. Both sides live in the
  residue-coefficient derived category, not merely after forgetting the residue action.
- Its equation specifies the canonical comparison. Write L_A, R_A and L_B, R_B for
  geometric pullback and pushforward with integral and residue coefficients, and T_U,
  T_X for derived reduction. The helper θ = `reductionPullbackMap` is
  `L_A ⋙ T_U ⟶ T_X ⋙ L_B`. The equation is
  `θ_(R_A K) ≫ L_B(c) ≫ ε_B = T_U(ε_A)`.
  On K-flat representatives θ is the usual balanced tensor association, an isomorphism;
  adjunction therefore determines c uniquely. This is the usual coefficient-change
  (projection-formula) comparison. The existential is a characterization of that
  canonical arrow, not a free choice of an arbitrary isomorphism.
- The helper θ is the inverse mate, along the two derived scalar-extension/restriction
  adjunctions, of the inverse of `CondensedRing.derivedComapUpperStarIso`. This latter
  square is exact and available for arbitrary coefficient morphisms. The published
  `derivedPushHom` cannot be used here: its enclosing section imposes flatness, whereas
  O_E -> F_E is not flat. No such hypothesis has been added to the delivery.
- The next conjunct is `constantModelBoundedConstructible ... X (Rj_*K)`.
- The last conjunct is the equality of the bounded constructible object predicate
  with its intersection with `DerivedCategory.finiteTorAmplitude`. Their full
  subcategories are precisely `ConstantModelBoundedConstructible` and
  `ConstantModelConstructibleFiniteTor`. This renders the explicit category equality
  `Dbc(X,O_E) = Dctf(X,O_E)` and, together with the preceding conjunct, gives the
  finite Tor amplitude of the image. No claim about all unbounded complexes is made.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  Its docstring and `CondensedRing.compactificationOverField` signature spell out the
  separated finite-type over-field binders. The chosen compactification is irrelevant
  to this open direct-image statement, which uses the same setting explicitly.
- `def-weil-l-adic-coefficient-extension`: module
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, theorem
  `Padic.finite_coefficientExtensionRing`, and its public `CoefficientExtension` module
  for integers, uniformizer, ideals, finite rings and quotient maps.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and the quasi-compactness class exported by it.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `ProEtale.coefficientRing`, `condensedRingObj`, `isCommMonObj_condensedRingObj`.
- `det-prop-sfb-qlbar-colimit-x-integral-limit`:
  `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`,
  `ProEtale.sfb_integral_coefficient_limit` and its continuous coefficient constructions.
- `sk-def-sfb-module-derived-pushpull`:
  `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `CondensedRing.moduleObjectDerivedPushforward`, publicly retaining the geometric
  derived adjunction and its exact-pullback comparison.
- `sk-def-sfb-derived-tensor-hom`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`, retaining
  `CondensedRing.derivedTensor` / `derivedHom` and the relative K-flat derived monoidal
  structure. The derived scalar-extension realization is the existing completion API.
- `sk-def-sfb-bounded-constructible`:
  `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`, which publicly
  retains `ProEtale.boundedConstructible`, `BoundedConstructible` and their ordinary
  unbounded derived-category presentation. Its extra discrete-coefficient predicate is
  not substituted for integral continuous coefficients. The more specific condensed
  finite-constant-model convention below is the one the item uses.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `ProEtale.constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`,
  with `IsConstantModelConstructible` and its local-model definitions.
- `det-def-sfb-constructible-tor-amplitude`: `Sheaf.Paper.ConstantModelTorAmplitude`,
  `constantModelConstructibleFiniteTor_wellDefined`, publicly retaining the preceding
  definitions and `DerivedCategory.finiteTorAmplitude`.
- `sk-def-pe-derived-completion`: `Sheaf.SixFunctors.ProEtale.DerivedCompletion`,
  `IsDerivedComplete`, `AdicCompletion.Modules`, `quotient`, `derivedReduction`.
- Added already landed statement dependency `sk-def-sfb-coefficient-change`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`,
  `coefficientMap`, `CondensedRing.derivedComapUpperStarIso` and the coefficient squares.

All recorded statement dependency modules are public imports. Every recorded proof
module is also imported, privately when it is only a proof dependency. The one proof
dependency without a Lean record is `sk-lem-integral-models`; it is retained in the DAG
and proof docstring, not restated or silently dropped. The theorem proof remains `sorry`.
The source for `ConstructibleSheaf.ProEtaleModule.DerivedCategory` was read through
`scompile.py --source`, as it is missing from the older source checkout. Framework
sources were read from the exact shared overlay, as required by the human update.

Edge cases checked before writing:

- Empty U and empty X are not excluded; no `Nonempty` or dimension hypothesis is added.
  The zero complex satisfies completeness, reduction and bounded constructibility.
- For the identity open immersion the two adjunction counits and coefficient square
  specialize to the identity comparisons; reduction and completeness have their usual
  meanings. No properness of j is assumed.
- Torsion integral K is admitted. Reduction is derived, so its extra Tor cohomology is
  retained; ordinary tensor reduction would be wrong in this case.
- Level 0 of the positive-level completion API is residue exponent 1. The exponent-zero
  zero ring is not mistakenly used.
- Arbitrary ramification and finite E/Q_l are allowed, including E = Q_l. The chosen
  uniformizer, not the rational integer l, is used by the coefficient quotient.
- The characteristic assumptions exclude characteristic zero and characteristic l,
  exactly as the fixed setting requires, and impose no algebraic closure or perfection.
- No flatness of the residue quotient is assumed. Exact restriction, rather than an
  invalid flat coefficient-change specialization, supplies the canonical square.
- Site objects retain universe u+1 and morphisms universe u; internal sheaves are
  `Ab.{u+1}`. No identification of these universes or finite-field base datum is imposed.

Searches for an existing statement:

- msearch.py leanfinder: "Derived pushforward along a quasi compact open immersion
  preserves bounded constructible adic integral complexes and commutes with reduction
  modulo uniformizer". Eight hits concern ordinary O_X-module pushforward, its
  adjunctions and compositions, and sheaf pushforward composition; none states this claim.
- msearch.py loogle: `AlgebraicGeometry.IsOpenImmersion, "derived"`: zero hits.
- msearch.py grep: `DerivedComplete|boundedConstructible.*[Ll]owerStar|[Oo]pen.*[Aa]dic`:
  25 hits, chiefly unrelated p-adic/topological "open" occurrences; no exact statement.
- msearch.py leansearch: "The derived direct image of bounded constructible integral
  ell-adic complexes under an open immersion is derived complete and commutes with
  reduction": eight hits on ordinary open-immersion module adjunctions, stalk restriction
  and the open-immersion definition; no match.
- rg of the old upstream WeilConjectures tree for the node id: no hits. rg of upstream
  SixFunctors and shared lean/Sheaf for open constructible / adic-open statements finds
  finite-coefficient open direct-image finiteness and unrelated adic extension-by-zero,
  not this completed-integral theorem. Those finite results remain proof imports.
- rg for `reductionPullbackMap|integral_open_direct_image` in upstream WeilConjectures,
  shared lean/Sheaf and dag/lean_names_upstream.json: no existing declaration.
- Read the entire published ChangeOfCoefficients implementation, including its flat
  section boundary; read DerivedCompletion and DerivedNakayamaResolution to verify
  the continuous coefficient objects and exponent indexing. No duplicate notion is added.

No STATEMENT-DISPUTED issue and no mathematical statement correction was found.

## Second reading by N8

This is a separate self-check of the node and completed module, not a claim that another
agent read the file: the dispatcher explicitly prohibited starting other agents and
provides the maintainer's independent review after delivery.

Checked each field/prime, extension, over-field, finite-type, separatedness, open,
quasi-compactness and K-constructibility hypothesis against the node. Checked all four
output clauses, including the global Dbc/Dctf equality and the canonical-arrow
normalization. Checked the mate direction: the scalar adjunction inverse mate takes
`Res_X ⋙ L_A -> L_B ⋙ Res_U` to `L_A ⋙ T_U -> T_X ⋙ L_B`. Thus the displayed equation has
source `T_U L_A R_A K` and target `T_U K`, and uniquely specifies the usual arrow
`T_X R_A K -> R_B T_U K` using the geometric adjunction. The exact geometric pullback
adjunctions are transported from their recorded total-derived versions by the recorded
leftDerivedUpperStarIsoMapDerivedCategory; no separate choice of adjunction is made.

The extra finite-Tor condition is expressed by equality of object predicates, avoiding
an ill-typed equality of two differently bundled full-subcategory types. No new
hypothesis, special-case coefficient category, arbitrary comparison map or hidden data
choice was introduced. The definitions contain no `sorry`. The one theorem has only
`sorry`; its proof docstring follows the current eleven-step route.

## Validation

Compilation and delivery preflight results are recorded below after the wrapper checks.

The first complete wrapper compile stopped before reaching this module in an imported
`Sheaf.Paper.CoefficientRingedSequenceSite`, with unresolved universe constraints. Its
import path was traced through the proof-only CartesianCoefficients/Tate-twist chain.
A diagnostic compile temporarily omitted only `import Sheaf.Paper.CartesianCoefficients`;
the actual delivered module then passed both sandbox (5.6 seconds) and library-artifact
(6.8 seconds) checks, with no errors or warnings. The import was restored immediately.
A fresh `scompile.py --source Sheaf.Paper.CoefficientRingedSequenceSite` showed that the
published source had meanwhile gained the coefficient-universe sheafification repair;
no shared or launcher file was edited by this worker. Final compilation and preflight
below use the complete restored imports, not the diagnostic omission.

The complete restored module passed `scompile.py N8 det-thm-sf-pf-adic-open ...`
with exit code 0. The wrapper's current-server confirmation successfully rebuilt or
reused the entire required import closure, including the repaired sequence site,
CartesianCoefficients and its Tate-twist dependencies. The delivered library module
compiled in 6.5 seconds, nice 19, two threads, hard 60-second limit, with no warnings
or errors. Declaration enumeration finds precisely the recorded helper definition and
main theorem. The JSON signature is an exact copy of the saved theorem text, all Lean
lines are at most 99 characters, and there is exactly one theorem proof `sorry`.

`deliver2.py N8 det-thm-sf-pf-adic-open --no-push` passed with exit code 0:
`OK (dry run): commit 633ffb3aba passes the preflight and compiles; nothing pushed`.
It compiled the restored complete module in both sandbox and library-artifact modes
and staged exactly the report, item node record and one Lean module.
