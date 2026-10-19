## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalCurveTestDatum` states
`AlgebraicGeometry.Etale.exists_curveTestDatum_of_int`. Its only theorem has the whole proof
`sorry`. It defines no new notion. The node is unchanged except for its `lean` record.

The current blueprint main-20261015 unit was read directly. Its statement agrees verbatim
with the node. The already published upstream `Etale.exists_curveTestDatum` supplies the
same geometry with a natural annihilator. An `existing: true` record for that declaration
would silently restrict the source's signed integer n. The new statement retains n : Z,
uses the existing datum, and states divisibility in Z. It also uses the recorded chosen
Cartesian-square interface. This is a signature adaptation of the existing construction,
with no arbitrary canonical map or new choice-based definition.

Hypotheses and clauses, in order:

- The schemes and morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- X affine is `[IsAffine X]`; f affine is `[IsAffineHom f]`.
- Smooth of relative dimension one is `[SmoothOfRelativeDimension 1 f]`. Mathlib supplies
  smoothness from this class; there is no separate extra hypothesis.
- The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`, matching the established small
  etale module-sheaf size convention for schemes in universe u.
- The signed integer is `(n : ℤ)`; invertibility on S is
  `(hn : IsUnit (n : Γ(S, ⊤)))`.
- n Lambda = 0 is `(hΛ : (n : Λ) = 0)`: for a unital ring, annihilation of the whole module
  Lambda is equivalent to annihilation of 1.
- The integer degree and lower bound are `(q : ℤ) (hq : 1 ≤ q)`.
- Every lower degree universally is
  `∀ q' : ℤ, q' ≤ q - 1 → Etale.UniversalBaseChangeProperty Λ f q'`.
  The full integer range, including negative degrees, is retained.
- Failure at the fixed base in degree q is `¬ Etale.BaseChangeProperty Λ f q`;
  it is not silently replaced by failure of the universal property.
- The existing datum is the existential `D : Etale.CurveTestDatum.{u}`.
- S' is `D.S₀` and the morphism S' to S is the existential `a : D.S₀ ⟶ S`.
- X' is `D.X₀`, f' is `D.f₀`, and its projection to X is `b : D.X₀ ⟶ X`.
  The existential `ChosenCartesianSquare b D.f₀ f a` supplies the chosen identification
  X' isomorphic to X times_S S', and the two projection equations. Thus X' need not be
  definitionally Mathlib's selected pullback object; it has exactly the specified square.
- Affineness, integrality and normality of S' are the existing datum fields
  `D.isAffine_base`, `D.isIntegral_base`, and `D.isIntegrallyClosed_stalk`.
  On an integral scheme the stalks are domains, so their integral closedness is precisely
  normality. If A = Gamma(S', top), the canonical `S'.isoSpec` identifies S' with Spec A;
  the affine fraction-field theorem identifies `D.S₀.functionField` with Frac A.
- L is `D.S₀.functionField`, with algebraic closedness `D.isAlgClosed_functionField`.
- K is `D.K`, with `D.field`, `D.isAlgClosed`, and the field embedding `D.i` from L.
  A unital ring homomorphism between fields is injective, so this is the stated extension.
- The geometric generic point g is
  `Spec.map D.i ≫ D.S₀.fromSpecStalk (genericPoint D.S₀)`.
- The fibre is `D.Y₀` with `D.e` and `D.h`; `D.isPullback` supplies exactly its Cartesian
  square with g and D.f₀. In particular, h targets X', not the geometric point.
- Affineness and smooth relative dimension one of f' are `D.isAffineHom` and
  `D.smoothOfRelativeDimension_one`; affineness of X' follows from its affine base.
- The integer d is `(D.d : ℤ)`. It is invertible on S' by `D.isUnit_d` and divides the
  original signed n by `(D.d : ℤ) ∣ n`.
- Nonvanishing is
  `¬ IsZero (Etale.higherDirectImage Λ D.h q (Etale.constantModSheaf Λ D.Y₀ D.d))`.
  `constantModSheaf` is literally the sheafification of the constant presheaf valued in
  `Λ ⧸ Ideal.span {(D.d : Λ)}`; `higherDirectImage` is degree-q homology of the bounded
  below derived direct image of this sheaf in degree zero.

The natural-number witness in the existing datum is read as an integer, with no loss of
existential cases. Given any signed d, |d| generates the same ideal (d) = (-d), has the
same invertibility and divisibility properties, and hence the same quotient coefficient
sheaf. Conversely a natural witness is an integer witness. No positivity assumption on n
or extra nonzero hypothesis is imposed. To prove the statement from the upstream theorem,
apply it to n.natAbs, use q' <= q-1 iff q' < q, and choose the canonical pullback
identification from the resulting IsPullback square.

Dependency declarations used (full source signatures and docstrings read):

- `sk-def-bc`: `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`,
  `AlgebraicGeometry.Etale.BaseChangeProperty`, `UniversalBaseChangeProperty`,
  `baseChangeHomologyMap`, `constantModSheaf`, `higherDirectImage`.
- `sk-def-smooth` and `def-sbc-smooth-morphisms`: Mathlib's
  `AlgebraicGeometry.SmoothOfRelativeDimension` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`. The compound sk-def-smooth node's separate
  allowed-torsion filtered-colimit theorem is not needed for this statement; its recorded
  `Sheaf.AlgebraicGeometry.AllowedTorsion.allowedTorsion_colimit_map_isIso` was read, and
  the actual class is used from the explicit smooth-morphism dependency, not copied.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`, used inside the existing datum.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, used in the existing datum.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, used on the integral scheme's stalks in the existing datum.
- `def-sc-function-field`: `Sheaf.AlgebraicGeometry.FunctionField` records both the
  component-product construction and the integral-scheme specialization, which reuses
  Mathlib's `AlgebraicGeometry.Scheme.functionField`. The latter, not the product over a
  general reducible curve, is used by the datum. Its field instance and affine fraction
  field theorem in `Mathlib.AlgebraicGeometry.FunctionField` were read.
- `def-weil-algebraic-closure`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`;
  `AlgebraicClosure` supplies the proof's field extension.
- `def-weil-pbc-cartesian-square`: `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`, used explicitly in the conclusion.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, reused by `Etale.constantModSheaf`.
- `def-weil-pbc-quotient-module`: `Mathlib.LinearAlgebra.Quotient.Defs` and `.Basic`,
  `Submodule.hasQuotient`, `Submodule.Quotient.module`, `Submodule.mkQ`,
  `Submodule.mkQ_surjective`, `Submodule.ker_mkQ`, reused by the constant quotient.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, and the derived pushforward in the existing
  higherDirectImage definition.
- The published `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum`
  supplies `Etale.CurveTestDatum` and `Etale.exists_curveTestDatum`. The current source
  was also confirmed with `scompile.py --source`, not just the older checkout.

The available proof-dependency modules are imported without public export. The one
unrecorded proof dependency `lem-sbc-module-bc-integral-surjective` is the argument already
present as the upstream theorem
`Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective` in IntegralBaseChange,
which is imported by CurveTestDatum. No extra statement notion is missing; no new node or
dependency module is required for this stage-2 statement. The docstring records the
node's complete seven-step proof, retaining its arbitrary-Lambda coefficient reasoning.

Edge cases checked: q=1 includes degree zero in hprev; negative degrees remain quantified.
Negative n is retained and passed to the upstream construction via its absolute value.
n=0 is not excluded by a new hypothesis (on an empty base it can be a unit); any failure
would give a map from a nonempty field spectrum, where its pullback cannot be a unit.
For the zero coefficient ring all sheaves are zero, so the failure hypothesis is false.
The empty X, or empty S, likewise admits no such cohomological failure. d=0 cannot be a
unit on the datum's integral nonempty base, and d=1 has zero quotient, contradicting the
nonzero conclusion. No hidden positivity or nonemptiness assumption was added.
Universes are explicitly u for schemes/fields and u+1 for coefficient rings/module values,
following the recorded BC interface. There are no auto-bound variables or local notation.

Searches made with msearch.py (Q92/sk-lem-universal-datum):

- leanfinder, "Universal curve test datum for failure of etale cohomology base change with
  a signed integer annihilator": 8 hits, about etale/formally etale/smooth properties;
  no matching theorem.
- leansearch, the same query: 8 hits, geometric stability/etale properties only.
- loogle, "AlgebraicGeometry.Etale.exists_curveTestDatum": 0 hits, unknown identifier in
  Mathlib. This does not deny the upstream declaration; it is not a Mathlib declaration.
- grep, "exists_curveTestDatum|CurveTestDatum", Mathlib/AlgebraicGeometry: 0 hits.
- rg in upstream WeilConjectures for `CurveTestDatum|exists_curveTestDatum`: the existing
  datum and natural-n theorem in CurveTestDatum.lean, plus callers in Induction/Vanishing.
- rg in upstream for `sk-lem-universal-datum`: its existing theorem docstring.
- rg in lean/Sheaf for `curveTestDatum|CurveTestDatum|universal.*[Cc]urve.*[Dd]atum`:
  only the older UniversalBaseChangeFailureDatum import, no signed-n wrapper.
- rg across dag/nodes for CurveTestDatum: the item, its citers, the normalization and
  prime-coefficient nodes; no independent missing definition of this existing notion.
- rg in both source roots for `exists_curveTestDatum_of_int|exists_curveTestDatum_int`:
  no prior declaration with the new name.

No STATEMENT-DISPUTED flag or source-based statement correction is needed.

Validation: scompile.py compiled this delivery's single file separately as both sandbox
and library module, cleanly, with no warnings, using the prescribed 60-second limit.
The prescribed deliver2.py --no-push dry run is the final gate; its result is recorded below.

## Handoff audit

The route note's Q114 stage-1 sandbox no longer exists. The repository's Q114 report has
an independent second reading and the ledger records its reviewed merge at 02:33, followed
by live-completion superseding syncs. Thus the route note's assertion that no reading or
merge exists is stale. The current item has no lean record and is a genuine stage-2 task.
The suggested old deliver.py dry run was invoked; it waited for worktree capacity before
it could check the absent sandbox, and was stopped to avoid an obsolete stage-1 packet.
The current delivery keeps the reviewed DAG split unchanged, rather than reconstructing
or replacing it. Only the new stage-2 lean record and statement module are supplied.

## Second reading by Q92

I independently read the node, the blueprint source, Stacks etale-cohomology.tex
16848–17339, the delivery module, and the upstream CurveTestDatum and Defs modules.

Object/hypothesis/conclusion list and matching Lean, with verdicts:

- Schemes X and S and f : X → S: `{X S : Scheme.{u}} (f : X ⟶ S)`. Exact.
- X affine; f affine and smooth of relative dimension one: `[IsAffine X]`,
  `[IsAffineHom f]`, `[SmoothOfRelativeDimension 1 f]`. Exact; no extra finiteness,
  Noetherian, separation, or characteristic hypothesis.
- Arbitrary commutative coefficient ring: `Λ : Type (u + 1)` and `[CommRing Λ]`.
  Exact under the recorded small-etale module coefficient size convention.
- Signed integer n, invertible on S, annihilating Λ: `n : ℤ`,
  `hn : IsUnit (n : Γ(S, ⊤))`, `hΛ : (n : Λ) = 0`. Exact. Annihilation of 1
  is equivalent to annihilation of the unital ring.
- Integer q ≥ 1: `q : ℤ`, `hq : 1 ≤ q`. Exact.
- Every lower integer degree universally: `hprev : ∀ q' : ℤ, q' ≤ q - 1 →
  Etale.UniversalBaseChangeProperty Λ f q'`. Exact; integer inequalities match q' < q.
- Failure for the fixed f at q: `hfail : ¬ Etale.BaseChangeProperty Λ f q`.
  Exact; this is not replaced by universal failure.
- Output S' and its map to S: `D.S₀` and `a : D.S₀ ⟶ S`, for the existential
  `D : Etale.CurveTestDatum.{u}`. Exact.
- S' affine, integral, normal: datum fields `isAffine_base`, `isIntegral_base`,
  `isIntegrallyClosed_stalk`. Exact: integral schemes have domain stalks, and their
  integral closedness is normality. The canonical `S'.isoSpec` identifies this affine
  scheme with Spec of its section ring.
- Algebraically closed fraction field L: `D.S₀.functionField` and
  `D.isAlgClosed_functionField`. Exact by the integral affine fraction-field theorem.
- Algebraically closed extension K/L and geometric generic map: `D.K`, `D.field`,
  `D.isAlgClosed`, `D.i`, and `Spec.map D.i ≫ D.S₀.fromSpecStalk (genericPoint D.S₀)`.
  Exact. The unital field homomorphism D.i is injective.
- X' and base-changed f': `D.X₀`, `D.f₀`, `b : D.X₀ ⟶ X`, and the existential
  `ChosenCartesianSquare b D.f₀ f a`. Exact: its pullback isomorphism respects both
  projections. Datum fields also retain affineness and smooth relative dimension one.
- Y and the Cartesian fibre over Spec K: `D.Y₀`, `D.e`, `D.h`, `D.isPullback`.
  Exact; h has target X' and e has target Spec K, in the required orientation.
- Integer d dividing n and invertible on S': `(D.d : ℤ) ∣ n` and `D.isUnit_d`.
  Exact existential rendering. A signed divisor may be replaced by its absolute value:
  the principal ideal, quotient, divisibility and invertibility are unchanged.
- Nonzero R^q h_*(Λ/dΛ): `¬ IsZero (Etale.higherDirectImage Λ D.h q
  (Etale.constantModSheaf Λ D.Y₀ D.d))`. Exact: Defs.lean defines the constant module
  as Λ modulo the ideal generated by d, and higherDirectImage as degree-q homology of
  derived pushforward applied to that sheaf in degree zero.

I opened the signatures behind the dependency records: BC and universal BC in upstream
Defs; SmoothOfRelativeDimension in Mathlib; IsAffineHom; Spec; IsIntegral;
IsIntegrallyClosed; the integral Scheme.functionField specialization (not the reducible
curve component product); IsAlgClosed; ChosenCartesianSquare; constantSheaf; the module
quotient; and lowerStar. The bundled datum uses exactly these notions. The compound
sk-def-smooth's torsion-colimit declaration is not mistaken for the smoothness predicate:
that predicate is supplied by the explicit def-sbc-smooth-morphisms dependency.

Source hypotheses: the blueprint statement agrees verbatim with the node. Stacks 0F08
and its preceding Remark 0F02 use a signed integer and all lower degrees universally;
the blueprint explicitly supplies the arbitrary-Lambda and affine smooth curve variant.
No hidden Noetherian or field-base assumption occurs. The full seven-step node proof is
represented in the theorem docstring, including normalization, arbitrary-coefficient
comparison, injectivity, prime detection and inherited geometry.

Edge cases: q=1 includes degree zero, and all negative lower degrees remain quantified.
Negative n is allowed; n=0 is not removed by a positivity premise. Empty S or X and the
zero coefficient ring cannot satisfy the failure premise. The integral base excludes an
empty output, as required by the existence of its fraction field. d=0 cannot be a unit
on it, while d=1 has a zero quotient and cannot give the nonvanishing conclusion. All
characteristics compatible with invertibility remain covered. The explicit universe u
and coefficient universe u+1 follow the recorded BC interface; no auto-bound variable
or local notation is present.

Independent searches: rg for CurveTestDatum, exists_curveTestDatum, generic-point and
normalization terms in upstream WeilConjectures found the already read natural-n theorem
and its datum. Searches in Mathlib and lean/Sheaf found no signed-n wrapper. The older
UniversalBaseChangeFailureDatum module states the separate Z/n cumulative-BC node and
cannot replace this arbitrary-Lambda statement. Semantic and type searches are recorded
below with independent queries. The upstream theorem requires n : Nat, so recording it
as an exact existing declaration would not retain the signed input; the wrapper is
appropriate and adds no second definition.

No new node or dependency module is in this delivery, and no statement_change is present
or needed. I found no mathematical mismatch and preserved the correct Lean and node.
The sole change is this missing independent second-reading audit. The prescribed
scompile.py compiled the sandbox and library module cleanly, with no warning or error.

Independent query results (2026-10-17, msearch.py):

- LeanFinder: "Nonvanishing of a constant quotient sheaf higher direct image on the
  geometric generic fibre detects failure of base change" returned eight unrelated
  affine-limit/lifting results, with no cohomological datum theorem.
- Loogle: "IsUnit, Int, AlgebraicGeometry.Scheme" returned Scheme.ord_of_isUnit and
  Scheme.ordHom_of_isUnit, neither of which concerns base-change failure.
- rg of geometricGeneric/normalization/CurveTestDatum and the theorem name in the upstream,
  project and Mathlib algebraic-geometry trees confirmed the Mathlib normalization
  construction and the existing natural-n upstream datum; none is a signed-n theorem
  matching this signature.
- LeanSearch: "A normal integral affine scheme with algebraically closed rational
  function field and a nonzero higher direct image of constant coefficients" returned
  eight affine/normalization/proper-morphism results, none stating this cohomological
  theorem. Thus all three search kinds were independently repeated.
