## Worker report

This delivery states `AlgebraicGeometry.radical_normalization_projective_etale` in
`Sheaf.AlgebraicGeometry.Curve.RadicalNormalizationProjectiveEtale`. Its only proof is `sorry`.
The node changes only in `lean`; there are no new notions, dependency repairs, or statement
corrections. The full eight-step natural-language proof is in the declaration docstring.

Hypotheses and clauses, checked against the node:

| Node text | Lean rendering |
| --- | --- |
| K is a field | `(K : Type u) [Field K]` |
| C is a smooth projective integral K-curve | `(C : Scheme.{u}) (q : C ⟶ Spec (.of K)) [IsSmoothProjectiveCurve q]`; this class extends `IsIntegralCurve`, `Smooth`, `IsProjective`, and the integral-curve class supplies integrality and dimension exactly one |
| F = K(C) | `C.functionField`, the canonical generic stalk with its existing field instance |
| U is an arbitrary open subscheme | `(U : C.Opens)`; no nonemptiness or affineness assumed |
| n >= 1 and invertible in K | `(n : ℕ) (hn : 1 ≤ n) (hnK : IsUnit (n : K))` |
| finite list of nonzero rational functions | `(r : ℕ) (a : Fin r → C.functionFieldˣ)` |
| each a_j and its inverse regular on U | `hreg` requires both values to belong to `Set.range (algebraMap (C.presheaf.stalk x) C.functionField)` for every `x ∈ U`; stalk algebra is the canonical specialization map to the generic stalk |
| algebraic closure of F and chosen roots | `(Ω : Type u) [Field Ω] [Algebra C.functionField Ω] [IsAlgClosure C.functionField Ω]`, with `α : Fin r → Ω` and `hα : ∀ j, α j ^ n = algebraMap C.functionField Ω (a j)` |
| L is exactly F(α_1,...,α_r) | `(L : IntermediateField C.functionField Ω)` and `hL : L = IntermediateField.adjoin C.functionField (Set.range α)` |
| L/F is finite | `[FiniteDimensional C.functionField L]` |
| Y and ν are the specified normalization | `C.normalizationIn L`, `C.fromNormalizationIn L`; no arbitrary substitute scheme or morphism |
| normal, meaning every local ring is an integrally closed domain | first conjunct is `∀ y : C.normalizationIn L, IsDomain (...stalk y) ∧ IsIntegrallyClosed (...stalk y)` |
| Y is an integral K-curve | `IsIntegralCurve (C.fromNormalizationIn L ≫ q)` supplies integrality, separatedness, finite type, and dimension exactly one |
| Y is projective over K | `IsHProjective (C.fromNormalizationIn L ≫ q)`, exactly the finite projective-space embedding convention of def-kun-projective |
| ν is finite and surjective | `IsFinite (C.fromNormalizationIn L) ∧ Surjective (C.fromNormalizationIn L)` |
| inverse image of U maps etale to U | `Etale (C.fromNormalizationIn L ∣_ U)`, the canonical morphism restriction |
| the canonical generic morphism identifies K(Y) with the specified L/F, compatibly over C | `∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField, e.hom ≫ (C.normalizationIn L).fromSpecFunctionField = (C.fromSpecOfAlgebraFunctionField L).toNormalization`; affine Spec equivalence gives the field identification, and composition with ν is the original `Spec.map (algebraMap F L) ≫ C.fromSpecFunctionField` by the defining normalization factorization |
| no geometric integrality or roots of unity | neither is a binder; no Galois, perfectness, or algebraically closed ground-field assumption |

The explicit structure map q is required by the recorded `IsSmoothProjectiveCurve` interface
and specifies the K-structure on Y as ν followed by q. No separate K-algebra structure on F
is postulated. One ambient universe is the existing normalization interface: any given field,
curve and algebraic closure fit after raising their common ambient universe. There is no
universe equality hypothesis or quantification over small test objects.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `IsSmoothProjectiveCurve`, `IsIntegralCurve`, `IsVariety`
  (def-pc-smooth-projective-curve, def-pc-curve).
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` (def-pc-integral-scheme).
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the integral clause of
  def-sc-function-field explicitly reuses `Scheme.functionField` from Mathlib; its general
  `Scheme.functionFieldOfComponents` is not the integral carrier used here.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap` (def-pc-field-extension).
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` / `.Basic`:
  `AlgebraicClosure`, `IsAlgClosure` (def-weil-algebraic-closure); the statement quantifies
  over a specified closure Ω, so it uses the latter.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalizationIn`,
  `Scheme.fromNormalizationIn`, `Scheme.fromSpecOfAlgebraFunctionField`
  (def-fin-normalization-extension), with `Scheme.Hom.toNormalization` from Mathlib.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`
  (def-weil-finite-integral-morphism); its integral companion `IsIntegralHom` was also read.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`
  (def-weil-surjective-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (def-weil-etale-morphism).
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`
  (def-kun-projective), public through SmoothProjective.
- `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`: `IntermediateField.adjoin`,
  used to specify the roots' generated subfield without a new definition.

Recorded proof dependencies are imported privately, including regular-normal decomposition,
affine-cover dimension, finite-over-projective, the unit-binomial lemma and the finite-etale
normal generic-component theorem. Mathlib proof dependencies are imported at their recorded
modules (normality under localization, integral-closure fraction fields, lying over and
finite-dimensional domains); proof modules already public through statement dependencies
are not redundantly imported. No import of the downstream tame-normalization theorem is made.

Edge cases checked before writing:

- `r = 0`: `Fin 0` is empty, hreg and hα are vacuous, and adjoin of the empty range is the
  bottom intermediate field, canonically F. No `Nonempty (Fin r)` or positive-r condition.
- `n = 1`: permitted by hn; the root equation places every chosen root in F and L = F.
- `U = ⊥`: hreg is vacuous pointwise, and restriction is the empty-to-empty morphism, etale.
  In contrast, directly using `C.germToFunctionField U` would demand `Nonempty U`; this was
  rejected before drafting. Pointwise stalk regularity is equivalent to regular sections
  on any open, by gluing their agreeing germs, including the empty open.
- Characteristic zero and positive characteristic are both allowed; only `IsUnit (n : K)`
  excludes the characteristic divisors as in the node. No primitive root is needed for
  the unit-binomial construction or for selecting its chosen generic field component.
- Non-geometrically-integral C, nontrivial constant fields, and imperfect K are allowed.
- C empty or zero-dimensional is excluded by the given integral curve assumption itself.

Source reading: the local Stacks sources, etale-cohomology.tex lines 2842--2885 (03PL),
pione.tex lines 2430--2463 (0BQL), morphisms.tex lines 3272--3290 (035B) and 14221--14265
(0AVK), agree with the root-algebra, normal-component, and finite-normalization proof plan.
No statement fault or `STATEMENT-DISPUTED` issue was found.

Searches for an existing statement (prescribed msearch.py; raw records in searches.jsonl):

- LeanFinder: “Normalization of a smooth projective integral curve in an extension generated
  by nth roots is finite surjective projective and etale where the radicands are units”.
  Eight hits: general normalization constructions/instances and standard-etale algebras;
  none states this theorem.
- Loogle: `AlgebraicGeometry.Scheme.normalizationIn, AlgebraicGeometry.Etale`.
  Zero hits; unknown upstream identifier normalizationIn in the Mathlib-only index.
- msearch grep: `normalization.*[Ee]tale|[Rr]adical.*[Nn]orm`, AlgebraicGeometry.
  Zero hits.
- LeanSearch: “Normalization of a smooth projective curve in a radical field extension is
  finite surjective projective and etale on the unit locus”. Eight generic normalization
  construction/instance hits; no radical-unit-locus theorem.
- rg in live `WeilConjectures/` and `Sheaf/`: root/normalization, stalk-regularity,
  `IsSmoothProjectiveCurve`, `IsIntegralCurve`, `germToFunctionField`; read the existing
  TameRadicalNormalization module, which assumes geometric integrality, roots of unity
  and an etale branch marking and thus does not state this more general theorem.
- Exact node id grep in `lean/WeilConjectures`, and exact proposed declaration/id search in
  `WeilConjectures`, `Sheaf`, `dag/lean_names_upstream.json`: no existing declaration.

Validation: scompile.py compiled this file separately as sandbox and library module on the
server in 9.1 and 9.2 seconds, with no errors or warnings. All variables and universe u are
explicit, autoImplicit is disabled, the sole theorem body is sorry, and there are no probes.

## Second reading by Q02

A second pass by this worker (the dispatcher explicitly forbids starting other agents;
independent maintainer review remains pending) reread the node and the full Lean signature.
K, the integral smooth projective C, the open U, positive invertible n, finite nonzero list,
pointwise regular function/inverse, specified algebraic closure and chosen roots, generated
intermediate field L, and finiteness are all present exactly as listed above. All seven
conclusion blocks match: stalkwise normality, integral curve, finite projective-space
embedding, finite map, surjective map, etale restriction, and the specified generic field
identification. The generic equation fixes the identification over C, rather than giving
only an abstract field isomorphism. The restricted map has target U itself. The uses of
IsHProjective and IsIntegralCurve retain dimension exactly one and the source's projective
convention. No missing clause, added root-of-unity/geometric-integrality hypothesis, or
incorrect edge-case restriction was found; no statement changes were needed.
