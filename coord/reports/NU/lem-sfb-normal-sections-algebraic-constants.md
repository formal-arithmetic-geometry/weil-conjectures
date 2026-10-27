## Worker report

The module `Sheaf.AlgebraicGeometry.NormalSectionsAlgebraicConstants` states
`AlgebraicGeometry.normal_sections_algebraic_constants`, with its whole proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypotheses and objects, matched to the node:

- The commutative integral domain is `(A : Type u) [CommRing A] [IsDomain A]`.
- The integral scheme is `(X : Scheme.{u}) [IsIntegral X]`. In particular it is nonempty,
  its global sections form a domain, and its local rings are domains by Mathlib's
  integral-scheme instances. The normality hypothesis `hX` asks precisely for
  `IsIntegrallyClosed (X.presheaf.stalk x)` at every point; the domain part is already
  supplied by integrality, rather than silently dropped.
- The named dominant map is `(h : X ⟶ Spec (CommRingCat.of A)) [IsDominant h]`.
- `F = Frac A` is represented by `(Spec (CommRingCat.of A)).functionField`.
  Mathlib's `functionField_isFractionRing_of_affine` makes this the fraction field
  of A for its canonical A-algebra. `E` is `X.functionField`, exactly the generic stalk.
  `R` is `Γ(X, ⊤)`.
- The A-action on R is explicitly the module of the algebra
  `((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ h.appTop).hom.toAlgebra`.
  Thus `hfin : @Module.Finite A Γ(X, ⊤) ...` is finite generation for the actual pullback,
  rather than for an arbitrary A-action. `ΓSpecIso.inv` sends A into the sections of Spec A.
- The field-algebra witness `e` is required to equal `h.dominantFunctionFieldAlgebra`.
  This existential merely names the existing canonical algebra for typeclass inference
  in the subsequent clauses. Its equality fixes all its data and is no extra hypothesis
  or free field embedding. The canonical algebra is the generic stalk pullback.
- The map R into E is `X.presheaf.germ ⊤ (genericPoint X) (by trivial)`.
  This is definitionally Mathlib's `X.germToFunctionField ⊤`, written directly to supply
  the top-open membership without an additional nonempty-open instance.

Every conclusion, matched to the node:

- `∃ L : IntermediateField F E` names the field inside E. Its defining equality
  `L.toSubfield = Subfield.closure (Set.range (generic germ))` says it is Frac R
  inside E: since the generic germ is injective and R is a domain, the smallest
  subfield containing its image consists exactly of its fractions. This is also
  Mathlib's `Subfield.ringHom_fieldRange_eq_of_comp_eq` characterization of the
  image of a fraction field. No assumption that all of E is Frac R is made.
- `L = algebraicClosure F E` gives exactly `L = {a in E | IsAlgebraic F a}` by
  `mem_algebraicClosure_iff`, using the recorded relative-algebraic-closure definition.
- `FiniteDimensional F L` states that L/F is finite, not merely algebraic or finitely
  generated as a field.
- `∀ a : X.functionField, IsAlgebraic L a → a ∈ L` is precisely algebraic closedness
  of L inside E, using the canonical subfield inclusion for the L-algebra on E.
- For every `IsAlgebraic F a`, `∃ d : A, d ≠ 0 ∧ ∃ r : Γ(X, ⊤), ...` states that the
  generic germ of r equals the generic germ of the pulled-back d times a. The
  denominator lies in A, not just R, and is explicitly nonzero. Injectivity and the
  field laws yield the node's parenthetical fraction `a = r/d`.
- Properness, Noetherianity, finite type, separatedness, separability and a condition
  on characteristic do not occur among the binders.

Dependencies used (declarations and their source/docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`; the integral
  stalk and sections domain instances supply domain properties implied by the node.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded function-field
  definition module, whose docstring explicitly directs arbitrary integral schemes
  to Mathlib's `Scheme.functionField`, not the component-product construction.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`,
  `Scheme.germToFunctionField`, `germ_injective_of_isIntegral`,
  `stalkFunctionFieldAlgebra`, and the affine/stalk `IsFractionRing` instances.
- `Sheaf.TraceFormula.LocalDimensionFormula`:
  `Scheme.Hom.dominantFunctionFieldAlgebra`, the exact declaration recorded by
  `def-sfb-dominant-function-field-map`. Its real body uses
  `Scheme.Hom.functionFieldMap` in
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, and the generic-point
  equality obtained from dominance.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`.
- `Mathlib.FieldTheory.AlgebraicClosure`: `algebraicClosure`, `mem_algebraicClosure_iff`.
- `Mathlib.RingTheory.Algebraic.Defs`: `IsAlgebraic` (transitively public).
- Proof import `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`:
  `Scheme.exists_germToFunctionField_eq` (the recorded gluing theorem).
- Proof import `Mathlib.RingTheory.Algebraic.Integral`: `IsAlgebraic.restrictScalars`
  and `instFiniteDimensionalFractionRingOfFinite`, the two recorded Mathlib leaves.
- Proof import `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`:
  `Algebra.IsIntegral.of_finite`, the recorded finite-algebra leaf.

Source checked: local `properties.tex`, lemma-normal-integral-sections (Tag 0358),
including its full proof by local integrality and gluing, and `fields.tex`,
lemma-finite-is-algebraic, lemma-algebraic-elements, lemma-algebraic-permanence
(Tags 09GG, 09GI, 09GJ). As the node itself says, this relative result is an adapted
consequence, rather than a verbatim Stacks statement. The docstring contains all six
steps of the DAG proof and names their dependencies.

Edge cases checked mathematically before writing:

- The empty scheme and zero ring are excluded by exactly integrality and `IsDomain A`,
  as in the node; no additional nonemptiness hypothesis is used.
- For a field A, F is canonically A and the denominator may be 1. A finite normal
  integral A-algebra gives the expected finite field case.
- For `h = 𝟙 (Spec A)` with A integrally closed, R = A and L = F; this is covered.
- A nonnormal base A is allowed: only the local rings of X are integrally closed.
- Nonproper and non-finite-type X are allowed whenever the explicitly given finite
  global-sections hypothesis holds. Finite module generation is not replaced by
  finite-type algebra generation.
- Purely inseparable elements and all characteristics are included.
- If a = 0 the denominator assertion allows d = 1 and r = 0; the algebraicity proof
  also handles degree-one equations. An annihilating nonzero polynomial over a
  field cannot be a nonzero constant, so normalization uses degree at least one.
- All variables and universe u are explicit; A and X use the common universe of the
  scheme morphism category, without a separate size restriction on test objects.

Searches made for an existing statement:

- `msearch.py ... leanfinder`: “For a normal integral scheme dominant over a domain A
  with global sections finite over A, the fraction field of its global sections is
  the relative algebraic closure of Frac A in its function field”, and “normal
  integral scheme global sections finite over domain relative algebraic closure”.
  Results included `finite_appTop_of_universallyClosed`, function-field instances,
  normalization and integral-closure finiteness results; none states this result.
- `msearch.py ... leansearch`: “An algebraic rational function on a normal integral
  scheme with finite global sections becomes a global section after multiplication
  by a nonzero base denominator”. Results were rational-function denominator lemmas
  and the stalk fraction-field instance, not this statement.
- `msearch.py ... loogle`: `"algebraicClosure", "IsFractionRing"`. The sole hit was
  `Ring.instIsFractionRingNormalClosureSubtypeAlgebraicClosureFractionRingMemIntermediateFieldNormalClosure`,
  a normal-closure construction, not the scheme statement.
- `msearch.py ... grep` in Mathlib/AlgebraicGeometry:
  `algebraicClosure|isFractionRing.*[Gg]lobal|[Gg]lobal.*isFractionRing` found only
  uses of AlgebraicClosure in group schemes, not this statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for relative algebraic closure,
  normal sections, algebraic sections, canonical function-field algebras, and
  `appTop.*toAlgebra` found the canonical maps reused here and
  `exists_normal_stein_constant_field`. The latter assumes properness and finite
  type and gives a Stein factorization; it is not this arbitrary-domain theorem.
- The item id has no declaration hit in `lean/WeilConjectures`; the proposed theorem
  name has no hit in Mathlib, either project root, or `dag/lean_names_upstream.json`.

No STATEMENT-DISPUTED flag or node fault remains. The first compile exposed elaboration
issues, repaired by explicitly naming the canonical algebra and writing the generic germ.
The next compile succeeded with only one long-line warning, which has been wrapped.
The final dry run recompiles the delivered source.

## Second reading by NU

This is a single-worker rereading, not a claimed independent review: the dispatcher's
brief forbids starting other agents and assigns independent review to the maintainer.
I reopened the node and final signature and checked each binder and conjunct as above.
The algebra witness is fixed by equality to the recorded canonical construction, the
intermediate field is fixed by its subfield equality to the fraction field of R, and
both the nonzero A-denominator and algebraic closedness clauses are present. The source
assumes no normality of A. Local domain hypotheses follow from integral X. There is no
new mathematical hypothesis, omitted conclusion or private duplicate definition.
