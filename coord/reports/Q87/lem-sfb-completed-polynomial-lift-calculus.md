## Worker report

The module Sheaf.RingTheory.CompletedPolynomialLiftCalculus states
Algebra.completedPolynomial_lift_calculus, with one postponed proof and no definitions.
The accepted stage-1 split is preserved. The current queue assigns this item to stage 2,
and the live node has no Lean record or released repair note. The predecessor's rejection
concerned reopening its stage-1 split, rather than recording the stage-2 statement.

For readability in this report only, write P = Localization.AtPrime q,
p = IsLocalRing.maximalIdeal P, S = AdicCompletion p P, and F = Fin r → S.
The delivered signature writes all these Mathlib types explicitly and introduces no aliases.

Hypotheses and clauses, in signature order:

- `k : Type u` and `[Field k]` give exactly the field, with no characteristic restriction.
  `r : ℕ` includes zero, and `q : Ideal (MvPolynomial (Fin r) k)` with `[q.IsMaximal]`
  gives the specified maximal ideal in the finite polynomial ring. The localization is
  Mathlib's concrete Localization.AtPrime q; p is its maximal ideal, equivalently qP.
  S is exactly Mathlib's compatible-sequence completion at p.
- The first existential `b : Module.Basis (Fin r) P (KaehlerDifferential k P)` and the
  first conjunct `b i = KaehlerDifferential.D k P (algebraMap ... (MvPolynomial.X i))`
  assert freeness on precisely the differentials of the polynomial variables.
- The existential `e : AdicCompletion p (KaehlerDifferential k P) ≃ₗ[S] F` is the
  S-linear identification of the completed differential module with the finite free module.
  Its normalization on `AdicCompletion.of p ... w`, coordinate i, is the image under
  `algebraMap P S` of `b.repr w i`. Thus this is the stated completion identification.
  The finite product F is canonically the finite direct sum in the node.
- `d : Derivation k S F` is additive, k-linear, zero on the base field, and Leibniz for
  the canonical S-action. The displayed ideal-power condition asserts continuity:
  for each n there is N such that d sends m_S^N into m_S^n F. Its following coordinate
  equality on `algebraMap P S a` asserts that it extends the original universal derivation
  through the identified completion. The next conjunct quantifies every other continuous
  derivation with that same extension equality and asserts `d' = d`.
- The universal-property conjunct binds B with CommRing, Algebra k B, IsLocalRing,
  IsNoetherianRing and IsAdicComplete (maximalIdeal B) B. An arbitrary k-algebra map f
  from S to B is represented by `[Algebra S B] [IsScalarTower k S B]`, with underlying
  map `algebraMap S B`. Every f gives this structure by f.toAlgebra; conversely the scalar
  tower says that its map respects k. Its IsLocalHom and ideal-power continuity hypotheses
  are written explicitly. This does not assume a coefficient field or a residue-field map.
- `M : Type w`, AddCommGroup, Module B M, and Module.Finite B M give every finitely
  generated B-module. Its topology is expressed through m_B^n • top in Submodule B M,
  so it is specifically the maximal-ideal topology, not f(m_S)-adic completeness.
- `Φ : ((B ⊗[S] F) →ₗ[B] M) →ₗ[B] (S → M)` is B-linear. Its specified formula
  `Φ t s = t (1 ⊗ₜ[S] d s)` is composition with the completed derivation after extension
  of scalars. The tensor is written B ⊗[S] F to use Mathlib's left-factor B-module
  instance; TensorProduct.comm identifies it canonically with the node's F ⊗[S] B.
  Function.Injective Φ gives uniqueness, and the next iff says its image is exactly
  the continuous k-derivations. The image predicate spells out zero, additivity, vanishing
  on k, the two f-twisted Leibniz terms, and the m_S/m_B ideal-power continuity condition.
  These clauses express the B-linear bijection onto precisely the derivations in the node;
  the ambient function space merely avoids a duplicate bundled derivation construction.
- The restriction conjunct quantifies each complete Noetherian local k-algebra E. Its
  first half states that restricting a continuous local map is local. Its second half
  says that every local k-map h : P →ₐ[k] E has exactly one k-map g : S →ₐ[k] E that
  is local, continuous, and restricts to h on every a : P. Together these state exactly
  the claimed restriction bijection.
- The last conjunct binds B and E independently, each complete Noetherian local over k,
  f : S →ₐ[k] B continuous and local, and π : E →ₐ[k] B local and surjective with
  `RingHom.ker π.toRingHom ^ 2 = ⊥`. Its existential g is local and continuous and
  satisfies `π.comp g = f`. This is exactly square-zero lifting.
- The residue fields remain unrestricted throughout, including inseparable extensions.
  All universes u, v, w and all variables are explicitly bound. No test-object universe
  is identified with the source universe.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field, through the polynomial and differential imports.
- Mathlib.Algebra.MvPolynomial.Basic: MvPolynomial, X, algHom_ext; also the aeval
  signature and docstring in Mathlib.Algebra.MvPolynomial.Eval were read.
- Mathlib.RingTheory.Localization.AtPrime.Basic: Localization.AtPrime, the recorded
  concrete localization. Its local-ring and maximal-ideal identifications were checked.
- Mathlib.RingTheory.AdicCompletion.Basic and Algebra: AdicCompletion,
  IsAdicComplete, AdicCompletion.of, and the completed module's S-module instance.
  LocalRing supplies the canonical local completion and maximal-ideal identification.
- Mathlib.RingTheory.Kaehler.Basic: KaehlerDifferential, KaehlerDifferential.D,
  and linearMapEquivDerivation; no private differential object was introduced.
- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing, via public dependencies.
- Mathlib.LinearAlgebra.TensorProduct.Defs and Tower: TensorProduct, tmul, its
  leftModule action, and canonical commutativity of tensor factors.

The node's stated proof dependency modules are imported privately: finite-type Noetherian
permanence; localization Noetherian permanence; completion and completion-tensor results;
polynomial Kähler basis; localized differentials; and
WeilConjectures.RingTheory.Derivation.CompletionAndLocalization, whose
Derivation.exists_completion_and_unique_localization signature and shifted-coordinate
construction were read. The eight proof steps are included in the theorem docstring.

Sources opened: literature/stacks-project/more-algebra.tex, labels
lemma-formally-smooth-completion (07ED), lemma-lift-continuous (07NJ), and
lemma-derivation-extends (07PE), including their proofs. The stage-1 polynomial calculation
uses no residue-field section, as these completion and lifting arguments require none.

Edge cases checked mathematically: r=0 makes P=S=k and F zero; the continuous k-derivations
are zero and the restriction/lifting assertions still hold. M=0 gives the unique zero map.
The identity surjection has zero square-zero kernel and admits the original f as lift.
For an imperfect field and q=(x^p-a), a not a pth power, the differential basis remains dx;
the formulas use no separability. Powers with n=0 give the whole target module or ring and
impose no extra condition. Finite products represent finite direct sums also when empty.

Searches actually run in this attempt:

- msearch.py leanfinder, query `Continuous derivations of completed local polynomial rings
  and extension of local homomorphisms to complete local algebras`: eight hits, including
  BDeRham, liftOfDerivationToSquareZero, derivationToSquareZeroEquivLift and ordinary formally
  smooth completion lifting. None states this completed-source differential and local-map
  calculus. The initial search process expired before its output could be recovered; the
  identical search was rerun and its successful results inspected.
- msearch.py loogle, query `"AdicCompletion", "Derivation"`: OK, zero hits.
- msearch.py grep, query `ContinuousDerivation|completedPolynomial|completed_polynomial`:
  OK, zero hits.
- Direct rg of lean/WeilConjectures and lean/Sheaf for completedPolynomial,
  completed_polynomial, CompletedPolynomial, completed-polynomial-lift,
  continuousDerivation and ContinuousDerivation: no matching declaration.
- Direct rg of dag/lean_names_upstream.json, lean/WeilConjectures and lean/Sheaf for the
  exact item id and proposed declaration: no existing declaration.
- Direct rg and source reads in Mathlib found the completion, its module action,
  the Kähler universal derivation, and the tensor leftModule instance used here.

No new nodes, dependency repairs, statement correction, or disputed statement is needed.
The inherited CompactObject example is currently withdrawn, so its file supplies no usable
header; this module follows the current module-mode instructions in brief-stage2 instead.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
