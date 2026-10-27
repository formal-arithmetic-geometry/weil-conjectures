## Worker report

The new module `Sheaf.TraceFormula.CurveDeltaCompletionData` states
`AlgebraicGeometry.Scheme.curve_delta_completion_data`, with one postponed theorem
and no definitions. The node's statement is unchanged. The only statement dependency
added is the already landed `def-trf-normalization-pushforward-stalk`, to reuse the
actual ring stalk with its canonical local-ring algebra, not a replacement ring.
The theorem of `NormalizationSingularSkyscraper` is not used: only its unconditional
stalk, quotient, ideal and completion abbreviations and algebra instance are used.

Source read: `literature/stacks-project/varieties.tex`,
`lemma-prepare-delta-invariant` (Tag 0C1R), all nine clauses and its proof;
`lemma-normalization-same-after-completion` (Tag 0C3V), statement and proof.
The node is an extracted helper, not a blueprint unit's statement. No source-based
correction, disputed statement, dependency repair, or new node was necessary.

Hypotheses and conclusions, in declaration order:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Reduced finite-type k-scheme: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`,
  `[IsReduced X]`, `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`. Finite type is exactly the conjunction
  in the dependency record, not just locally finite type.
- Pure dimension one: `hpure : X.IsPureDimension 1`, the recorded definition
  requiring dimension one of every irreducible component with its subspace topology.
- Closed point: `(x : X) (hx : IsClosed ({x} : Set X))`.
- Componentwise normalization: `X.reducedNormalization` and
  `X.fromReducedNormalization`, the recorded coproduct of normalizations of reduced
  irreducible components, followed by their closed inclusions.
- A is `X.presheaf.stalk x`. B is `normalizationPushforwardStalk X x`, definitionally
  the stalk of the direct-image structure presheaf. Its algebra instance comes from
  taking the stalk of `X.fromReducedNormalization.c`.
- M is `normalizationQuotientStalk X x`, the module quotient of B by the range of
  `Algebra.linearMap A B`. No quotient by an ideal is used.
- Finiteness and surjectivity of nu: `IsFinite X.fromReducedNormalization` and
  `Surjective X.fromReducedNormalization`.
- Finite nonempty fibre: `Set.Finite {y | X.fromReducedNormalization y = x}` and
  `Nonempty {y // X.fromReducedNormalization y = x}`.
- Structural inclusion on opens: injectivity of `(X.fromReducedNormalization.app U).hom`
  for every open U. The stalk inclusion is separately `Function.Injective (algebraMap A B)`.
- Closed fibre points and their structural residue fields: for each fibre subtype
  element y, `IsClosed ({y.val} : Set X.reducedNormalization)` and an isomorphism
  from its residue field to k whose inverse, under Spec, is precisely the composite
  of its canonical residue-field point, nu, and the given structure morphism.
- A is reduced and local: `_root_.IsReduced A` and `IsLocalRing A`.
  `ringKrullDim A = 1` is exactly Krull dimension one.
- Essentially finite type over k: `RingHom.EssFiniteType` of the structural ring map,
  written explicitly as global sections from `ΓSpecIso.inv` followed by the germ at x.
- Noetherian A: the existential binder `hnoeth : IsNoetherianRing A` is a conclusion,
  not an added hypothesis. Naming this proof lets the subsequent completion's canonical
  local-ring instance use it, without an illegal let binder or an extra assumption.
- Structural residue field of A: `e : X.residueField x ≅ CommRingCat.of k` with
  `Spec.map e.inv = X.fromSpecResidueField x ≫ structureMap`.
- Finite integral closure: `Module.Finite A B` and `Nonempty (B ≃ₐ[A]
  integralClosure A (FractionRing A))`. `FractionRing` is localization at all
  non-zero-divisors for an arbitrary commutative ring, including reducible rings.
  This is not a fraction field assumption or an integrality assumption on X.
- Finite length: there exist r and `F : Fin (r+1) → Submodule A M` with endpoints
  bottom and top, strictly increasing adjacent terms, and each adjacent module quotient
  `IsSimpleModule A`. There is no positivity constraint on r. `Module.length A M = r`
  records the length of this simple filtration.
- Finite dimension and length comparison: `@Module.Finite k M ...` and the equality
  of `@Module.finrank k M ...` with `Module.length A M` in extended naturals.
  Both use `Module.compHom M` with exactly the explicit structural k-to-A ring map,
  so scalars are fixed by the scheme's structure morphism, not an arbitrary k-action.
- H is `normalizationBaseCompletion X x = AdicCompletion (maximalIdeal A) A`.
  C is `normalizationStalkCompletion X x = AdicCompletion (maximalIdeal A).map B`;
  its ideal is `normalizationCompletionIdeal X x`. Powers of this image ideal give
  exactly the modules m_A^n B in the node's inverse limit.
- H is reduced, Noetherian, local, complete, and dimension one: the explicit
  `_root_.IsReduced H`, `IsNoetherianRing H`, `IsLocalRing H`,
  `IsAdicComplete (IsLocalRing.maximalIdeal H) H`, and `ringKrullDim H = 1` clauses.
- Structural residue field of H: bijectivity of the composite k → A → H → κ(H),
  with every map explicit. Thus this identifies the structural field, not merely
  some abstract field isomorphic to k.
- Canonical inclusion H into C: `i : H →ₐ[A] C`, injective, with its value at every
  n-th quotient specified by the image of a lift b in A. Since every quotient class
  has a lift, the displayed equations determine i uniquely.
- C is the tensor extension: `t : (H ⊗[A] B) ≃ₐ[A] C`, with
  `t (a ⊗ₜ b) = i a * algebraMap B C b`. This fixes the entire map on generators,
  in particular multiplication and the H-action. Tensor symmetry gives the node's
  written order B ⊗[A] H. No arbitrary algebra equivalence is substituted.
- Completed integral closure: `ec : C ≃+* integralClosure H (FractionRing H)` with
  `ec (i a) = algebraMap H _ a` for every a in H. This H-compatible identification
  is unique: an H-automorphism of the closure in Q(H) fixes all fractions, because
  every closure element has a regular denominator in H. Together with the specified
  i and t this is the node's canonical comparison.
- Canonical quotient comparison: `eM : M ≃ₗ[A] (C ⧸ i.toLinearMap.range)` with
  `eM (class c) = class (AdicCompletion.of ... c)` for every c in B. Restriction of
  this equivalence along the same structural k-to-A map used for finrank makes it
  the specified k-linear isomorphism. A-linearity here is the canonical map's
  scalar structure and exactly supplies k-linearity, not a chosen stronger hypothesis.
- Smooth at x: existence of an open U containing x with `Smooth (U.ι ≫ structureMap)`.
  The conclusion `Function.Bijective (algebraMap A B)` renders B=A under the
  structural inclusion; `Subsingleton M` renders M=0. Bare types do not use `IsZero`.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` and the algebraically closed finite-extension comparison.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`; `.Smooth`: `Smooth`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization` and the reduced-component construction.
- `Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper`: the six unconditional
  stalk/algebra/quotient/completion declarations listed above. Their full definitions
  were read; none is copied or replaced.
- `Mathlib.RingTheory.AdicCompletion.Basic`, `.Algebra`, `.Completeness`, `.LocalRing`:
  `AdicCompletion`, `IsAdicComplete`, `evalₐ`, `of`, the local-ring instance,
  completion maximal ideal and residue-field maps.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `.KrullDimension.Basic`: `ringKrullDim`; `.EssentialFiniteness`:
  `RingHom.EssFiniteType`; `.IntegralClosure.Algebra.Basic`: `integralClosure`;
  `.Finiteness.Defs`: `Module.Finite`; `.Length`: `Module.length` and additivity.
- Proof imports: `Sheaf.AlgebraicGeometry.CurveNormalizationCoherentSupport`
  (`Scheme.curve_normalization_coherent_support`),
  `Sheaf.AlgebraicGeometry.CoherentFiniteSupportSkyscrapers`
  (`Scheme.Modules.coherent_finite_support_skyscrapers`),
  `Sheaf.TraceFormula.CurveNormalizationCompletion`
  (`RingTheory.curve_normalization_completion`),
  `WeilConjectures.RingTheory.AdicCompletionNoetherian`
  (`AdicCompletion.isNoetherianRing`), and Mathlib's properness, quasi-finite fibres,
  and integral primes over maximal ideals. They are plain imports when used only
  by the future proof.
- `lem-trf-normalization-affine-stalk-closure` and
  `lem-trf-finite-colength-completion-comparison` have no recorded Lean module on
  this base, so no import can be added for them. They occur only in the proof plan;
  the statement already has all its objects from the recorded definition interfaces.

Edge cases checked: the empty scheme has no closed point x, so this theorem imposes
no spurious nonemptiness condition on it. A smooth closed point has B=A and zero
quotient, represented by r=0 with no simple factors. Reducible curves remain allowed:
`FractionRing` is the total fractions and B need not be local or a domain; fibres
may have multiple branches. Arbitrary characteristic is allowed. No regularity,
separatedness, properness, singularity, nonzero defect, or domain hypothesis was added.
H's local structure uses the Noetherian conclusion, not an input assumption.
All universes and variables are explicit, with both auto-implicit options disabled.

Searches made:

- msearch LeanFinder: “Normalization of a reduced algebraic curve has finite length
  local defect canonically unchanged by completion”: eight unrelated good-reduction,
  minimal-Weierstrass-model, and normalization-reduced hits; no exact statement.
- msearch Loogle `AdicCompletion, integralClosure`: zero hits.
- msearch grep `normalization.*completion|completion.*normalization|deltaInvariant`
  in Mathlib/AlgebraicGeometry: zero hits.
- msearch LeanSearch: “The normalization quotient of a reduced algebraic curve has
  finite length and its completion quotient is canonically isomorphic”: eight hits
  on finite length of a principal quotient and relative normalization; none includes
  the local curve, structural residue fields, length/dimension equality and comparison.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for normalization stalks, quotient,
  completion, and the item id: found the reused NormalizationSingularSkyscraper
  abbreviations, CurveNormalizationCompletion, and CurveNormalizationCoherentSupport.
  The old theorem only treats nonzero singular stalks and does not assert all the
  node's field/length/dimension clauses. No theorem states the assigned conjunction.
- rg in `dag/nodes` found the existing definition node
  `def-trf-normalization-pushforward-stalk`, which is added to stmt_deps. No duplicate
  definition node or Lean definition was introduced.

Validation: every compile used the prescribed scompile.py wrapper. The final module
compiled both as a sandbox module and at its library module name without diagnostics.
Only the single theorem proof is `sorry`. No live repository or launcher file was edited.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
