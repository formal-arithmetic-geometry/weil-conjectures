## Worker report

The module `Sheaf.RingTheory.DvrNormalizedFiniteStageDescent` states
`IsDiscreteValuationRing.exists_normalized_finite_stage`, with its proof `sorry`.
The item statement, proof and other inherited fields are unchanged. Its statement
dependencies gain the definition node described below. No statement correction is
made in this delivery: the finite-module hypothesis was already part of the
reviewed stage-1 statement supplied to this worker.

Hypothesis and conclusion correspondence, checked with the node and Lean open:

- The rings A and B have `CommRing`, `IsDomain`, `IsDiscreteValuationRing` instances.
  `Algebra A B`, `IsLocalHom (algebraMap A B)` and `hinj` give exactly the injective
  local homomorphism. There is no completeness or separability assumption on it.
- K and L have `Field`, `Algebra A K`, `IsFractionRing A K`, `Algebra B L` and
  `IsFractionRing B L`. `Algebra K L` and the two scalar towers identify the
  specified inclusion of fraction fields with the original ring map. The extra
  A-to-L structure is compatibility data, not an extra mathematical condition.
- `hfiniteType` quantifies a commutative A-algebra U, a prime p, the recorded
  `RingHom.FiniteType (algebraMap A U)`, and `Nonempty (B ≃ₐ[A] Localization.AtPrime p)`.
  It does not assume B is a finite type algebra without localization. U can be
  represented in `Type (max u v)` by adjoining finitely many generators over A.
- P is a field with `Algebra K P` and `Algebra.IsAlgebraic K P`; the A-to-P algebra
  and scalar tower are the prescribed composite. No finiteness is assumed for P.
- R_P is literally `integralClosure A P`. C_P is the existing
  `eppUpperClosure B K L P`, literally `integralClosure B (eppReducedTensor K L P)`.
  `eppReducedTensor` is `(L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)`, so reduction kills
  all nilpotents; no separable-only tensor or chosen field factor is substituted.
- `hfiniteModule` is `Module.Finite (B ⊗[A] integralClosure A P) C_P` with the
  module structure explicitly given by `normalizedTensorMultiplication ...`.
  This is the canonical multiplication action, not an arbitrary algebra action.
- The two `IsNoetherianRing` instances assert exactly Noetherianity of R_P and C_P.
  `hmaxLower` and `hmaxUpper` assert finiteness of their sets of maximal ideals.
- `hlocal` ranges over every ideal q with `q.IsMaximal`. Its contraction is
  `q.comap (eppNormalizationMap A B K L P)`, using the existing canonical map
  r ↦ [1 tensor r]. The first conjunct states this contraction is maximal.
- The next conjunct is `IsDiscreteValuationRing (Localization.AtPrime n)`.
  The lower normalization is a subring of the field P, so its domain instance
  and that of its localization are inferred. For the upper localization the
  statement explicitly quantifies `hdom : IsDomain ...` before the DVR condition:
  C_P itself is not assumed a domain and can have several generic branches.
- `Ideal.map ((algebraMap C_P (Localization.AtPrime q)).comp normalizationMap) n =
  Ideal.map (algebraMap C_P (Localization.AtPrime q)) q` is exactly
  n(C_P)_q = q(C_P)_q. No uniformizer choice is added to the hypotheses.
- The residue extension is the algebra induced by
  `Ideal.ResidueField.map n q normalizationMap rfl`. The statement explicitly
  supplies its `toAlgebra` to `Algebra.IsSeparableExtension`, the recorded notion
  of separability allowing transcendental extensions. It does not replace this
  by `Algebra.IsSeparable`, which would force algebraicity.
- Finitely generated *as a field* is `IntermediateField.FG` of top for that same
  residue-field algebra. It is not `Algebra.FiniteType` and does not force a finite
  algebraic residue extension.
- The conclusion is `∃ K₀ : IntermediateField K P, Module.Finite K K₀ ∧ ...`.
  Thus K₀ is inside the given P and finite-dimensional over K. For each maximal
  q of `eppUpperClosure B K L K₀` the conclusion repeats precisely maximal
  contraction, lower DVR, upper DVR, extended ideal equality and separability
  for the canonical residue map. It adds no finite-generation conclusion.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  including its domain parameter and nonzero maximal ideal condition.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (and its underlying
  `Algebra.FiniteType` definition).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField` and
  `Ideal.ResidueField.map`, with its exact contraction hypothesis.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, whose
  carrier is `IsIntegral`; `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `WeilConjectures.FieldTheory.SeparableExtension`: `Algebra.IsSeparableExtension`
  and its definition in terms of `Algebra.IsSeparablyGenerated`.
- `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits`: `eppReducedTensor`,
  `eppUpperClosure`, `eppNormalizationMap`, read with full signatures and docs.
  Only these existing real constructions are used from that module. Its Epp
  existence theorem is not a hypothesis and is not used to choose an object.
- `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`: `IntermediateField.FG`.
- Stated proof dependencies are imported privately: integral injective lying-over
  from `Mathlib.RingTheory.Spectrum.Prime.Topology`, and going-up from
  `Mathlib.RingTheory.Ideal.GoingUp`. The three statement-only proof lemmas
  (algebraic-normalization structure, finite-normalization algebraic model,
  separability tensor-field descent) have no recorded modules to import.

Edge cases: K₀ = K (the bottom intermediate field) is allowed. P = K and finite P
are included. Purely inseparable algebraic P and nonalgebraic residue extensions
are included. The upper normalization may have multiple factors: no `IsDomain`
on C_P is imposed. The residue action is canonical even without a globally
chosen R_P-algebra instance on C_P. DVRs exclude fields exactly as the node does.
All five base object universes are independent; tensor and residue universes are
inferred maxima. There is no artificial universe equality or test-algebra
quantification. The empty-maximal-ideal situation is not separately excluded by
an invented assumption.

Searches actually run using msearch.py under Q120 and this item:

- LeanFinder: `Finite stage descent of unramified localizations of integral closures
  of DVRs in algebraic extensions`. Eight hits concerning unramified localizations
  and ramification, no finite normalized-stage descent theorem.
- Loogle: `IsDiscreteValuationRing, integralClosure`. Zero hits.
- Mathlib grep: `integralClosure.*[Tt]ensor|[Tt]ensor.*integralClosure|[Ff]inite.*[Ss]tage`
  in RingTheory. Found `TensorProduct.toIntegralClosure` and related smooth and
  étale results, not the item. Its generic comparison is used in the new definition.
- LeanSearch and LeanFinder for canonical integral-closure maps to reduced tensor
  normalizations found `AlgHom.mapIntegralClosure`, `IsIntegralClosure.lift` and
  `TensorProduct.toIntegralClosure`; none supplies the reduced generic target.
- Further LeanSearch for the canonical B tensor R_P multiplication, Loogle
  `TensorProduct.toIntegralClosure`, and Mathlib grep
  `toIntegralClosure|[Nn]ormaliz.*[Tt]ensor.*[Mm]ap` are recorded with their actual
  full results in the new node. All returned successfully.
- `rg` of Mathlib, WeilConjectures and Sheaf for the proposed names found no
  duplicate. `rg` of WeilConjectures for this item's id found none; concept
  searches in both project libraries found the existing Epp helpers, which are
  reused. DAG-wide searches for the multiplication and normalization names found
  the Epp node and the existing normalization model/structure lemmas, but no
  definition node for the multiplication map. Blueprint searches `normalized tensor`,
  `normalization multiplication`, `canonical multiplication` found no matching unit.

The source read is `literature/stacks-project/more-algebra.tex`, proposition
`proposition-epp-essentially-finite-type`, all proof paragraphs, particularly its
last three. The inherited stage-1 review records that the original unrestricted
09II descent argument is false, and that the extra finite-module assumption
repairs this auxiliary statement. That assumption remains explicit. The inherited
`split_report` dispute concerns the earlier unrestricted statement and the parent
Epp proof's use of the repaired lemma; it is not silently weakened or deleted.
No new statement dispute or node correction is asserted here.

Validation: scompile.py compiled each module separately in dependency order,
including the library-module form, cleanly. The map is a real construction and
has no `sorry`; the only postponed theorem is `exists_normalized_finite_stage`.
Final compilation and delivery preflight results are appended below.

## New nodes

`def-sfb-normalized-tensor-multiplication` defines the missing canonical
`B ⊗[A] integralClosure A P →+* integralClosure B ((L ⊗[K] P)_red)`.
Source: 09EM's construction and 09II's displayed canonical tensor comparison in
the final descent argument, used by the already corrected finite-module hypothesis.
The Epp module already owns the reduced tensor and normalization map; these are
reused, not copied. The new map is constructed by `TensorProduct.toIntegralClosure`
followed by `AlgHom.mapIntegralClosure` of the actual generic tensor map. Its
formula is b tensor r ↦ [b tensor r], with the natural B and P inclusions.
The generic Mathlib comparison has target the integral closure in B tensor_A P,
so it is a component of the construction and not an exact existing match.
The new node carries the required searches, provenance and import_flags.

## Second reading by Q120

A separate second pass re-opened the item JSON and both complete Lean files.
No other agent was started, as the dispatcher brief explicitly forbids this.
I checked the correspondence above again, with particular attention to the
finite-module action and the two different meanings of separability. Findings
repaired before delivery: the canonical multiplication was rewritten as a
composition of existing Mathlib constructions, eliminating the initially
contemplated postponed compatibility proof; the `IntermediateField.FG` arguments
were put in the declaration's actual parameter order; nonexisting guessed FG
module names were replaced with `IntermediateField.Adjoin.Defs`; long residue
signatures were wrapped. The final comparison retains every local hypothesis,
the field-finite-generation hypothesis only at P, and all five clauses at K₀.
The lower DVR's domain instance is canonical; the upper DVR's domain condition
is explicit and existential. The conclusion quantifies actual intermediate
fields, including bottom. No statement change was needed.

Final checks: both finished source modules compiled cleanly through scompile.py
in dependency order (2.6 seconds and 4.4 seconds in library-module form).
The first dry run found only that its signature extractor starts at `def`,
excluding the `noncomputable` modifier. The new node signature was adjusted to
that convention; its mathematical signature and module are unchanged. The two
combined DAG citations were also separated into individual bracket citations.
The Epp parent cannot import this theorem's module directly while its helpers
remain in the parent module: that proof import would close a module cycle.
Per stages/2-statements.md §3(7), omit that parent proof import pending extraction
of the shared helper definitions into a lower module by the maintainer. This
delivery uses the existing definitions and never assumes the Epp theorem.

## Maintainer second reader's fix (2026-10-24)

The delivered `NormalizedTensorMultiplication` imported `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits`.
That module belongs to lem-sfb-epp-essentially-finite-type-traits, and the parent's proof_deps contain this item,
so the stage-3 proof of the parent could not import this item (an import cycle). The fix removes that import.
The def node's module now owns the 09EM helpers with Mathlib-only imports:
`normalizedReducedTensor` ((L ⊗[K] P)/nilradical), `normalizedUpperClosure` (integral closure of B in it),
`normalizedTensorMultiplication` (body unchanged), and `normalizedLowerMap` (its restriction along `includeRight`,
r ↦ [1 ⊗ r]). The item states the same clauses with `normalizedUpperClosure`/`normalizedLowerMap` in place of
`eppUpperClosure`/`eppNormalizationMap`. A test file compiled clean and checked
`normalizedUpperClosure B K L P = eppUpperClosure B K L P` (rfl) and
`normalizedLowerMap A B K L P = eppNormalizationMap A B K L P` (ext; simp; rfl), so the mathematics is unchanged and the
Epp module can import this def module and abbreviate its helpers to these.
