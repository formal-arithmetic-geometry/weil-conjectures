## Worker report

The delivery states lem-trf-separable-closed-point-formal-presentation, with its complete
seven-step proof plan in the theorem docstring and `sorry` as its entire proof. The natural
statement, proof, and proof dependencies are unchanged. Two definition nodes give the
presentation data and the canonical completed-Jacobian predicate needed to express the
universal quantifier over presentations. No dependency record is repaired.

The theorem is `Algebra.separable_closed_point_formal_presentation` in
`Sheaf.RingTheory.SeparableClosedPointFormalPresentation`.

Hypotheses and objects:

- A field k: `{k : Type u} [Field k]`.
- A finitely generated k-algebra S: `{S : Type v} [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S]`.
- A maximal ideal p: `(p : Ideal S) [p.IsMaximal]`.
- A is exactly `Localization.AtPrime p`, with its existing local-ring instance. Its maximal
  ideal is pA by `Localization.AtPrime.map_eq_maximalIdeal`; we use
  `IsLocalRing.maximalIdeal (Localization.AtPrime p)` for m throughout, so no second ideal
  or local-ring structure is chosen.
- F is `p.ResidueField`, definitionally `IsLocalRing.ResidueField (Localization.AtPrime p)`.
  For maximal p, `Ideal.bijective_algebraMap_quotient_residueField` identifies this canonically
  with S/p. This uses the recorded dependency's residue-field construction.
- Finite separability is `[FiniteDimensional k p.ResidueField]
  [Algebra.IsSeparable k p.ResidueField]`.
- A-hat is `Algebra.LocalCompletion (Localization.AtPrime p)`, a transparent abbreviation
  of `AdicCompletion (IsLocalRing.maximalIdeal A) A`. Its map from A is Mathlib's algebraMap.

Each conclusion:

- A is Noetherian: the first `IsNoetherianRing (Localization.AtPrime p)` conjunct; it is local
  by the canonical instance already required to form its maximal ideal.
- A-hat is Noetherian local: the two existential class witnesses immediately following that
  conjunct. Neither is a hypothesis. Its maximal ideal is m A-hat: the following ideal-map
  equality. Its maximal-adic completeness is the `IsAdicComplete` conjunct.
- Its residue field is F: the existential k-algebra equivalence `e` and the equality
  `e (IsLocalRing.residue _ z) = AdicCompletion.evalOneₐ ... z`. The equality specifies the
  canonical residue identification on every completed element, rather than an abstract
  field isomorphism.
- Existence of a section and power series presentation with n at least two: `Nonempty
  (FormalLocalPresentation k A)`. This is the existence assertion for explicitly defined
  data, not a definition obtained by choosing from an unproved existence theorem.
- Section sigma: `FormalLocalPresentation.sectionMap : F →ₐ[k] A-hat`, with
  `section_residue` saying its reduction is the identity. `map`, `constants`, and `surjective`
  specify the surjective F-algebra map for precisely this coefficient-field action.
  `n`, `two_le`, `s`, `relation`, `kernel`, and `kernel_le` give the numbers of variables and
  equations, exact kernel generation, and containment in the variable ideal.
  `adic_continuous` is the usual ideal-power definition of continuity for these adic topologies.
- Every presentation, including every coefficient section and every generating family:
  the binder `∀ P : FormalLocalPresentation k A` is outside both comparisons.
- The first completed differential cokernel: `HasCompletedJacobianPresentation k A F
  P.n P.s P.map.toRingHom P.relation`. Its definition uses the canonical continuous
  derivation D extending `a ↦ 1 ⊗ da`, and a C-linear surjection pi from `Fin n → C` with
  `pi (Pi.single i 1) = D (Phi (X i))`. Its kernel is exactly the span of the s columns
  `(Phi (pderiv F i (f j)))_i`. That span is the image of the specified matrix C^s → C^n,
  so these are exactly the cokernel clauses. The finite free modules use functions on Fin;
  these are canonically the finite direct sums in the node.
- Completed differentials use `C ⊗[A] KaehlerDifferential k A`; the canonical tensor symmetry
  identifies this with the written `KaehlerDifferential k A ⊗[A] C`. Choosing the completion
  as the first factor exposes Mathlib's existing C-module action and does not change M.
- Any field extension containing the specified embedded F: the universal field K binder,
  `[Field K] [Algebra k K]`, and `ι : p.ResidueField →ₐ[k] K`. Field maps are injective.
  The universes of k and S remain independent; K is allowed in `Type (max u v w)` for
  arbitrary w, avoiding a size restriction on extensions.
- The evaluation S tensor K → K is the real construction `closedPointTensorEvaluation p ι`
  using `Algebra.TensorProduct.lift`, `IsScalarTower.toAlgHom`, and `AlgHom.id`.
  It sends `a ⊗ c` to `ι (algebraMap S F a) * c` by `lift_tmul`.
  `ClosedPointBaseChangeLocalRing p ι` is exactly localization at its kernel; the prime
  witness is the existing `RingHom.ker_isPrime` proof. No additional prime is assumed.
- B is Noetherian local: `IsNoetherianRing (ClosedPointBaseChangeLocalRing p ι)` together
  with its standard localization local-ring instance.
- The local map A → B: the existential ring map g is specified on every a in S by the
  equality between `g (a/1)` and the localization of `a ⊗ 1`. The universal property of
  localization makes this uniquely the canonical map. `g.FaithfullyFlat` and `IsLocalHom g`
  state exactly faithful flatness and locality; g is not an unconstrained map.
- mB is the maximal ideal: the ideal-map equality following those map properties.
  The residue K: the K-algebra equivalence `ResidueField B ≃ₐ[K] K` and its pure-tensor
  formula fix the evaluation identification. Combined with mB = maximalIdeal B, this is
  precisely B/mB = K. The K-action on B is explicitly the canonical action through
  `Algebra.TensorProduct.includeRight`, then localization; the instance has real data.
- B-hat and its complete local K-algebra structure: the existential Noetherian/local class
  witnesses and the maximal-adic `IsAdicComplete` conjunct use the canonical completion.
- The completion map h is fixed on *every* finite quotient: whenever z reduces to a
  modulo m^r, h z reduces to g a modulo m_B^r. This is the inverse-limit characterization
  of the canonical map of completions; in particular it extends g and is continuous.
- The base-changed presentation: phi is a K-algebra map from `MvPowerSeries (Fin P.n) K`.
  The equation `phi (MvPowerSeries.map ι.toRingHom f) = h (P.map f)` fixes the comparison
  on the whole original power series ring, hence on every variable and every coefficient.
  The displayed K-algebra equivalence from the quotient by the coefficientwise images
  of `P.relation j` to B-hat is characterized by `e (Ideal.Quotient.mk _ f) = phi f`.
  It implies exact kernel equality and surjectivity of phi; it is explicitly local.
  Both sides carry their maximal-adic complete local structures, so locality of this
  algebra equivalence also gives continuity in both directions.
- The final Jacobian cokernel is `HasCompletedJacobianPresentation K B K P.n P.s
  phi.toRingHom (fun j ↦ MvPowerSeries.map ι.toRingHom (P.relation j))`.
  It uses the same variable and equation indices, the coefficientwise extended equations,
  and the same derivative construction. Partial differentiation commutes with coefficient
  extension, so this is exactly the node's same-Jacobian assertion.

Dependency declarations read and used:

- Mathlib.RingTheory.FiniteType: `Algebra.FiniteType`, finite generation of the top subalgebra.
- Mathlib.RingTheory.Localization.AtPrime.Basic: `Localization.AtPrime`, the localization at
  p.primeCompl, its local-ring instance and canonical maximal ideal.
- Mathlib.RingTheory.LocalRing.ResidueField.Ideal: `Ideal.ResidueField`, definitionally
  the residue field of the localization; quotient-residue bijectivity at a maximal ideal.
- Mathlib.FieldTheory.Separable: `Algebra.IsSeparable`, whose minimal-polynomial condition
  includes algebraicity; `FiniteDimensional` expresses finiteness.
- Mathlib.RingTheory.AdicCompletion.Basic/Algebra/LocalRing: `AdicCompletion`, its
  `algebraMap`, `evalₐ`, `evalOneₐ`, and `IsAdicComplete`.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
- Mathlib.RingTheory.MvPowerSeries.Basic/Derivative: `MvPowerSeries`, `C`, `X`, `map`,
  and `pderiv`; component rings and coefficient extension are not redefined.
- Mathlib.RingTheory.Kaehler.Basic: `KaehlerDifferential`, `KaehlerDifferential.D`,
  and the derivation construction whose universal property is `linearMapEquivDerivation`.
- Mathlib.RingTheory.Flat.FaithfullyFlat.Basic and Mathlib.RingTheory.RingHom.FaithfullyFlat:
  `Module.FaithfullyFlat` and `RingHom.FaithfullyFlat`; the latter uses the former through
  the ring map's module structure.
- Mathlib.LinearAlgebra.TensorProduct.Defs/Basic: `TensorProduct`, its bilinear constructors
  and universal map. Mathlib.RingTheory.TensorProduct.Maps supplies the algebra tensor lift.

The already stated proof dependencies are imported without `public`: the Mathlib flat-local,
faithfully-flat, completion, and finite-type APIs, and
`WeilConjectures.RingTheory.AdicCompletionNoetherian`,
`Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`,
`Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`, and
`Sheaf.RingTheory.PowerSeriesUniversalPropertyComplete`.
The currently unstated proof-only nodes lem-trf-completed-jacobian-differentials,
lem-trf-field-extension-completion-presentation, and
lem-trf-separable-residue-coefficient-section are named in the proof docstring but have no
module to import. No statement notion depends on their missing proofs. The live upstream
Noetherian-completion module was read through `scompile.py --source`, since it is absent
from the older local upstream checkout.

Edge cases checked: S may be nonreduced; p maximal excludes the zero ring automatically.
The field case A = F and zero-dimensional/artinian rings still allow n = 2 by adding dummy
variables and their equations. s = 0 is permitted and gives zero Jacobian column span.
The presentation is not required to be minimal. Identity field extensions, F = k, arbitrary
larger K, and arbitrary characteristics including two are retained. No algebraic closure,
regularity, reducedness, smoothness, dimension, or perfectness hypothesis was added. The
finite-separable assumption is retained: it is what makes residue-field differentials vanish
and the localized closed fibre equal K.

Searches: the real msearch.py LeanSearch, LeanFinder, Loogle, and Mathlib grep queries and
results are in searches.jsonl. In particular the whole-theorem query returned standard
etale/smooth presentations, and `KaehlerDifferential, AdicCompletion` returned zero Loogle
hits. The formal-presentation query found analytic power series and Weierstrass data, not
this record; the completed-Jacobian query found general completion maps and polynomial
cotangent complexes, not this predicate. Mathlib grep for the completed-differential/formal
presentation combinations returned zero hits. Direct rg searches in WeilConjectures,
lean/Sheaf, and dag/lean_names_upstream.json found no matching declarations; the item-id
search found only comments in consumers. DAG definition searches and blueprint_refs.py
searches for 'formal presentation' and 'completed Jacobian' found no existing definition
nodes. Existing theorem prerequisites are not copied or restated.

No STATEMENT-DISPUTED flag, statement correction, or dependency-interface fault is needed.
The first compile diagnosed the missing residue-field algebra import, repaired by importing
Mathlib.RingTheory.LocalRing.ResidueField.Basic. The next compile found that the evaluation
kernel's prime witness must be supplied explicitly to localization; it now uses the existing
Mathlib proof. Validation results are recorded below after compilation and dry run.

## New nodes

`def-trf-formal-local-presentation` defines the specified coefficient-field section and
continuous power series surjection, variable/equation counts, and exact kernel generators,
following varieties.tex Tag 0C52 and the item's dummy-variable convention. Its transparent
LocalCompletion helper specializes AdicCompletion and introduces no alternative completion.
The node contains no existence theorem and no postponed proof. LeanSearch, LeanFinder,
Mathlib grep, upstream/side-library grep, and DAG/blueprint searches found no existing record.

`def-trf-completed-jacobian-presentation` defines the canonical completed-Jacobian property
using the actual scalar extension of KaehlerDifferential, its continuous derivation, and an
explicit basis-normalized quotient map whose kernel is the Jacobian column span. It follows
the differential and completion passage in curves.tex Tag 0C4D. It does not define algebraic
Kaehler differentials of a power series ring as the finite module of continuous differentials.
Its definitions have real data and assert no existence theorem. The searches found only
ordinary polynomial differential presentations and generic completion constructions.

Validation: scompile.py compiled each of the three delivered modules separately in dependency
order, including their library-module forms, with exit code zero and no warnings. The final
library-file times were 2.4 s, 8.0 s, and 4.5 s, respectively. The source check confirms that
only lean and stmt_deps changed on the item, and that there is one sorry, solely the theorem
proof; both definition modules contain no sorry. Every Lean line is at most 100 characters.

Dry-run repair: the preflight signature reader excludes the terminating `:=` / `where` token.
The three lean.statement records were adjusted to its exact signature convention; no Lean
source or mathematical statement changed.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
