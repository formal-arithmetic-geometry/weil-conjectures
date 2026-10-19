## Worker report

The module `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` states
`AlgebraicGeometry.ProEtale.compactificationProjection_coefficient_coherence` with a
single `sorry`. It states the two equalities for the inverse of the actual
fixed-compactification projection transformation and the constructible domains of their
inputs. Helper definitions name its canonical inverse, its two explicit equations,
the finite lists of domain assertions, the canonical coefficient realization, and the full
quantified assertion; their data contain no `sorry`. A named instance applies the existing
finite-ring Noetherian theorem directly. There is no mathematical statement correction.

Hypothesis and clause correspondence:

- The finite field, its characteristic and its algebraic closure are `D : FiniteFieldDatum`;
  `l`, `[Fact l.Prime]` and `_hl : l ≠ D.p` give the coefficient prime. The arbitrary finite
  extension is `E`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]`. `Padic.coefficientExtensionRing l E (n + 1)` is the
  recorded quotient by the recorded uniformizer. Indexing the positive level by a natural
  predecessor covers every level ≥ 1, including level 1 at `n = 0`.
- The two `Over (Spec (CommRingCat.of D.k))` instances, and the locally finite type and
  quasi-compact instances on the structure morphisms, mean precisely finite-type k-schemes.
  `f.IsOver` says f is a k-morphism. `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and
  `[QuasiCompact f]` are precisely the separated finite-type hypotheses. Neither X nor Y is
  assumed separated over k.
- `c : Compactification f` gives the fixed open immersion `c.i`, proper map `c.g`, and
  factorization `c.comm`. `rightDerivedLowerShriekOfCompactification ... c` is exactly
  R(c.g)_* after exact termwise (c.i)_!. It is used at that same c in every expression.
- M, B and B' are objects of the ordinary unbounded derived categories of constant-A
  module sheaves on the small pro-etale sites. The standard `ULift` of the coefficient
  ring permits ModuleCat values of size u+1 while the scheme has size u; the site still
  has object universe u+1 and morphism universe u. There is no universe equality imposed.
- `cx M` in `CompactificationProjectionCoefficientCoherence` is
  `intrinsicFiniteTorsionConstructible` applied to the image under the canonical
  `sfIntrinsicDerivedEquivalence`. `ty B` and `ty B'` are the recorded
  `WeilConjectures.finiteTorConstructible` under the same equivalence. Thus M is only
  bounded constructible and B and B' additionally have finite Tor amplitude. The helpers
  `projectionCoherenceConstructible` and `projectionCoherenceFiniteTor` are abbreviations
  of these predicates, not alternative constructibility definitions.
- The existing global monoidal structure on the fixed-ring derived categories supplies
  tensor, associators and unitors. `leftDerivedUpperStarTensorIso` is the canonical
  inverse tensor structure map delta, and `leftDerivedUpperStarUnitIso` is e. Their source
  definitions are respectively the derived ordinary tensor comparison and the image of
  the degree-zero coefficient unit. `projectionCoherenceSymmetry` is the existing
  `DerivedMonoidal.braiding` of K-flat localization, with the Koszul sign. It chooses no
  arbitrary braided structure.
- `inverseCompactificationProjection` is literally P.map(symmetry), inverse of
  `((projectionMapOfCompactification ... c).app M).app B`, then symmetry. The upstream
  projection map's body is the proper counit mate followed by proper image of the open
  projection isomorphism and the pullback-composition comparison. Hence it is exactly PF
  from the node, with its specified normalization; no unconstrained projection family is
  supplied.
- `hunit` asserts invertibility of PF(M,1), `hprod` of PF(M,B tensor B'), `hleft` of
  PF(SB' tensor M,B), and `hright` of PF(M,B'). These are precisely the four components
  inverted in the two equations. Invertibility is assumed, never concluded.
- `CompactificationProjectionUnit` is the displayed unit equality in Lean's diagrammatic
  order: pi(1,M) followed by lambda equals P.map(e tensor identity followed by lambda).
- `CompactificationProjectionAssoc` is the displayed coefficient-associativity equality:
  pi(B tensor B',M) followed by alpha equals P.map(delta tensor identity followed by
  alpha), then pi(B,SB' tensor M), then B tensor pi(B',M). All parentheses and functors
  occur explicitly in that definition. No permutation is hidden in a structural arrow.
- `CompactificationProjectionDomains` lists the unit and product coefficient domains,
  their pulled-back finite-Tor domains, the tensors with M and their compact-support
  images, and the tensor targets on Y. The main theorem supplies only the canonical
  transported intrinsic predicates to the full quantified assertion and this list. The
  quantifiers over M, B, B' and the seven domain/invertibility hypotheses are inside the
  fully defined assertion, so none of the objects or hypotheses is omitted. In particular no finite Tor amplitude
  of M is required.
- No right adjoint of compact support, smoothness, purity, change of compactification,
  or composition of two geometric morphisms is introduced.

Dependency declarations and source inspection:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  construction module: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, its integer ring, uniformizer and quotient ideal.
- Scheme-morphism-properties is a recorded convention node: finite type is
  `LocallyOfFiniteType` plus `QuasiCompact`, and separated is `IsSeparated`.
- `WeilConjectures.Compactification.Refinement` / `...Defs`: `Compactification`, with
  fields `Z`, `i`, `g`, `comm`, and the open/proper instances. Refinements are not used.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the recorded module-sheaf categories
  and coefficient realization. `SfIntrinsicRealizationTransport` gives the canonical
  derived equivalence for the intrinsic constant-ring presentation.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`.
- Compact support: the item uses the fixed-ring
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`,
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`, the presentation
  in which the canonical projection map exists. (Reviewer correction: on the current base
  the `def-compact-support-direct-image-detailed` record is Q13's intrinsic
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`, the same Rr_* j_! on the intrinsic
  coefficient category that `sfIntrinsicDerivedEquivalence` identifies with this one. That
  record is left unchanged; the item's `lean.note` says so.)
- The finite-coefficient `...Derived.Tensor`, `...Derived.UpperLowerStar`, and
  `...Derived.UpperStarMon.Comparison` supply the actual K-flat tensor, the ordinary
  derived inverse image, `leftDerivedUpperStarTensorIso`, and
  `leftDerivedUpperStarUnitIso`. These are the fixed-ring coordinates of the finite
  operations in `Sheaf.Paper.DerivedPullbackTensorHom` and its recorded canonical tensor
  comparison. Their full source signatures and docstrings were read via scompile --source.
- `Sheaf.Paper.FinitePullbackTensorComparison`, an already landed definition node added
  to stmt_deps, supplies the existing positive-level coefficient-finiteness instance.
  No second finiteness instance is declared.
  `projectionCoherenceCoefficientNoetherian` applies Mathlib's
  `isNoetherian_of_finite` at this quotient to avoid repeated low-priority instance search. Its canonical comparisons and the full
  `DerivedPullbackTensorIso` module supply the intrinsic comparison/coherence proof route.
- `Mathlib.CategoryTheory.Monoidal.Functor`: `Functor.CoreMonoidal`, `Functor.Monoidal`,
  their inverse tensor/unit maps; `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`:
  `Functor.ProjectionFormula.unit` and `.assoc`, whose formulas are exactly the two named
  equation definitions here. No global ProjectionFormula object is asserted: only the
  specified components are assumed invertible.
- All stated proof dependencies are imported: `DerivedPullbackTensorIso`,
  `PullbackTorAmplitude`, `FiniteCoefficientTensorCtf`,
  `FiniteCompactSupportConstructibility`, `RingedDerivedClosedSymmetricMonoidal`, and the
  Mathlib free-monoidal coherence and adjunction construction modules. The genuinely
  unstated proof-only dependency `lem-sf-open-tensor-normalization` has no module to
  import and is not replaced or assumed. Its exact use is retained in the proof docstring.

Sources checked directly: Stacks `sites-cohomology.tex`, the counit definition at
`equation-projection-formula-map` (0B56), the derived open tensor identity at
`lemma-j-shriek-and-tensor` (0GL1), and the current main-20261015 blueprint
`sk-prop-cohsm.proof.md`, equation (G13). The docstring carries all nine DAG proof steps,
including forward proper/open equations, their pasting, inversion only at the specified
components, and the constructible-domain check.

Edge cases checked: empty X or Y, zero inputs, unit coefficients, the first positive
coefficient level, and M without finite Tor amplitude are all retained. The unit is
represented by A in degree zero; the canonical pullback unit map has exactly that source.
The neighboring `finiteProjectionAction_compactification` is not a duplicate: it states
forward tensor-action formulas with extra absolute separatedness hypotheses, whereas this
node states the inverse unit and coefficient-associativity laws without those hypotheses.

Searches for existing statements:

- msearch leanfinder: “The inverse compactification projection formula maps obey tensor
  unit and coefficient associativity coherence” returned eight unrelated representation,
  free-module and general unit isomorphism results, with no match.
- msearch loogle: `CategoryTheory.Functor.ProjectionFormula` returned no Mathlib match
  (unknown identifier in Mathlib's index); the project framework does contain this generic
  definition, which was read and used as the equation convention.
- msearch grep in CategoryTheory:
  `projection.*(unit|assoc|coheren)|(unit|assoc|coheren).*projection` returned only
  `Mathlib/CategoryTheory/Sites/Coherent/SequentialLimit.lean`, unrelated.
- rg over the upstream WeilConjectures sources and the shared Sheaf sources found the
  canonical projection construction, generic projection-formula equations, and the
  neighboring finite action lemma, but no theorem with this node's hypotheses and both
  requested inverse equations. Searching upstream for the exact item id returned no match.
- Read the upstream name index and searched the new names; no existing declaration was
  replaced or shadowed. Searches use only the directories authorized by the brief.

## Dependency modules

`def-weil-derived-tensor`: existing-presentation repair only; no new module. Its previous
intrinsic tensor has SheafOfModules endpoints, so it cannot type the fixed-ring projection
map of the fixed-ring compact-support functor used here. The record now identifies the existing
`AlgebraicGeometry.ProEtale.derivedTensor` in the current finite-coefficient source module.
It is the same ordinary K-flat total tensor. The previous intrinsic module remains intact.

The item uses the finite projection component of `def-exchange-projection` directly:
`AlgebraicGeometry.ProEtale.projectionMapOfCompactification`, from
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`.
This is precisely the third component of
`AlgebraicGeometry.ProEtale.finiteExchangeProjection` in
`Sheaf.Paper.ExchangeProjection` (lines 119–133), whose body explicitly supplies that map.
Its proper-counit/open-projection composite is the node's finite PF^c. The full
`def-exchange-projection` record remains Q14's
`CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` in
`Sheaf.Paper.ExchangeProjectionSuppliedDomains`, retaining exchange, compact exchange,
projection and the supplied-domain coefficient interfaces. No replacement dependency
record for that node is included in this delivery.


The equation predicates are defined first for general monoidal categories. The complete
assertion then specializes them to the existing fixed-ring sheaf operations at V, and the
main theorem specializes V and its predicates to the actual positive quotient. This keeps
the type checker from repeatedly comparing large derived monoidal instance terms. Neither
the theorem nor this fully defined assertion accepts an arbitrary projection map, tensor
comparison, coefficient realization, or constructibility predicate as a hypothesis: all
are the specified canonical values at the main theorem.

Verification: the complete delivered module passed the prescribed scompile.py checks in
the sandbox (10.2 s) and as its actual library module (6.5 s), with no warnings. The
specialization is kept under the unchanged 60-second limit by the generic assertion
interface; no mathematical assumption or canonical construction was changed.

## Returned-delivery repair

The independent review of immutable head `4bdcb3da4004` accepted the item statement,
the full module and the same-notion `def-weil-derived-tensor` presentation repair.
Its H13/H4 return concerned only narrowing the whole `def-exchange-projection`
record to one finite map. Removed that node file from this packet and documented the
existing finite specialization in the item's `lean.note` and above. The accepted Lean
module is unchanged. The current shared base still records Q14's complete supplied-domain
interface; this repair preserves it and changes no consumer.

The review's proof-stage observations are retained: `def-pur-finite-pullback-tensor-comparison`
is an unused statement-dependency entry (its module supplies the coefficient instance),
and S, delta and e are the fixed-ring upstream maps. Stage 3 must transport
`lem-pur-derived-pullback-tensor-iso` to those maps. These observations require no change
to the accepted stage-2 module or its four invertibility hypotheses.

The initial saved packet passed the prescribed dry run at `edfa42662a`; that mechanical
pass did not discharge the semantic H13/H4 repair. The final repaired packet is checked
again before delivery.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the
maintainer's independent review is the only review. The independent cc reviewer of head
`55428d46bb51` (NT-stage2-cc-55428d46b) read the delivery as follows; the full record is its
review.md.

Clause by clause (node statement → Lean → verdict):

- k₀ finite of characteristic p, k its algebraic closure → `D : FiniteFieldDatum` → correct.
- ℓ ≠ p prime, E/Q_ℓ finite, A = O_E/ϖ_E^n, n ≥ 1 → `[Fact l.Prime]`, `_hl`, `E` with
  `FiniteDimensional (Padic l) E`, `Padic.coefficientExtensionRing l E (n + 1)` → correct;
  n + 1 covers every level ≥ 1.
- X, Y finite-type k-schemes; f separated of finite type over k → `Over (Spec k)`,
  `LocallyOfFiniteType`/`QuasiCompact` of the structure maps, `f.IsOver`, `IsSeparated f`,
  `LocallyOfFiniteType f`, `QuasiCompact f` → correct; X, Y not assumed separated.
- fixed compactification c = (j, r) → `c : Compactification f`, used at the same c
  everywhere → correct.
- ordinary constant-A derived categories on the small pro-étale sites, derived tensor →
  `DerivedCategory (Sheaf (ProEt.topology _) (ModuleCat.{u+1} (ULift A)))` with its K-flat
  monoidal structure (`⊗` is `curriedTensor`, i.e. `ProEtale.derivedTensor`) → correct; no
  universe equality.
- P = Rr_* j_! → `rightDerivedLowerShriekOfCompactification V c` → correct (see the
  presentation note above).
- S = Lf^*, δ, e → `L((f)^*[V])`, `(leftDerivedUpperStarTensorIso V f B B').hom :
  S(B ⊗ B') ⟶ SB ⊗ SB'`, `(leftDerivedUpperStarUnitIso V f).hom : S 1 ⟶ 1` → correct
  directions.
- PF^c_{M,B} : PM ⊗ B → P(M ⊗ SB) of def-exchange-projection →
  `((projectionMapOfCompactification V c).app M).app B`, of type
  `derivedTensorRightDerivedLowerShriek ⟶ rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar`
  → correct; the def-exchange-projection record is not changed.
- π_{B,M} = β ∘ PF⁻¹ ∘ P(β) → `inverseCompactificationProjection` with the derived Koszul
  braiding → correct.
- invertibility only as hypotheses → `hunit`, `hprod`, `hleft`, `hright`: exactly the four
  inverted components → correct.
- M ∈ D^b_c(X), B, B' ∈ D^b_ctf(Y) → `cx M`, `ty B`, `ty B'`, the recorded intrinsic
  predicates through the canonical realization → correct; M has no Tor condition.
- unit equation → `CompactificationProjectionUnit` → correct order and maps.
- associativity equation → `CompactificationProjectionAssoc` → correct order, parentheses
  and maps.
- all displayed inputs lie in the stated domains → `CompactificationProjectionDomains` →
  correct; every listed membership is true.

Edge cases: empty X or Y, zero objects, unit coefficients, the first level (n = 0 in Lean)
and universes are all covered.

Compile: `tools/nt_compile.py` on the delivered module, rc 0, 4.8 s, with no errors; the
definitions use only propext, Classical.choice and Quot.sound.

Reviewer changes: this section; the compact-support sentence under "Dependency
declarations"; and the item's `lean.note`, which now records the fixed-ring versus
intrinsic presentation. The module and statement are unchanged.
