## Worker report

The module `Sheaf.RingTheory.HenselianFiniteGaloisLift` states
`HenselianLocalRing.finiteGaloisLift`, with one `sorry` and no new definitions.
Source: Stacks Project, `pione.tex`, Tag 0BSW, `lemma-identify-inertia`, the paragraph
beginning “Let kappa prime/kappa be a finite Galois extension”. The source's omitted
fraction-field/degree calculation is expanded in the node's seven proof steps;
the declaration docstring reproduces every step and names its dependencies.

The prior worker's stale-assignment message referred to Q09's stage-1 delivery.
The shared node has the Q09 split/review but no `lean` record; its ledger line does
not say “stage 2”. This delivery supplies stage 2 without changing that split.

Hypotheses, in order:

- The henselian local ring `(H,m,kappa)` is `(H : Type u) [CommRing H]
  [HenselianLocalRing H]`, with `m = IsLocalRing.maximalIdeal H` and
  `kappa = IsLocalRing.ResidueField H`. `HenselianLocalRing` already extends
  `IsLocalRing`; no additional hypothesis on H is needed.
- “Normal domain” is `[IsDomain H] [IsIntegrallyClosed H]`, exactly the recorded
  domain specialization of `def-weil-pbc-normal-ring`.
- A local H-algebra B is `(B : Type v) [CommRing B] [IsLocalRing B] [Algebra H B]`.
  Module-finiteness is `[Module.Finite H B]`. Etaleness is `[Algebra.Etale H B]`:
  the approved ring-algebra encoding of `def-weil-etale-morphism`, equivalent to
  `Etale (Spec.map (CommRingCat.ofHom (algebraMap H B)))`. It does not require
  H and B to share a universe.
- The given field extension e/kappa is `(e : Type w) [Field e]
  [Algebra (IsLocalRing.ResidueField H) e]`. Its H-algebra structure and
  `[IsScalarTower H (IsLocalRing.ResidueField H) e]` express the induced H action.
  Because H surjects onto its residue field, this compatible structure is unique;
  these are structure binders, not a new algebraic restriction.
- “Finite Galois”, including the stated separability and minimal-polynomial
  normality, is `[FiniteDimensional (IsLocalRing.ResidueField H) e]
  [IsGalois (IsLocalRing.ResidueField H) e]`. Mathlib `IsGalois` consists precisely
  of `Algebra.IsSeparable` and `Normal`; `Normal` says the minimal polynomials split.
- The identification `B/mB = e` is the actual algebra equivalence
  `r : (B ⧸ (IsLocalRing.maximalIdeal H).map (algebraMap H B)) ≃ₐ[H] e`.
  Thus `mB` is the extended ideal, not a separately chosen maximal ideal, and
  the identification respects the base residue-field extension. H-linearity
  implies kappa-linearity since H -> kappa is surjective.

Conclusions, clause by clause:

- “B is a normal domain” is `IsDomain B ∧ IsIntegrallyClosed B`.
- “H -> B is injective” is `Function.Injective (algebraMap H B)`.
- `K = Frac(H)` and `E = Frac(B)` are expressed by the conclusion's universal
  binders `[Field K] [Algebra H K] [IsFractionRing H K]` and
  `[Field E] [Algebra B E] [IsFractionRing B E]`. Their scalar towers specify the
  induced H -> B -> E and H -> K -> E inclusions. They quantify arbitrary
  presentations of the stated fields, after domain and injectivity have already
  been concluded; no assumption of B being a domain is smuggled into the theorem
  hypotheses. For every such pair of fraction fields, the induced K-algebra
  structure on E exists uniquely by localization, since H -> B is injective.
- The finite Galois extension is `FiniteDimensional K E ∧ IsGalois K E`.
- The degree equality is
  `Module.finrank K E = Module.finrank (IsLocalRing.ResidueField H) e`.
- `E = K tensor_H B` is an algebra equivalence
  `t : K ⊗[H] B ≃ₐ[K] E`, characterized on every pure tensor by
  `t (k ⊗ₜ[H] b) = algebraMap K E k * algebraMap B E b`.
  Pure tensors generate, so the comparison is uniquely specified and canonical.
- “B consists exactly of the elements of E satisfying a monic H-polynomial” is
  `∀ a : E, IsIntegral H a ↔ ∃ b : B, algebraMap B E b = a`.
  `IsIntegral` is the existing Mathlib monic-polynomial definition. The injection
  B -> E is supplied by its fraction-ring structure. This is exactly the
  integral-closure claim, not merely integrality in one direction.
- The first group isomorphism is
  `s : (E ≃ₐ[K] E) ≃* (B ≃ₐ[H] B)`; its formula
  `algebraMap B E (s σ b) = σ (algebraMap B E b)` specifies restriction.
  Injectivity of B -> E uniquely determines s. Its inverse is extension to fractions.
- The second group isomorphism is
  `q : (B ≃ₐ[H] B) ≃* (e ≃ₐ[IsLocalRing.ResidueField H] e)`;
  `q τ (r (Ideal.Quotient.mk _ b)) = r (Ideal.Quotient.mk _ (τ b))`
  specifies the action on B/mB through the given identification. The quotient
  map and r are surjective, so this determines q on every residue element.
  Both equivalences are multiplicative, including composition compatibility.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: recorded
  `IsStrictlyHenselianLocalRing` and its parents `HenselianRing`,
  `HenselianLocalRing`; this statement uses the last one, not strict henselianity.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  with `IsDomain` and `IsFractionRing` from its Mathlib imports. The normal-domain
  conjunction is the dependency node's prescribed inline form.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` and
  its affine ring-map equivalence; the existing `Algebra.Etale` is used here.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, via the public dependency imports.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, via
  `Mathlib.FieldTheory.Galois.Basic`, whose `IsGalois` includes this exact property.
- Already stated non-Mathlib proof dependencies are imported without `public`:
  `Sheaf.RingTheory.EtaleNormalRing` (`RingHom.Etale.isNormalRing`) and
  `Sheaf.RingTheory.HenselianFiniteEtaleMapBijective`
  (`CommAlgCat.FiniteEtale.bijective_baseChange_residueField_map_of_henselianLocalRing`).
  The remaining proof dependencies are the recorded Mathlib localization,
  finite-flat/free, integrality, fixed-field, and degree-multiplicativity lemmas;
  their owning modules are imported, with Galois.Basic already public.

Edge cases checked before finalizing the statement:

- H a field (m = 0): B is the finite separable field e, and the tensor and
  automorphism formulas reduce to the ordinary finite Galois extension case.
- The degree-one case e = kappa, including B = H: finrank is one and all displayed
  restriction/reduction formulas give the identity comparisons.
- No Noetherian, excellent, DVR, positive-characteristic, perfect-residue-field,
  or finite-residue-field restriction is present or needed. Infinite residue
  fields and all characteristics remain allowed.
- The zero ring is excluded by the stated domain/field assumptions and the local
  algebra's field closed fibre. No spurious nonemptiness hypothesis is added.
- A product of two nonzero finite etale factors is excluded by the node's own
  locality hypothesis, not silently selected by the Lean statement.
- The five universes u,v,w,x,y are explicitly bound and independent. No test
  algebra or index family is confined to a universe below H or B.
- The isomorphisms are characterized on all elements or generating tensors;
  arbitrary abstract group equivalences cannot satisfy the statement in place
  of the source's specified maps.

Searches made (all from the prescribed read-only trees, with msearch logging):

- LeanFinder: “A finite local etale algebra over a henselian normal local domain
  with finite Galois residue extension has a Galois fraction field extension of
  the same degree and identical automorphism groups”. Eight results include
  `IsGaloisGroup.iff_isFractionRing`, `to_isFractionRing`, `of_isFractionRing`,
  `toFractionRing`, and generic ramification/normal-closure results. They assume
  an established Galois ring action or invariant-ring identity and do not derive
  it from henselian reduction. None states this node.
- Loogle: `"IsHenselian", "IsGalois"`; zero results.
- msearch grep in Mathlib RingTheory:
  `hensel.*[Gg]alois|[Gg]alois.*hensel|[Ee]tale.*[Gg]alois|[Gg]alois.*[Ee]tale`;
  zero results.
- LeanSearch: “A finite etale local algebra over a henselian normal local domain
  with Galois residue field has Galois fraction field of the same degree and
  reduction is an isomorphism on automorphism groups”. Eight results include
  `IsGaloisGroup.to_isFractionRing`, `Algebra.FormallyEtale.iff_exists_algEquiv_prod`,
  `IsGalois.card_aut_eq_finrank`, `galRestrict`, and `galRestrictHom`.
  `galRestrict` was read: it supplies the first comparison only after an integral
  closure setup is established. None supplies all this node's conclusions.
- `rg` in Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no declaration named `finiteGaloisLift`.
- `grep -rn lem-wf-henselian-finite-galois-lift` in `WeilConjectures` found no
  attachment. Targeted henselian/Galois grep in `WeilConjectures` and `lean/Sheaf`
  found related residue actions and tame sequences but no finite local etale
  normal-domain lift theorem. The existing `HenselianResidueGaloisAction` concerns
  algebraic constants in an algebraic closure, not this finite-stage statement.

No new nodes or dependency repairs were needed. The item's natural-language
statement, proof, dependencies, and all non-lean fields are unchanged. No
STATEMENT-DISPUTED flag or source correction is necessary.

Validation: the entire delivered module is checked through the prescribed
`scompile.py` wrapper. The delivery dry run and final push use `deliver2.py`.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
