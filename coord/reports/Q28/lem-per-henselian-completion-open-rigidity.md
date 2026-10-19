## Worker report

The module `Sheaf.AlgebraicGeometry.HenselianCompletionOpenRigidity` states
`AlgebraicGeometry.Etale.bijective_cohomologyMap_henselianCompletion_openComplement`.
Its sole theorem has proof `sorry`; there are no new definitions or helper axioms.
The item is unchanged except for `lean`. In particular the Q27 stage-1 split and
its reviewed proof route are retained. The previous assignment-superseded message
concerned resplitting: this delivery supplies the previously absent stage-2 statement.

Hypothesis and clause correspondence:

- A commutative Noetherian ring C is `(C : Type u) [CommRing C]
  [IsNoetherianRing C]`. An ideal I is `(I : Ideal C)` and the henselian pair is
  `[HenselianRing C I]`. There is no locality assumption on C.
- The completion is the existing `AdicCompletion I C`. Its canonical map is
  `algebraMap C (AdicCompletion I C)`, with the existing completion algebra
  structure, and its spectrum morphism is `Spec.map (CommRingCat.ofHom ...)`.
  Thus the completion is constructed from compatible quotient sequences, not
  supplied as an arbitrary algebra or as an existential witness.
- X and the completed X are respectively `Spec (CommRingCat.of C)` and
  `Spec (CommRingCat.of (AdicCompletion I C))` (the latter is inferred as the
  domain of `Spec.map`).
- V(I) is `PrimeSpectrum.zeroLocus (I : Set C)`, exactly the primes containing I.
  U is the open `⟨(PrimeSpectrum.zeroLocus (I : Set C))ᶜ,
  (PrimeSpectrum.isClosed_zeroLocus (I : Set C)).isOpen_compl⟩`.
  `Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))` gives its open subscheme,
  and `Scheme.Opens.ι` is its inclusion.
- The completed open is exactly the categorical pullback of the canonical
  completion morphism and this inclusion. Its map to U is `pullback.snd` in
  the statement, so neither an arbitrary map nor an independently chosen
  comparison is introduced. This spells out the node's specified fibre product.
- Every small-etale abelian sheaf F on U is quantified by the binder
  `F : Sheaf (...).smallEtaleTopology AddCommGrpCat.{u + 1}`. The coefficient
  universe follows the existing small-etale cohomology API for `Scheme.{u}`;
  no independent smaller universe is used for test objects.
- `(hF : F.IsTorsion)` uses the recorded local-section predicate: every section
  becomes of finite additive order on a covering sieve. It imposes neither a
  global annihilator nor torsion on every whole group of sections.
- `(q : ℕ)` covers precisely the integers q >= 0, including q=0.
- `cohomologyMap (pullback.snd ...) F q` is the existing canonical inverse-image
  homomorphism `Sheaf.H F q →+ Sheaf.H ((upperStar ...).obj F) q`.
  `Function.Bijective` states that this very homomorphism is an isomorphism of
  abelian groups. It asserts more than merely an abstract group isomorphism.
  `Sheaf.H` is the existing Ext-based sheaf cohomology encoding used by the
  project and allowed in the recorded etale-cohomology dependency note.
- Naturality in F is already `Etale.cohomologyMap_map` in the imported comparison
  module, so follows from the choice of the canonical map in the signature.
  The theorem adds no excellence, regularity, constructibility, invertibility
  of torsion orders, finite generation of F, or boundedness hypothesis.

Dependency declarations read and used (module, declaration):

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` and its ideal-finiteness
  characterization: def-weil-pbc-noetherian-ring.
- `WeilConjectures.Mathlib.RingTheory.Henselian` and its Mathlib import
  `Mathlib.RingTheory.Henselian`, `HenselianRing`:
  def-weil-pbc-henselian-terminology. The other two notions recorded in that node
  are `HenselianLocalRing` and `IsStrictlyHenselianLocalRing`; they are not assumed.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`, `AdicCompletion` and
  its canonical algebra map: def-weil-pbc-adic-completion.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`:
  def-weil-affine-spectrum.
- `Mathlib.CategoryTheory.Sites.Sheaf`, `CategoryTheory.Sheaf`, specialized with
  `Scheme.smallEtaleTopology` and `AddCommGrpCat`: def-weil-pbc-abelian-etale-sheaves.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves` (published source in the
  side-project source tree), and
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`,
  `CategoryTheory.Sheaf.IsTorsion`: def-weil-pbc-etale-sheaves.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `Etale.upperStar`:
  def-weil-pbc-inverse-image. The imported `.TopologicalInvariance` module gives
  its canonical `Etale.cohomologyMap` and `Etale.cohomologyMap_map`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `Etale.cohomology` and
  `Etale.rightDerivedGlobalSections`: def-weil-pbc-etale-cohomology. Its recorded
  note explicitly permits `CategoryTheory.Sheaf.H`, used here to retain the
  existing canonical cohomology map without rebuilding comparison machinery.

The proof-only imports `.AdicCompletion.LocalRing` and `.Completeness` provide
`AdicCompletion.isAdicComplete_self` and `AdicCompletion.ker_evalOneₐ_eq_map` from
lem-weil-pbc-adic-completion-mod-ideal. The recorded
lem-weil-pbc-complete-pair-henselian is `IsAdicComplete.henselianRing` in the
already imported `Mathlib.RingTheory.Henselian`. The remaining proof dependencies
lem-per-admissible-modification-cohomology-presentation,
lem-per-admissible-modification-valuative-stalks and
lem-per-dense-henselian-field-etale-comparison currently have no recorded Lean
module, so no import is available for them. Their exact proof roles are preserved
step by step in the theorem docstring; their absence does not affect typing.

Source and edge cases checked before writing:

- Read ILO Expose XX section 4.4, printed pp.373--374 (PDF pages 379--380):
  CTC for maps of henselian pairs with finitely generated I, and the displayed
  open-complement comparison (*), followed by the admissible-blowup spectral
  sequence and dense-henselian-valued-field reduction. The supplied reviewed
  node gives the Noetherian general-pair cohomology formulation. Nothing in
  the Lean adds the strictly local assumption used in the source's stalk proof.
- Nilpotent I, in particular I=0: V(I) is all of Spec C and U is empty. The same
  pullback is empty, so the cohomology groups are zero. The statement allows it.
- I=C: the henselian pair's Jacobson condition forces the zero ring, whose
  spectrum is empty; the zero ring is not excluded.
- q=0: the ordinary sections comparison is included by the Nat degree binder.
- C already I-adically complete: the specified completion map is an isomorphism,
  giving the expected inverse-image comparison; the formulation does not
  require completion to be a proper extension.
- C need not be local or excellent. There is no hidden `[Nontrivial C]`,
  `[IsLocalRing C]`, or invertibility-of-coefficient-orders assumption.
- Local torsion with unbounded orders is retained through `F.IsTorsion`.

Searches for an existing exact declaration:

1. `msearch.py ... leanfinder`, query: "Etale cohomology of the open complement of
   a Noetherian henselian pair is invariant under adic completion for torsion
   abelian sheaves". Eight hits: localCohomology.isoSelfLERadical,
   IsAdicComplete.henselianRing, BDeRhamPlus, BDeRham, AdicCompletion.map_exact,
   AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
   AdicCompletion.flat_of_isNoetherian and
   AdicCompletion.coe_ofTensorProductEquivOfFiniteNoetherian. Their returned
   signatures concern module local cohomology or algebraic completion, not
   cohomology of a small-etale torsion sheaf on the open complement.
2. `msearch.py ... loogle`, query: `"HenselianRing", "cohomology"`.
   Successful search, zero hits.
3. `msearch.py ... grep`, query:
   `henselian.*cohomology|cohomology.*completion|Fujiwara`.
   Successful Mathlib search, zero hits.
4. `msearch.py ... leansearch`, query: "Etale cohomology with torsion coefficients
   on the complement of a henselian pair is invariant under completion".
   Eight hits on algebraic adic completion, etale ring maps and base change
   of etale morphisms. Read returned signatures: none states this comparison.
5. `rg` in upstream WeilConjectures and project lean/Sheaf for
   `henselian.{0,50}completion|completion.{0,50}henselian|
   henselian-completion-open-rigidity|adicCompletion.{0,20}cohomology`.
   Five project hits concern henselization regular fibres, Weierstrass cylinders,
   finite-etale lifting, finite-etale completion, or partial algebraization;
   none is this cohomology statement. Searching upstream by the exact blueprint
   id also gives zero hits.
6. Searched `cohomologyMap_bijective` in project and upstream sources and read
   its signature: the existing general comparison theorem assumes a universal
   homeomorphism; the completion projection in this item has no such assumption.
   Henselian closed-fibre comparison also has a different morphism and conclusion.
7. Exact new declaration/module name search in Mathlib, upstream, lean/Sheaf,
   and dag/lean_names_upstream.json gives no existing declaration.

Validation: `scompile.py Q28 lem-per-henselian-completion-open-rigidity` compiled
this one file both as a sandbox module and under its final library module name,
2.8 seconds each, with no errors or warnings. Universes and variables are
explicitly bound and `autoImplicit` is false. There are no new nodes, dependency
repairs, statement corrections, or statement disputes.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
