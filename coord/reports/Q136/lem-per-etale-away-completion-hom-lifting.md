## Worker report

The module `Sheaf.RingTheory.EtaleAwayCompletionHomLifting` states
`RingTheory.existsUnique_algHom_lift_of_etale_away_completion`, with one `sorry`
and no new definitions. The node is unchanged except for `lean`.

Read the node, every statement dependency's statement and recorded signature and
source docstring, the recorded proof interfaces, and Stacks `restricted.tex`,
`lemma-fully-faithful-etale-over-complement` (Tag 0AKJ). The source maps into the
pair henselization of C. The node is its valid henselian-target specialization,
where that henselization is canonically C. No correction or disputed statement.

Hypothesis and conclusion correspondence:

- A commutative Noetherian ring: `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`.
- I an ideal: `(I : Ideal A)`; no propriety or nonzero assumption.
- D a commutative A-algebra: `(D : Type u) [CommRing D] [Algebra A D]`.
- D finite type over A: `hD : (algebraMap A D).FiniteType`, using the
  dependency's recorded `RingHom.FiniteType`.
- Spec D -> Spec A is the actual structural map
  `Spec.map (CommRingCat.ofHom (algebraMap A D))`.
- Etaleness over Spec A minus V(I): `hEtale` is `Etale` of
  `morphismRestrict` of that map to the open with underlying set
  `(PrimeSpectrum.zeroLocus (I : Set A))ᶜ`. The proof of openness is
  `PrimeSpectrum.isClosed_zeroLocus ... |>.isOpen_compl`; it is intrinsic
  to this existing open, not an additional mathematical assumption.
- C a commutative Noetherian A-algebra: `(C : Type v) [CommRing C]
  [Algebra A C] [IsNoetherianRing C]`. C is not required finite type,
  finite, etale, local, or already complete.
- (C,IC) henselian: `[HenselianRing C (I.map (algebraMap A C))]`.
  This is the recorded equivalent root-lifting formulation of henselian pairs.
- The two completions: `AdicCompletion (I.map (algebraMap A D)) D`
  and `AdicCompletion (I.map (algebraMap A C)) C`. For each extended
  ideal J, Mathlib uses D/(J^n • top), which equals D/J^n; and
  `(I.map (algebraMap A D))^n = (I^n).map (algebraMap A D)`.
  Thus these are exactly the displayed limits D/I^nD and C/I^nC.
- Every A-algebra map between them: the arbitrary binder `φ : ... →ₐ[A] ...`.
  No continuity hypothesis is added: it follows from preservation of powers
  of the finitely generated ideal as explained in the node and docstring.
- Existence and uniqueness of u: `∃! u : D →ₐ[A] C, ...`.
- The required compatibility: `∀ d : D, algebraMap C (AdicCompletion ... C)
  (u d) = φ (algebraMap D (AdicCompletion ... D) d)`. The two algebra maps
  are exactly the canonical completion maps. This is the node's explicitly
  equivalent formulation `iota_C u = φ iota_D`, written pointwise.
- Equality of the completed u with φ is encoded by that equivalent condition:
  an A-algebra map preserves I^n, and projections of the completion have
  kernel I^n times the completion (finite generation of I). For x and n,
  choose d representing x at level n; φ(x) and completed-u(x) both have
  nth coordinate u(d) modulo I^nC. Separatedness of the inverse limit then
  gives equality. No independent arbitrary comparison map is introduced.

Statement dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.
- `Mathlib.AlgebraicGeometry.Scheme` (publicly available through the geometry
  imports): `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  `Mathlib.AlgebraicGeometry.Restrict`: `AlgebraicGeometry.morphismRestrict`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded henselian
  terminology module, publicly exposing Mathlib's `HenselianRing`.
- `Mathlib.RingTheory.AdicCompletion.Algebra`: `AdicCompletion` and its real
  ring/algebra instances and canonical `algebraMap` (the module publicly
  imports the dependency's `Mathlib.RingTheory.AdicCompletion.Basic`).

All available proof dependencies are imported: completeness
(`AdicCompletion.isAdicComplete`, `pow_smul_top_eq_ker_eval`), finite-type
Noetherianity (`Algebra.FiniteType.isNoetherianRing`, already in the statement
import), etale base change and composition (already in the etale import),
`WeilConjectures.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods`
(`etale_on_open_of_etale_infinitesimal_neighbourhoods`),
`WeilConjectures.RingTheory.HenselizationStageMap`
(`RingTheory.existsUnique_henselization_stage_map`), complete implies
henselian (`IsAdicComplete.henselianRing`, already public),
`WeilConjectures.RingTheory.HenselianFactorizationCriterion`
(`henselianRing_iff_factorization_criterion`), and
`Mathlib.RingTheory.Filtration`
(`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`).
The two proof-only nodes `lem-per-completed-retraction-conormal-torsion` and
`lem-per-conormal-torsion-algebraization` currently have no recorded Lean
interface; no import is invented for them. Their future proof use is included
in the seven-step theorem docstring. They are not needed to type this statement.

Edge cases checked before writing:

- I=0: completions are the original rings, so u is precisely φ, irrespective
  of the vacuous etale condition on the empty complement.
- I=A: henselianity forces C to be the zero ring since IC is the unit ideal
  contained in the Jacobson radical. The maps to C and its completion are unique.
- Zero C: all target maps exist uniquely, with no `Nontrivial` hypothesis.
- Zero D: if a map φ to the target completion exists, separatedness of the
  Noetherian henselian C forces C=0. The conditional theorem is correct.
- Nilpotent I: the complement is empty and completions are the original
  algebras, so the assertion reduces to the given map.
- No constraint on characteristic, connectedness, or nonempty spectrum.
- The affine source and base use a common ambient universe u, as required
  by Mathlib's category of schemes. Every pair of rings fits in a common
  ambient universe; the target uses independent v. No small test-object
  quantification or size-bound restriction occurs.

Searches made with the prescribed `msearch.py Q136 <item>` wrapper:

- LeanFinder: "Algebra maps between adic completions of finite type algebras
  etale away from ideal lift uniquely into Noetherian henselian target".
  Eight hits: `IsAdicComplete.liftAlgHom`, formally smooth quotient lifts,
  complete implies henselian, and ordinary standard-etale lifting. None is
  the requested algebraization theorem.
- Loogle: "AdicCompletion.mapAlgHom, HenselianRing". Zero hits; Loogle
  reports unknown identifier `AdicCompletion.mapAlgHom`.
- LeanSearch: "A homomorphism of adic completions of a finite type algebra
  etale outside V I uniquely lifts to a Noetherian henselian target".
  Eight hits: completion extensionality and lifts of compatible quotient
  maps. None algebraizes into a henselian noncomplete ring.
- Mathlib grep: `etale.*completion|completion.*henselian` in RingTheory.
  Zero hits. Directly inspected the completion Algebra and Functoriality APIs.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the same patterns,
  for `completion.*hom|Completion.*[Ll]ift|etale.*[Aa]way|[Aa]way.*[Ee]tale`,
  and for this node id. Related completion constructions and strict
  henselization results exist, but no matching statement.
- Exact proposed declaration-name search in `dag/lean_names_upstream.json`,
  Mathlib, WeilConjectures, and Sheaf: no existing declaration.

Validation: the delivered module compiled in both wrapper sandbox and library
contexts using `scompile.py`, in 1.9 and 1.7 seconds, with no errors or warnings.
Every universe and variable is explicitly bound. There are no helper definitions,
private declarations, local notation, or proofs other than the requested `sorry`.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
