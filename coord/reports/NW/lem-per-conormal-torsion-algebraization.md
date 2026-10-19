## Worker report

The module Sheaf.RingTheory.ConormalTorsionAlgebraization states
AdicCompletion.exists_finiteType_algebraization_of_conormal_torsion, with its only
proof `sorry`. No definitions, new nodes, dependency repairs, or statement corrections
are needed. The source is Stacks Project, More on Algebra, Tag 0ALR,
lemma-quotient-by-idempotent; I read its statement and entire proof in the local source.
The theorem docstring gives all nine steps of the node's proof.

Clause-by-clause correspondence:

- A Noetherian commutative ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- An ideal of A: `(I : Ideal A)`; it need not be proper or nonzero.
- A finite type A-algebra B: `(B : Type v) [CommRing B] [Algebra A B]`
  and `(hB : RingHom.FiniteType (algebraMap A B))`. The latter uses precisely
  the dependency's recorded RingHom.FiniteType, equivalent to Algebra.FiniteType
  for this algebra map by RingHom.finiteType_algebraMap.
- The I-adic completion of B: `AdicCompletion (I.map (algebraMap A B)) B`.
  The ideal is extended to B, and the ring and A-algebra structures are Mathlib's
  canonical structures from AdicCompletion.Algebra.
- The surjection to C: `(C : Type w) [CommRing C] [Algebra A C]`,
  `(f : AdicCompletion (I.map (algebraMap A B)) B →ₐ[A] C)` and
  `(hf : Function.Surjective f)`. Its A-linearity specifies the induced A-algebra
  structure on C: every bare ring surjection in the source has exactly that
  induced structure. No B-algebra structure on C is separately assumed.
- The kernel J: `RingHom.ker f.toRingHom`, rather than a separately chosen ideal.
- J/J² as a module over the completed ring: `(RingHom.ker f.toRingHom).Cotangent`.
  Mathlib Ideal.Cotangent is literally the quotient of J by the submodule J • top;
  its toCotangent kernel maps to J², as Ideal.map_toCotangent_ker states.
- Some c ≥ 0: `∃ c : ℕ`, including c = 0.
- Multiplication by every element of the extended ideal I^c kills every conormal
  class: `∀ r ∈ (I ^ c).map (algebraMap A (AdicCompletion ... B)),
  ∀ x : (RingHom.ker f.toRingHom).Cotangent, r • x = 0`.
  Both ideal extension and scalar action are over the completion, not over C.
- A finite type A-algebra algebraizing C: existential `D`, `CommRing D`,
  `Algebra A D`, and `RingHom.FiniteType (algebraMap A D)`.
- Its I-adic completion is A-algebra isomorphic to C:
  `Nonempty (AdicCompletion (I.map (algebraMap A D)) D ≃ₐ[A] C)`.
  Nonempty here expresses existence of an actual algebra equivalence, not a
  construction of data from a postponed existence theorem.

Universes u, v, w are explicit and independent. D is in Type (max u v), a universe
large enough for a quotient of a polynomial A-algebra and all finite constructions
starting from B. There is no equality requirement on the universes of A, B, and C.
All variables are explicitly bound; autoImplicit is disabled.

Dependency declarations inspected and used:

- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing, exactly all ideals finitely
  generated, as recorded by def-weil-pbc-noetherian-ring.
- Mathlib.RingTheory.AdicCompletion.Basic: AdicCompletion, the compatible sequences
  of quotients, as recorded by def-weil-pbc-adic-completion.
  Mathlib.RingTheory.AdicCompletion.Algebra supplies the ring and A-algebra structures.
- Mathlib.RingTheory.FiniteType: RingHom.FiniteType, as recorded by
  def-weil-pbc-finite-type-algebra; its full signature and docstring were read.
- Mathlib.RingTheory.Ideal.Cotangent: Ideal.Cotangent, the existing module J/J².

The already recorded proof modules are imported without public export:
FormalGlueingData, the upstream Henselian module, AdicCompletionNoetherian,
Mathlib Henselian, FiniteModuleComplete, BijectiveQuotientMapPowOfFlat,
LiftIdempotentUpstairs, and Mathlib's etale morphism module.
Other proof prerequisites lacking a recorded Lean module are left to later stages;
none is needed to type the statement.

Edge cases checked mathematically:

- c = 0 means the whole completed ring annihilates J/J², hence J = J²;
  the proof handles its finitely generated idempotent kernel.
- I = 0 gives B completed = B; every quotient is already a finite type A-algebra.
- I = top gives zero completion and forces the surjective target C to be zero.
- J = 0 gives the completion of B itself; f is the desired equivalence.
- C = 0, the zero base ring, and a zero product factor are admitted: no Nontrivial
  instance appears. Empty generator lists are also allowed.

Existing-declaration searches were run before writing:

- msearch.py leanfinder, query `A quotient of an adic completion with conormal module annihilated by a power of the ideal is the completion of a finite type algebra`: 8 hits; top names AdicCompletion.mk_smul_top_ofAlgEquiv_symm, AdicCompletion.factor_evalₐ_eq_eval, AdicCompletion.factor_eval_eq_evalₐ, AdicCompletion.subalgebra, AdicCompletion.instAlgebra, Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete, AdicCompletion.exists_smodEq_pow_smul_top_and_mkQ_eq, AdicCompletion.of_apply. No exact algebraization theorem.
- msearch.py loogle, query `"AdicCompletion", "FiniteType"`: 0 hits; top names . No exact algebraization theorem.
- msearch.py grep, query `algebraiz|algebrais|conormal`: 25 hits; top names Mathlib/RingTheory/Spectrum/Prime/Topology.lean, Mathlib/RingTheory/Spectrum/Prime/Topology.lean, Mathlib/RingTheory/Spectrum/Prime/Topology.lean, Mathlib/RingTheory/Finiteness/Ideal.lean, Mathlib/RingTheory/Finiteness/Basic.lean, Mathlib/RingTheory/Finiteness/Basic.lean, Mathlib/RingTheory/Finiteness/ModuleFinitePresentation.lean, Mathlib/RingTheory/EssentialFiniteness.lean. No exact algebraization theorem.
- msearch.py leansearch, query `A quotient of an adic completion whose conormal module is killed by a power of the ideal is algebraizable`: 8 hits; top names AdicCompletion.module, AdicCompletion.of_ofAlgEquiv_symm, AdicCompletion.ofAlgEquiv, AdicCompletion.instAlgebra, AdicCompletion, AdicCompletion.mkₐ, AdicCompletion.ofAlgEquiv_apply, Algebra.FormallySmooth.exists_kerProj_comp_eq_id. No exact algebraization theorem.

Direct rg searches of Mathlib, WeilConjectures, lean/Sheaf and
 dag/lean_names_upstream.json for the chosen declaration name,
quotient_by_idempotent, and conormal_torsion_algebraization found no existing theorem.
Broader algebraiz/algebrais/conormal searches found completion APIs, smooth lifting,
and geometric conormal material, but no theorem with this hypothesis and conclusion.
The upstream grep for the exact item id was empty. None of the semantic search hits
produces a finite type algebraization of this quotient; ofAlgEquiv only identifies
an already complete ring with its own completion, and smooth lifting imposes a
formally smooth hypothesis absent here.

Validation: the delivery module compiled cleanly through the prescribed scompile.py
wrapper with both the sandbox and library module names. The only postponed theorem
is the named theorem above. No statement dispute or node fault was found.

## Second reading by NW

No second reading by a worker: the dispatched brief requires direct delivery and
reserves the independent review for the maintainer. The clause correspondence and
edge-case checks above are the author's self-check, not an independent review.
