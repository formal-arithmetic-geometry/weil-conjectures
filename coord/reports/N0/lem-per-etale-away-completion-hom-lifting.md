## Worker report

The module `Sheaf.RingTheory.EtaleAwayCompletionHomLifting` states
`AdicCompletion.existsUnique_algHom_of_etale_away_completion`, with one `sorry` and no new
definition. It states precisely the node's equivalent restriction formulation. There are
no changes to the mathematical statement, dependencies, proof, or other node fields.
No repair note for this item was present.

Hypothesis and clause correspondence:

- A commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- An ideal of A: `(I : Ideal A)`.
- A commutative A-algebra D: `(D : Type u) [CommRing D] [Algebra A D]`.
- Finite type of D over A: `hD : RingHom.FiniteType (algebraMap A D)`, using the
  dependency's exact recorded predicate. This is equivalent to `Algebra.FiniteType A D`.
- The scheme map Spec D to Spec A: `Spec.map (CommRingCat.ofHom (algebraMap A D))`.
- Its etaleness over Spec A minus V(I): `hetale : Etale (... ∣_ U)`, where
  `U = ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
  (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩`. The notation here in
  the report abbreviates the explicit open in the file; no file-local notation or
  auxiliary predicate is introduced. Morphism restriction restricts both target and
  source to this open and its inverse image, exactly as required.
- C commutative, Noetherian and an A-algebra:
  `(C : Type v) [CommRing C] [Algebra A C] [IsNoetherianRing C]`.
- The henselian pair `(C,IC)`:
  `[HenselianRing C (I.map (algebraMap A C))]`. This uses the recorded terminology,
  not a completeness, locality, or finiteness assumption on C.
- The completion of D: `AdicCompletion (I.map (algebraMap A D)) D`.
- The completion of C: `AdicCompletion (I.map (algebraMap A C)) C`.
  Powers of the extended ideal are exactly I^n D and I^n C. Both types have Mathlib's
  ring and A-algebra structures, with componentwise operations on compatible sequences.
- Every A-algebra homomorphism of these completions is the parameter `φ : ... →ₐ[A] ...`.
  No extra continuity assumption is imposed.
- A unique A-algebra homomorphism D to C is `∃! f : D →ₐ[A] C, ...`.
- Its required compatibility is the equation quantified by `∀ d : D`:
  `algebraMap C Ĉ (f d) = φ (algebraMap D D̂ d)`, where Ĉ and D̂ in this report stand
  for the explicit completion types in the file. Both completion maps are the canonical
  Mathlib algebra maps, not unspecified maps.
- This renders the node's explicitly equivalent formulation. For completeness, why it
  says that the completion of f equals φ: A is Noetherian, so I is finitely generated;
  completion modulo I^n is D/I^nD or C/I^nC with kernel I^n times the completion. An
  A-algebra map preserves these powers. Given x in D̂, choose d_n representing its
  n-th coordinate. Then x minus the image of d_n is in I^n D̂. The equation determines
  the n-th coordinate of φ(x) as f(d_n) modulo I^nC, which is precisely the inverse-limit
  completion of f. Equality of all coordinates is equality in Ĉ. Conversely, evaluating
  a completed f on d gives the equation. Thus no whole-completion equality is lost by
  using the stated restriction formulation, and no separate canonical-map helper is needed.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, whose docstring says every
  ideal is finitely generated, and `isNoetherianRing_iff`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and `Algebra.FiniteType`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`, exposed
  through the public import of `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` and restriction.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded terminology import;
  it publicly imports Mathlib's `HenselianRing`, which is the pair predicate used here.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, its ring
  and algebra instances, and the canonical `algebraMap`. The Basic module is exposed
  by the public Algebra import.

Proof-only imports reflect the stated proof plan: `.AdicCompletion.Completeness`
(`AdicCompletion.isAdicComplete`, the evaluation kernels), `.FiniteType` (already public),
`.Morphisms.Etale` (already public; base change and composition), `.Filtration`
(`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`),
`Sheaf.RingTheory.ConormalTorsionAlgebraization`
(`AdicCompletion.exists_finiteType_algebraization_of_conormal_torsion`),
`Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods`
(`AlgebraicGeometry.etale_on_open_of_etale_infinitesimal_neighbourhoods`),
`Sheaf.RingTheory.HenselizationStageMap`
(`RingTheory.existsUnique_henselization_stage_map`),
`Sheaf.RingTheory.HenselianFactorizationCriterion`
(`henselianRing_iff_factorization_criterion`), and the already public Mathlib henselian
import (`IsAdicComplete.henselianRing`). The proof dependency
`lem-per-completed-retraction-conormal-torsion` had no recorded declaration/module;
it is retained in the node and explicitly named in the proof docstring, with no invented
import. It is a proof dependency, not a missing notion needed to state this item.

Source checked: `literature/stacks-project/restricted.tex`, the complete statement and
proof of `lemma-fully-faithful-etale-over-complement` (Tag 0AKJ), beginning at line 1848.
The source allows any finite type source and Noetherian target. Its conclusion uses the
pair henselization of C; under the node's henselian assumption that target is C itself.
The theorem docstring records all seven proof steps, including retaining E-linearity
in algebraization and using a localization at g congruent to 1 modulo the ideal.

Edge cases checked before writing:

- I = 0: both completions identify canonically with their rings. The complement of V(0)
  is empty, so etaleness imposes no condition; each map is its own unique lift.
- I = top: henselianity of (C,C) forces C to be the zero ring by the Jacobson condition.
  The unique map into that ring satisfies the conclusion.
- Zero rings and empty spectra are allowed: there is no `Nontrivial`, locality, faithful
  flatness, or nonempty-open hypothesis. If D is zero, existence of φ and separatedness
  of the Noetherian henselian target force the compatible zero-target case.
- C need not be finite type or finite over A, and D need not be finite or globally etale.
  The binders impose none of those restrictions. Positive-characteristic cases are included.
- A and D are in an arbitrary common universe, as required to form a scheme morphism.
  Any pair can be placed in a common larger universe. C has the independent universe v;
  there is no universe-sensitive quantification over test algebras that could be vacuous.

Searches for an exact existing statement (2026-10-18 UTC):

- `msearch.py ... leanfinder "Every homomorphism of adic completions from a finite type
  algebra etale away from an ideal lifts uniquely to a henselian target"`: eight hits,
  including `IsAdicComplete.henselianRing`, formally smooth lifting into complete targets,
  `AdicCompletion.liftAlgHom` and `IsAdicComplete.liftAlgHom`. None states algebraization
  of a given completed map into a henselian, potentially incomplete, target.
- `msearch.py ... loogle "AdicCompletion, AlgHom"`: twelve hits; quotient evaluations,
  `kerProj`, `liftAlgHom`, and the complete-ring equivalence. No exact match.
- `msearch.py ... grep "henselian|existsUnique" RingTheory/AdicCompletion`: zero hits.
- `msearch.py ... leansearch "Algebra homomorphisms from completions of algebras etale
  outside an ideal uniquely lift into henselian rings"`: eight hits, mostly complete
  target lifting/extensionality. No exact match.
- `rg` for `etale.*(away|complement)|completion.*(hom|lift)` in the upstream project and
  `lean/Sheaf`: the related Elkik equivalence has this node only as a proof input;
  formal-scheme completion maps and formally smooth complete-target results differ.
- `grep -rn "lem-per-etale-away-completion-hom-lifting"` in the upstream project:
  no declaration. `rg` of `dag/lean_names_upstream.json` and the RingTheory trees for
  `existsUnique.*(adic|hensel|completion)|completion.*(hensel|etale)` found henselization
  stages, etale local targets, and completion comparisons, none equal to this statement.
- Exact-name `rg` over Mathlib, upstream WeilConjectures, and `lean/Sheaf` found no
  existing `existsUnique_algHom_of_etale_away_completion` declaration.

Validation: `scompile.py N0 lem-per-etale-away-completion-hom-lifting <file>` passed both
its sandbox and library module checks (1.9 s and 2.3 s), with no errors or warnings.

## Second reading by N0

The dispatcher brief prohibits starting another agent; this section records a separate
self-check, not an independent-worker review. The maintainer's independent reading remains
part of the prescribed delivery workflow. Reopened the node and Lean file and matched:
Noetherian A; ideal I; commutative finite type A-algebra D; actual spectrum restriction
etale off V(I); commutative Noetherian A-algebra C; henselian pair (C,IC); the two canonical
completions; arbitrary A-algebra φ; and existence and uniqueness of f with the exact
canonical restriction equation. All clauses agree. The full-completion equality follows
from the coordinate argument above, precisely the equivalence already asserted by the
node; no statement correction is needed. There are no additional assumptions of finite
C, finite D, global etaleness, completeness of C, or nonzero rings. Every variable and
universe is explicitly bound, the sole theorem has `sorry`, and no definition or auxiliary
postponed theorem was introduced. No mismatch was found or silently corrected.

Delivery-tool failure: the first prescribed `deliver2.py ... --no-push` invocation
compiled the file, then crashed in `sharedrepo.fetch` with
`subprocess.TimeoutExpired: Command '['git', 'fetch', '-q', 'origin']' timed out after 600 seconds`.
A second identical dry run was attempted and remained waiting for the shared fetch for
over thirteen minutes without reaching preflight. Only this task's waiting dry-run
process was stopped. No launcher file, lock, shared checkout, or other task's process
was modified. The completed, compiling statement and node remain in this sandbox;
no delivery commit was pushed and no preflight success is claimed.


## Resumed delivery validation (2026-10-19 UTC)

The prescribed first retry of the saved packet passed: `deliver2.py N0
lem-per-etale-away-completion-hom-lifting --no-push` printed
`OK (dry run): commit 1a9d1bd042 passes the preflight and compiles; nothing pushed`.
The earlier fetch failure is resolved. Retained the Lean module and node record unchanged.
Compared the saved node to the current shared node: only `lean` differs. Reopened the
statement, its seven proof steps, the Lean module, all six statement-dependency records,
and their recorded declaration signatures/docstrings in the current local sources.
Checked Stacks 0AKJ again: specializing its henselization target to the henselian C gives
exactly the displayed unique restriction lift. The six hypotheses and the canonical-map
compatibility match as detailed above; no new mismatch or correction was found. The
independent universe for C and the zero/unit-ideal edge cases remain valid. No repair note
exists for this item. The required second reading is the explicit self-check above, under
the dispatcher's prohibition on starting other agents.
