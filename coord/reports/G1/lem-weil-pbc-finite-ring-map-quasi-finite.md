## Worker report

The module `lean/Sheaf/RingTheory/FiniteRingMapQuasiFinite.lean` states
`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite`, with only `sorry` as its proof.
It states the unchanged node, using the already landed isolated-fibre-point definition.
No new nodes, dependency modules, or statement correction are needed.

Hypothesis and clause correspondence:

- Commutative rings R and T: `(R : Type u) (T : Type v) [CommRing R] [CommRing T]`.
  Independent explicitly declared universes impose no equality of carrier universes.
- The homomorphism φ : R → T: `[Algebra R T]`, whose map is `algebraMap R T`.
  Every commutative ring homomorphism supplies this algebra structure via `φ.toAlgebra`;
  thus this presentation does not assume injectivity, surjectivity, or any extra structure.
- T is finitely generated as an R-module through this map: `[Module.Finite R T]`.
  Its scalar action is the action of the same algebra structure.
- The map is of finite type: `∃ hft : Algebra.FiniteType R T, ...`.
  This is a conclusion, not an additional finite-type assumption. The local `letI := hft`
  binds the finite-type instance required by the existing definition in the next clause.
- Quasi-finite at every prime q of T: `∀ q : PrimeSpectrum T,
  IsQuasiFiniteAtPrime R T q`. A point of `PrimeSpectrum T` is a proper prime ideal.
  The recorded predicate literally says the corresponding point of the residue-field
  fibre has an open singleton; it is not replaced by Mathlib's localization predicate.
  The existential conclusion expresses both clauses since the finite-type witness is
  a proposition and all witnesses are proof-irrelevant.

Dependency declarations read and used:

- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, whose full defining field is
  `fg_top : (⊤ : Submodule R M).FG` (node `def-weil-finitely-generated-module`).
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, with field
  `out : (⊤ : Subalgebra R A).FG` (node `def-weil-pbc-finite-type-algebra`).
- `Sheaf.RingTheory.QuasiFiniteAtPrime`: `Algebra.IsQuasiFiniteAtPrime`, with R, S,
  commutative-ring and algebra instances, finite-type instance, and a prime-spectrum
  point as arguments (node `def-weil-pbc-ring-map-quasi-finite-at-prime`). Its body
  uses `PrimeSpectrum.preimageHomeomorphFiber R S p` for `p = q.comap (algebraMap R S)`
  and `IsOpen` of the singleton image of `⟨q, rfl⟩`. The fibre is κ(p) ⊗[R] S,
  canonically the tensor swap of the node's S ⊗[R] κ(p).

The sole import is the last module, which already imports both Mathlib modules above.
The theorem docstring records all four node proof steps and every non-elementary input.
The proofs of these inputs are not imported: stage 2 states the theorem only.

Edge cases checked before writing: T may be the zero ring (the empty list generates
it, finite type holds, and there are no primes, so the universal clause is vacuous).
R may be the zero ring, in which case a unital map forces T to be zero too. A nonzero
T may have empty fibres over some primes of R; those fibres introduce no q and cause
no extra requirement. No domain, local, Noetherian, reduced, nontrivial, characteristic,
or injectivity assumption is present. The identity algebra and finite quotients have
finite discrete fibres, as required. Different universes for the rings are allowed.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch "finite algebra quasi finite isolated point fibre"`:
  unavailable, Internal Server Error; no verdict from this service.
- `msearch.py ... leanfinder "A finite ring map is of finite type and every prime is
  an isolated point in its residue field fibre"`: eight hits, including
  `Algebra.quasiFinite_iff`, `Algebra.QuasiFinite.finite_fiber`, and
  `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton`; none is the conjunction
  with the recorded isolated-point predicate.
- `msearch.py ... loogle "Algebra.QuasiFiniteAt, Module.Finite"`: two hits,
  `Algebra.instFiniteResidueFieldOfQuasiFiniteAt` and an étale-neighbourhood theorem;
  neither states this node.
- `msearch.py ... grep "of_finite|finiteType|isOpen_singleton"
  RingTheory/QuasiFinite`: five hits, finite fibres and finite-fibre characterizations.
  Direct Mathlib source reading found `RingHom.QuasiFinite.of_finite` and
  `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`, but these require comparison
  with the landed definition; they do not state this node's literal conclusion.
- `rg` on `WeilConjectures` for `IsQuasiFiniteAt|QuasiFiniteAt|quasiFiniteAt`:
  scheme-level and localization-based lemmas only. The prescribed node-id `grep -rn`
  had no hit. `rg` on `lean/Sheaf/RingTheory` found the recorded definition and the
  similar étale-map theorem, not the finite-map theorem. The latter was read as an
  example of binding the finite-type witness in the conclusion.
- Name search for `finiteType_and_isQuasiFiniteAtPrime_of_finite` in
  `dag/lean_names_upstream.json`, `lean/Sheaf`, and the slopmaster2 source checkout:
  no hit before writing; the new declaration name is unused.

Source checks: this machine has no `literature/stacks-project/algebra.tex` copy.
Opened the official Stacks pages [00PM](https://stacks.math.columbia.edu/tag/00PM)
and [0H8X](https://stacks.math.columbia.edu/tag/0H8X): finite fibres of a finite-type
map give quasi-finiteness at every prime, exactly the implication used by the node.
The finite-module hypothesis supplies both finite type and finite residue-field fibres.
No node fault or STATEMENT-DISPUTED concern was found.

Validation: server single-file compilation and delivery dry run are recorded below.
The second reading is intentionally left to the independent second worker.


## Second reading by G1

Read independently the item node and delivered Lean, all three statement-dependency
nodes, their recorded declarations and defining fields, and the landed
`Sheaf.RingTheory.QuasiFiniteAtPrime` module. There are no new definition nodes,
dependency modules, or statement corrections in this delivery.

Objects, hypotheses and conclusion clauses of the node, matched in order:

1. Arbitrary commutative rings R and T: `(R : Type u) (T : Type v)` with
   `[CommRing R] [CommRing T]`. Verdict: exact; u and v are explicitly bound
   independent universes, with no nontriviality, field, domain or Noetherian assumption.
2. A homomorphism φ : R → T: `[Algebra R T]`, with φ = `algebraMap R T`.
   Verdict: exact. A unital commutative-ring map induces this algebra structure by
   `RingHom.toAlgebra`; its scalar action is the same action used below. No faithfulness,
   injectivity or surjectivity has been added.
3. T is finitely generated as an R-module via φ: `[Module.Finite R T]`.
   Verdict: exact. Opened `Mathlib.RingTheory.Finiteness.Defs`; the defining field
   `fg_top : (⊤ : Submodule R M).FG` is the recorded dependency's notion, not
   finiteness of the underlying set.
4. First conclusion, finite type: `∃ hft : Algebra.FiniteType R T, ...`.
   Verdict: exact. Opened `Mathlib.RingTheory.FiniteType`; its defining field
   `out : (⊤ : Subalgebra R A).FG` expresses the finite algebra generators of the
   node. The witness is a conclusion, not a finite-type hypothesis. `letI := hft`
   supplies the instance required by the landed predicate. Existential quantification
   over this proposition followed by the second clause gives both conclusions;
   proof irrelevance removes any dependence on the choice of finite-type proof.
5. Second conclusion, quasi-finite at every prime q of T:
   `∀ q : PrimeSpectrum T, IsQuasiFiniteAtPrime R T q`.
   Verdict: exact. Opened the dependency definition: it forms
   `p := q.comap (algebraMap R T)`, then `e :=
   PrimeSpectrum.preimageHomeomorphFiber R T p`, and asserts the singleton of
   `e ⟨q, rfl⟩` is open in `PrimeSpectrum (p.asIdeal.Fiber T)`.
   Opened Mathlib's `preimageEquivFiber` and `preimageHomeomorphFiber`: the inverse
   is contraction along `Algebra.TensorProduct.includeRight`, so this is precisely
   the fibre prime whose contraction is q. The fibre is κ(p) ⊗[R] T, canonically
   isomorphic by tensor swap to the node's T ⊗[R] κ(p). Openness is preserved by
   the induced spectrum homeomorphism. There is no localization-based substitute
   for the node's isolated-point conclusion and no change of quantifier order.

Source check: no local Stacks .tex checkout is present. Read the actual official
`algebra.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
labels `lemma-isolated-point-fibre` (00PK), `definition-quasi-finite` (00PL),
`lemma-quasi-finite-above-p` (0H8X), `lemma-quasi-finite` (00PM), and the proof
of `lemma-quasi-finite-open` (00QA). The first two define isolatedness for a
finite-type map; 0H8X equates it at all primes over p with the fibre being finite
as a κ(p)-algebra; 00PM applies that criterion to all p. The 00QA proof explicitly
uses finite over R implies quasi-finite over R. No local, Noetherian, reduced,
characteristic or nonzero-ring hypothesis occurs in this application. Finite
module generators supply finite type and generate every residue-field fibre.

Edge cases: T = 0 is allowed, with finite type and the universal prime clause
vacuous. R = 0 forces T = 0 for a unital map, also covered. Empty fibre spectra
cause no extra demand. The empty generating list (n = 0) is permitted by FG,
including nonzero surjective images of R as well as the zero ring. No finite
index set, scheme, characteristic, or bound on n is imposed. Independent u and v
cover all ring-carrier universes; the tensor fibre uses their maximum universe.
Identity maps and finite quotients satisfy exactly the same statement.

Independent searches (2026-10-11), using different queries from the worker:

- LeanSearch via `msearch.py`: `finite module algebra isolated prime in every fibre`.
  Service unavailable (Internal Server Error); no mathematical verdict inferred.
- LeanFinder via `msearch.py`: `module finite algebra spectrum residue field fibre
  discrete quasi finite`. Eight hits, including `Algebra.quasiFinite_iff`,
  `Algebra.QuasiFinite.finite_fiber`, and
  `Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton`; no exact conjunction
  with the recorded `IsQuasiFiniteAtPrime` conclusion.
- Loogle via `msearch.py`: `Module.Finite, Algebra.FiniteType`. Eleven hits,
  notably `Module.Finite.finiteType` and the integral/finite-type characterization
  of finite algebras. The first gives only the first clause, not this statement.
- Direct rg over the complete `WeilConjectures` source, repository `lean/Sheaf`,
  `dag/lean_names_upstream.json`, and Mathlib's QuasiFinite and RingHom/QuasiFinite
  files, for `IsQuasiFiniteAtPrime`, the proposed theorem name, finite/quasiFinite
  combinations, `QuasiFinite.of_finite`, and `isDiscrete_comap_preimage_singleton`.
  No duplicate declaration found. Read `RingHom.QuasiFinite.of_finite` and
  `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber` in their source files: they
  use Mathlib's fibre-finiteness/localization predicates or a singleton in the
  fibre subspace, requiring the homeomorphism comparison to the landed predicate.
  They are ingredients, not a declaration stating the item's whole conclusion.

H5/H6/H8/H9: no definition or hollow data introduced; the sole theorem has exactly
`by sorry` as proof. Its docstring includes all four node proof steps and their
cited inputs; module and declaration docstrings name the source and blueprint id.
The sole import supplies the actual predicate and both finiteness notions.
No unbound variable or universe is present; namespace, topic, header and line
length follow the example. Checked by Python that `lean.statement` is verbatim
identical to the file signature and every line is at most 100 characters.

Mismatches found: none. Changes: appended this independent reading and search
record only; kept the correct Lean and node untouched. Compilation and delivery
checks follow below.

Second-reader validation: `scompile.py` compiled the delivered module on the server
in 1.3 seconds, exit 0, with no warnings. `deliver2.py --no-push` printed
`OK (dry run): commit f9b777948 passes the preflight and compiles; nothing pushed`.
