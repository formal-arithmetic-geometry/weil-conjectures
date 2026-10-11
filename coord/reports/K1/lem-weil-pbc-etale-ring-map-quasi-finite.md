## Worker report

The module `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime` states
`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_etale`, with a single `sorry` proof.
No definition is added and no node statement is changed.

Hypotheses and conclusions, clause by clause:

- The commutative rings are `(R S : Type u) [CommRing R] [CommRing S]`.
  The universe `u` is arbitrary. A common ambient universe imposes no mathematical
  size restriction on the two rings; any two small rings can be viewed in a
  common larger universe.
- The given ring homomorphism is `algebraMap R S`, furnished by `[Algebra R S]`.
  This represents an arbitrary ring map: any `φ : R →+* S` equips `S` with
  `φ.toAlgebra`, whose algebra map is `φ`. No injectivity, nontriviality, flatness,
  Noetherian assumption or separate finite-type hypothesis is added.
- Its induced scheme map is
  `AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))`.
- The hypothesis that this map is étale is the explicit binder
  `h : AlgebraicGeometry.Etale (...)`.
- The conclusion that `S` is finitely generated over `R` is the existential
  witness `∃ hft : Algebra.FiniteType R S`. Mathlib's `Algebra.FiniteType`
  means that the top subalgebra is finitely generated (FiniteType.lean:39).
- The conclusion at every prime is
  `∀ q : PrimeSpectrum S, Algebra.IsQuasiFiniteAtPrime R S q`.
  `PrimeSpectrum S` bundles an ideal and its primeness. `letI := hft` supplies
  the finite-type hypothesis of the recorded definition from the first
  conclusion, rather than assuming it in the theorem.
- The recorded `Algebra.IsQuasiFiniteAtPrime` contracts `q` along the same
  `algebraMap R S`, uses `PrimeSpectrum.preimageHomeomorphFiber` to identify
  the unique corresponding fibre prime, and asks that its singleton be open.
  Its `κ(p) ⊗[R] S` convention agrees with the node's `S ⊗[R] κ(p)` via the
  tensor swap. We reuse this existing definition without replacing it by
  Mathlib's different `Algebra.QuasiFiniteAt` predicate.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme` (imported through the étale module).
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. Its affine-local definition
  and `Etale.iff_flat_and_formallyUnramified` were read.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`:
  `Algebra.IsQuasiFiniteAtPrime`, `Sheaf.RingTheory.QuasiFiniteAtPrime`.
  Its entire definition and docstring were read.

Source checked: https://stacks.math.columbia.edu/tag/00U5, Algebra,
Lemma 10.143.6. The local `literature/stacks-project/algebra.tex` is absent
on this machine; the official tag supplies the statement and proof.
The declaration docstring records all four proof steps of the DAG, with
its dependency names: finite presentation implies finite generation;
base change to the residue field; the finite product of separable fields
and its discrete spectrum; the unique fibre prime has an open singleton.

Edge cases checked before writing:

- `S` may be the zero ring: its spectrum is empty and the universal statement
  over primes is vacuous; the zero algebra is finitely generated.
- `R` may be the zero ring: an `R`-algebra is also trivial, covered as above.
- A residue-field fibre may be empty (the zero ring); no prime `q` contracts
  to that base point, so no nonempty-fibre hypothesis is needed.
- Identity maps and finite separable field extensions have discrete fibres.
  Positive-dimensional bases and non-Noetherian rings are permitted.
- No characteristic or finite-generation-number restriction is present;
  an empty set of algebra generators is allowed by `Algebra.FiniteType`.

Searches for an existing exact statement:

- `msearch.py leansearch`, query "An etale ring map is of finite type and every
  prime is isolated in its fibre": service unavailable (Internal Server Error).
  This is recorded as unavailable, with no verdict attributed to that service.
- `msearch.py leanfinder`, query "An etale ring homomorphism is of finite type
  and quasi-finite at every prime, isolated in its fibre": eight hits, including
  `RingHom.Etale.toAlgebra` and `Algebra.Etale.finitePresentation`; none gives
  both conclusions using the project's isolated-point definition.
- `msearch.py loogle`, query `Algebra.Etale, Algebra.QuasiFiniteAt`: two hits,
  `exists_etale_isIdempotentElem_forall_liesOver_eq` and its auxiliary lemma;
  these construct an étale neighbourhood of a quasi-finite point and do not
  state the item.
- `msearch.py grep`, expression
  `etale.*quasi[Ff]inite|[Qq]uasiFinite.*[Ee]tale`, subdirectory `RingTheory`:
  no hits.
- Local `rg` of `lean/Sheaf` and `WeilConjectures` for `IsQuasiFiniteAtPrime`,
  `etale.*quasi` and `quasi.*etale`: the definition and its applications exist;
  no exact combined theorem. The source's
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`
  has `LocallyQuasiFinite.of_etale`, a different scheme-level formulation.
  The source's `WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite` deals
  with sections of étale algebras over normal domains, not this statement.
- Local `rg` for the full node id under `WeilConjectures`: no hits.
- Local name-collision search for
  `finiteType_and_isQuasiFiniteAtPrime_of_etale`: no existing declaration.
  The node's earlier searches also identify only a route via Mathlib's
  anonymous formally-unramified quasi-finite instance, not an exact match.

Validation: the server `scompile.py K1 lem-weil-pbc-etale-ring-map-quasi-finite`
compiled this single module cleanly in 1.7 seconds, with no warnings.
All variables and the universe are explicitly bound; no scratch `#check`
commands remain. No node faults or disputed statements were found.
The delivery dry run is the final check; the independent second reader
will supply the second-reading section and deliver.

## Second reading by K1

Independently opened the item node, sandbox Lean, all three statement-dependency
nodes and their actual declarations. No mathematical mismatch was found; the
module and node are unchanged. Only this second-reading report was added.

Source: [Stacks 00U5](https://stacks.math.columbia.edu/tag/00U5), and the official
[Algebra TeX](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex),
read at `lemma-etale-quasi-finite`, `section-etale`, and `section-conventions`.
The local literature TeX is absent, so a reference copy was saved in the sandbox
scratchpad. The conventions expressly allow the zero ring, and ring maps need
not be injective. The étale section imposes no standing field, Noetherian or
nontriviality assumption. The proof of 00U5 supplies finite type and finite
residue-field fibres, agreeing with the node's isolated-point conclusion.

Object/hypothesis/conclusion list and matching Lean (H3):

- Objects R and S, commutative unital rings: `(R S : Type u) [CommRing R]
  [CommRing S]`. Exact; neither ring is assumed a domain or nonzero.
- Object, the given ring map R → S: `[Algebra R S]` and `algebraMap R S`.
  Exact: an arbitrary ring homomorphism supplies this structure by
  `RingHom.toAlgebra`; it is not an inclusion or a specially chosen map.
- Object, the contravariant affine scheme morphism Spec S → Spec R:
  `Spec.map (CommRingCat.ofHom (algebraMap R S))`. Exact. Read `Spec` and
  `Spec.map` in Mathlib's Scheme.lean (470 and 479); they are the recorded
  declarations of def-weil-affine-spectrum, with this direction.
- Sole substantive hypothesis, that morphism is étale:
  `h : AlgebraicGeometry.Etale (...)`. Exact. Read its affine-local class
  and `Etale.iff_flat_and_formallyUnramified` in Morphisms/Etale.lean;
  the latter includes locally finite presentation, matching the dependency
  def-weil-etale-morphism. No extra finite-type assumption occurs.
- First conclusion, S finitely generated as an R-algebra:
  `∃ hft : Algebra.FiniteType R S`. Exact. Read the class in FiniteType.lean:
  `(⊤ : Subalgebra R S).FG` is algebra generation, not module finiteness.
- Second conclusion, quasi-finite at every prime ideal q of S:
  `letI := hft; ∀ q : PrimeSpectrum S, Algebra.IsQuasiFiniteAtPrime R S q`.
  Exact. The existential finite-type proof precedes the prime quantifier;
  it installs the required instance rather than adding a hypothesis.
  PrimeSpectrum bundles exactly an ideal with primeness.
- Meaning of that conclusion: read the complete recorded definition in
  Sheaf.RingTheory.QuasiFiniteAtPrime. It sets `p := q.comap (algebraMap R S)`,
  takes `e := PrimeSpectrum.preimageHomeomorphFiber R S p`, and asserts
  `IsOpen ({e ⟨q, rfl⟩} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))`.
  Read Mathlib's `Ideal.Fiber` and the homeomorphism signature in
  LocalRing/ResidueField/Fiber.lean. The latter sends precisely the point q
  over p to its corresponding fibre prime. Its κ(p) ⊗ S order agrees with
  the node's S ⊗ κ(p) by the canonical tensor-swap ring isomorphism and its
  spectrum homeomorphism. No second definition is introduced.

Edge cases: if S is the zero ring, Spec S is empty and the universal prime
clause is vacuous; finite algebra generation still holds. If R is zero, a
unital R-algebra is zero, also covered. An empty residue-field fibre introduces
no phantom prime. Empty generator lists (n = 0), identity maps, every
characteristic and non-Noetherian bases are admitted. There is no nonempty
index set or dimension bound. `u` is explicitly declared and arbitrary;
Mathlib's Spec.map has source and target rings in one ambient universe, so
this common-universe binder follows its recorded affine-spectrum interface.
Cumulativity places any two ring carriers in a common larger universe.
No variable or universe is unbound.

Independent duplicate searches (H4), using different phrases from the worker:

- LeanSearch: "For an etale homomorphism of commutative rings every prime is
  isolated in its fibre and the target algebra is finitely generated".
  Service returned Internal Server Error; recorded as unavailable, with no
  mathematical verdict attributed to it.
- LeanFinder: "An affine etale morphism gives a finitely generated algebra
  with isolated points in each residue field fibre". Eight hits, including
  Algebra.Etale.finitePresentation, RingHom.Etale.toAlgebra and etale-locus
  results; no combined exact statement with the recorded isolated-point notion.
- Loogle: `AlgebraicGeometry.Etale, Algebra.FiniteType`; zero hits.
- Local rg on repository lean/Sheaf, source WeilConjectures and Mathlib's
  RingTheory and AlgebraicGeometry for `IsQuasiFiniteAtPrime`, étale/quasi
  in both orders, and the full new declaration name. The project contains
  the recorded definition and downstream dimension/completion uses, but no
  exact theorem or name collision. Opened the source's
  `LocallyQuasiFinite.of_etale`: it concludes scheme-level locally
  quasi-finiteness, not this node's two-clause ring statement. Mathlib's
  formally-unramified quasi-finite instance and its isolated-point comparison
  are a proof route, as the node already records, not an existing declaration
  of this exact statement. Therefore the module is retained.

H5/H6/H8/H9: there are no new definitions or dependency modules to audit,
no hollow data and no proved auxiliary results. The only proof is the named
item theorem's `sorry`. Both docstrings name Stacks 00U5 and the blueprint id.
The theorem docstring follows all four node proof steps: affine étale implies
finite presentation and finite generation; residue-field base change remains
étale; a finite product of separable fields has discrete spectrum (tensor swap
included); the corresponding fibre prime has an open singleton. Both imports
are used. Namespace Algebra and the topic path are appropriate, and all lines
are at most 100 characters. The stored lean.statement was checked byte for
byte against the signature preceding `:= by`. The node differs from the base
only in lean; no statement correction or citer recheck is necessary.

Independent validation: scompile.py compiled the unchanged module on the server
in 1.7 seconds, exit code 0, without errors or warnings.
