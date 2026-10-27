## Worker report

The module `Sheaf.RepresentationTheory.CochainClosedRectangleCertificates` states
`ContinuousCohomology.exists_cochain_closed_rectangle_certificates`, with proof
`sorry`. It introduces no definitions, extra nodes, or dependency modules. The
item's statement, dependencies, proof plan, and other metadata are unchanged;
only its `lean` record is added. The blueprint paragraph (3) was read in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`.
It gives the direct-image application, not this scalar analytic input. The module
and theorem docstrings explicitly preserve that distinction. The existing node's
request for an exact literature reference remains; no new attribution is claimed.

Hypothesis-by-hypothesis rendering:

| Node hypothesis | Lean rendering |
| --- | --- |
| Prime ℓ | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Algebraic closure Ω of Q_ℓ | `(Ω : Type u) [NormedField Ω] [NormedAlgebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]` |
| Extended norm topology on Ω | The topology belongs to `NormedField Ω`; `NormedAlgebra (Padic ℓ) Ω` expresses extension of the p-adic norm. There is no separate, unrelated topology and no completeness assumption on Ω. |
| Increasing intermediate fields indexed by N ≥ 0 | `(F : ℕ → IntermediateField (Padic ℓ) Ω) (hFmono : Monotone F)` |
| Each field finite-dimensional | `hFfinite : ∀ N : ℕ, FiniteDimensional (Padic ℓ) (F N)` |
| Each field closed in Ω | `hFclosed : ∀ N : ℕ, IsClosed (F N : Set Ω)` |
| Union of fields is Ω | `hFcover : (⋃ N : ℕ, (F N : Set Ω)) = Set.univ` |
| Nonempty compact metrizable Hausdorff totally disconnected S | `S : Type v`, with `TopologicalSpace`, `Nonempty`, `CompactSpace`, `TopologicalSpace.MetrizableSpace`, `T2Space`, and `TotallyDisconnectedSpace` instances |
| Compact metrizable Hausdorff topological group G | `G : Type w`, with `Group`, `TopologicalSpace`, `IsTopologicalGroup`, `CompactSpace`, `TopologicalSpace.MetrizableSpace`, and `T2Space` instances |
| Basis of open normal subgroups | `hG : ∀ U ∈ nhds (1 : G), ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ U`; translations give the basis at all points. |
| Integer n ≥ 1 | `(n : ℕ) (hn : 1 ≤ n)` |
| Continuous z on S × G^n | `z : C(S × (Fin n → G), Ω)`; the finite function type has the product topology. |
| Size convention | Explicit, independent universes `u v w` for Ω, S, and G; every variable and universe is bound and `autoImplicit` is disabled. |

Clause-by-clause rendering:

| Node clause | Lean rendering |
| --- | --- |
| Definition of f_z | Inlined as `z (s, fun i : Fin n ↦ (y i.castSucc)⁻¹ * y i.succ)`. Here `castSucc` indexes 0 through n−1 and `succ` indexes 1 through n. No additional homogeneous-cochain construction or group action is assumed. |
| Sequences indexed by j ≥ 1 | Existential `H : ℕ+ → OpenNormalSubgroup G`, `a : ℕ+ → Fin (n + 1) → G`, and `N : ℕ+ → ℕ` |
| Open normal H_j, centres a_(j,0),…,a_(j,n), nonnegative N_j | Encoded by these sequence codomains; neither injectivity nor distinctness is required. |
| Right-coset rectangle R_j | `Set.pi Set.univ (fun i : Fin (n + 1) ↦ MulOpposite.op (a j i) • (H j : Set G))`. The Mathlib opposite action is multiplication on the right: precisely H_j a_(j,i). |
| Exact definition of A_j | An existential sequence `A : ℕ+ → Set S` satisfies a defining equality for every j: the set of all s for which every y in that rectangle has the displayed f_z value in `F (N j)`. Thus A_j is determined, rather than an arbitrary closed subset of the certificate set. |
| Every A_j nonempty and closed | `∀ j : ℕ+, (A j).Nonempty ∧ IsClosed (A j) ∧ …` |
| S is their union | `(⋃ j : ℕ+, A j) = Set.univ` |
| Every index [G:H_j] finite | `Finite (G ⧸ (H j).toSubgroup)`, the finite quotient/coset set (normality identifies left and right index) |
| Countable clopen basis of G | `∃ B : Set (Set G), B.Countable ∧ TopologicalSpace.IsTopologicalBasis B ∧ ∀ U ∈ B, IsClopen U` |
| Countable clopen subsets | `Countable (TopologicalSpace.Clopens G)` |
| Countable open subgroups | `Countable (OpenSubgroup G)` |
| Countable set of coset rectangles | `Set.Countable` on the subset of `Set (Fin (n + 1) → G)` consisting exactly of `Set.pi` rectangles with an open normal H and a tuple of centres. This counts distinct subsets, not presentations; the latter need not be countable. |
| Repetitions permitted | No distinctness condition on any sequence |
| No cocycle condition; A_j need not be open | No cocycle hypothesis and no openness conclusion for A_j |

Dependency declarations read and used:

- `def-weil-l-adic-numbers`: Mathlib `Padic` in
  `Mathlib.NumberTheory.Padics.PadicNumbers`, the Cauchy completion of Q for
  the p-adic norm, and its `normedField` instance. The statement uses this
  recorded definition directly, with the prime instance.
- `def-weil-algebraic-closure`: `AlgebraicClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `IsAlgClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. The dependency's match explicitly
  allows the latter class for an arbitrary chosen closure, as used here.
- `def-weil-size-convention`: the recorded metatheoretic convention has no Lean
  declaration or module; explicit universe polymorphism renders it here.
- `lem-sfb-compact-metrizable-second-countable`: the Lindelof/pseudometrizable
  `SecondCountableTopology` instance in `Mathlib.Topology.Metrizable.Basic`
  (recorded name
  `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetrizableSpace`).
- `lem-sfb-profinite-countable-clopens`:
  `TopologicalSpace.Clopens.countable_iff_secondCountable`,
  `Mathlib.Topology.ClopenBox`.
- `lem-weil-pbc-tychonoff-product-quasi-compact`: `Pi.compactSpace`,
  `Mathlib.Topology.Compactness.Compact`.
- `lem-sfb-baire-closed-cover-interior`:
  `nonempty_interior_of_iUnion_of_closed`, `Mathlib.Topology.Baire.Lemmas`,
  and its locally compact Hausdorff instance
  `BaireSpace.of_t2Space_locallyCompactSpace`,
  `Mathlib.Topology.Baire.LocallyCompactRegular`.

All recorded proof-dependency modules are imported. The metrizable module is
public because its class is also in the signature; the other proof modules are
plain imports. The other public Mathlib modules provide intermediate fields,
finite dimension, normed algebras, open normal subgroups and coset quotients,
clopen sets, and positive naturals. No project notion is copied privately.

Edge cases checked before writing:

- Empty S is excluded by the node, and explicitly by `Nonempty S`. This matters:
  the conclusion requires a positive-indexed sequence of nonempty A_j.
- G cannot be empty because it is a group; its identity tuple witnesses the
  nonemptiness needed in the fibrewise Baire argument.
- Trivial G is allowed. Its only rectangle is nonempty and its quotient is finite;
  the certificate sets reduce to the closed field-membership preimages of z(s).
- Singleton S and constant z are allowed: exhaustion supplies a field containing
  the value, and repeating that certificate gives the required sequence.
- n = 1 uses y(0)^(-1)y(1) with exactly two coset factors. n = 0 is excluded by the
  given hypothesis, without silently changing n to a shifted natural number.
- N_j = 0 and fields repeated in the increasing sequence are allowed.
- Finitely many surviving certificate pairs may be enumerated with repetitions;
  there is no infinite-distinctness assumption.
- Noncommutative G is allowed: every coset uses the right opposite action. Its
  normality is encoded in `OpenNormalSubgroup`, not inferred from commutativity.
- Closure Ω is not assumed complete or locally compact. Baire applies to the
  compact Hausdorff finite group product, not to Ω.
- Countability of presentations with arbitrary centres was deliberately avoided:
  only the image set of distinct rectangles is counted, exactly as in the node.

The module's docstring carries all four inherited proof steps: clopen/finite-index
cosets and total disconnectedness; second countability and counting clopens,
subgroups and rectangles; fibrewise Baire plus the finite intersection of normal
subgroups; closed parameter intersections and enumeration after discarding the
empty sets. No statement fault or dispute was found.

Searches for an existing statement (all wrapper searches used `msearch.py`, NL,
this item):

1. LeanFinder query: `A continuous algebraic p-adic valued function on a parameter space times a profinite group has a countable closed cover of finite subfield coset rectangle certificates`.
   Eight hits, including `Padic.instProperSpace`, finite product approximations
   of continuous maps, and `Profinite.NobelingProof.fin_comap_jointlySurjective`;
   none states exact finite-field rectangle certificates or their closed cover.
2. Loogle query: `IsAlgClosure, IntermediateField, IsClosed`. Zero hits.
3. Mathlib grep query:
   `(rectangle|certificate).*(Padic|cochain|IntermediateField)|(Padic|cochain|IntermediateField).*(rectangle|certificate)`.
   Zero hits.
4. LeanSearch query: `Countable closed finite-field valued coset rectangle certificates for continuous cochains on compact metrizable profinite parameter spaces`.
   Eight hits on `Profinite` limits, light profinite countable clopens, and
   profinite group constructions; no matching theorem.
5. The same rectangle/certificate regex in project `lean/WeilConjectures` and
   `lean/Sheaf` returned unrelated rectangle replacement/diagram occurrences.
   `grep -rn` for this item's id in `lean/WeilConjectures` returned no match.
6. Searches for `castSucc.*⁻¹.*succ`, successive differences, and homogeneous
   cochain coordinates found the coordinate isomorphism for representations and
   uses in accelerated differences, not this result. The coordinate formula is
   written inline; no duplicate cochain equivalence is defined.
7. Searched the chosen full name and rectangle-certificate name variants in
   `dag/lean_names_upstream.json`, Mathlib, `lean/WeilConjectures`, and
   `lean/Sheaf`; no existing declaration with this name or statement was found.

Validation: `scompile.py` checked both the sandbox module and its actual library
module name against the live published build, cleanly (about 1.4 and 1.3 seconds
respectively). The first compile identified the unqualified metrizable class;
both occurrences were corrected to `TopologicalSpace.MetrizableSpace`. The final
file has no compiler errors or warnings, no diagnostic commands, no local
notations or instances, and exactly one postponed theorem. Node JSON uses
one-space indentation, Unicode, a final newline, and the verbatim Lean signature.

This is a direct worker delivery. The maintainer supplies the independent review;
no second worker reading is claimed.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
