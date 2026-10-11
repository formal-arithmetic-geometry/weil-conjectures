## Worker report

The module `Sheaf.RingTheory.CompleteLocalMapRegularPresentation` states the complete-local regular presentation theorem from Stacks 07NN. It uses Mathlib's `IsNoetherianRing`, `IsLocalRing`, `IsAdicComplete`, `IsRegularLocalRing`, `RingHom.Flat`, ideals, quotients, and ring equivalences; no proof is supplied (`sorry`).

The hypotheses are rendered by commutative rings `A`, `B`, Noetherian and local typeclass assumptions, adic completeness for each maximal ideal, and a ring homomorphism `f : A →+* B` with `hf : IsLocalHom f`. The conclusion quantifies commutative Noetherian local complete regular rings `R`, `S`, surjective local maps `q : R →+* A` and `v : S →+* B`, and local `u : R →+* S`. The compatibility clause is `v.comp u = f.comp q`; the residue-field clause is an explicit ring equivalence `(R ⧸ m_R) ≃+* (A ⧸ m_A)` commuting with quotient maps. A regular system of parameters is rendered as a finite `Fin d` family spanning `m_R`, with `ringKrullDim R = d`; an injective `Fin d ↪ Fin m` identifies its images with part of a spanning `Fin m` family of `m_S`, with `ringKrullDim S = m`. The final clauses are `RingHom.Flat u` and regularity of `S ⧸ m_R.map u`.

Dependency declarations used are Mathlib declarations: `IsNoetherianRing`, `IsAdicComplete`, `IsRegularLocalRing`, and `RingHom.Flat`; all are exact notion matches recorded by the dependency nodes `def-weil-pbc-noetherian-ring`, `def-weil-pbc-adically-complete-ring`, `def-weil-regular-scheme` (ring-level regular local notion), and `def-weil-pbc-flat-ring-map`.

Edge cases checked include `d = 0` (empty parameter family, giving `m_R = 0`), `m = 0`, and zero-dimensional regular local rings. The quotient and parameter clauses remain well-typed in these cases.

Searches made: LeanSearch/LeanFinder and grep for complete local regular presentations returned no theorem; searches for Cohen, regular local, formally smooth, and parameter presentations in pinned Mathlib found only the ring-level `IsRegularLocalRing` and no presentation theorem. The node's recorded searches likewise report no match. No new nodes or dependency modules were needed.

## Earlier second reading (a previous round; superseded)

Read the node and module together. Every source hypothesis appears as an explicit typeclass or `IsLocalHom f`; the existential presentation includes both surjective local quotient maps, the commuting square, the residue-field isomorphism, parameter extension, flatness, and regular closed fibre. The module compiles on the remote server with only the expected `sorry` warning.

## Second reading by M1

Independent reading of the sandbox node and module, the four statement dependency nodes,
and their actual Mathlib declarations. Read Stacks Tag 07NN at
`/home/ubuntu/c1-stacks-review/more-algebra.tex:9769` through its entire proof and the section
opening at line 9694; checked its tag in `tags/tags`. The section imposes no extra standing
hypothesis. The node deliberately retains only the regularity/parameter consequences of
07NN, as its source record says; it does not request the characteristic-dependent
power-series descriptions. The residue-field assertion follows from the coefficient-ring
choice in that proof. No correction of the node is needed, and there is no
`statement_change`, new definition node, or dependency module to review.

Objects, hypotheses and conclusions, in node order:

| Node item | Lean rendering | Verdict |
|---|---|---|
| Commutative rings A and B | `(A : Type u) (B : Type v) [CommRing A] [CommRing B]` | Exact, independent arbitrary universes. |
| Noetherian A and B | `[IsNoetherianRing A] [IsNoetherianRing B]` | Exact; read Noetherian/Defs.lean:196 and `isNoetherianRing_iff_ideal_fg`. |
| Local A and B | `[IsLocalRing A] [IsLocalRing B]` | Exact; LocalRing/Defs.lean:30 includes nontriviality, as a local ring must. |
| Maximal-ideal-adic completeness of A and B | `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]` and the corresponding B instance | Exact, including separatedness; read AdicCompletion/Basic.lean:56 and `AdicCompletion.of_bijective_iff` at 647. |
| Local homomorphism f, sending m_A into m_B | `(f : A →+* B) (hf : IsLocalHom f)` | Exact; Units/Hom.lean:270 defines reflection of units; `IsLocalRing.local_hom_TFAE` in LocalRing/RingHom/Basic.lean:79 identifies it with the node's ideal condition. |
| Existence of regular local rings R and S | Existential types R, S, their commutative-ring structures, local and Noetherian structures, and `IsRegularLocalRing R`, `IsRegularLocalRing S` | Exact; redundant explicit local/Noetherian structures express constituents of regular local, not extra assumptions. Read RegularLocalRing/Defs.lean:51. |
| Maximal-ideal-adic completeness of R and S | Existential `IsAdicComplete (IsLocalRing.maximalIdeal R) R` and S instance | Exact. |
| Surjective local q : R → A and v : S → B | Existential q and v, `Function.Surjective q ∧ IsLocalHom q` and corresponding v clauses | Exact. |
| Local u : R → S | Existential u and `IsLocalHom u` | Exact. |
| Commuting square vu = fq | `v.comp u = f.comp q` | Exact direction of composition. |
| q induces a residue-field isomorphism | Existential `e : (R ⧸ m_R) ≃+* (A ⧸ m_A)` with `∀ r, e (Ideal.Quotient.mk m_R r) = Ideal.Quotient.mk m_A (q r)` | Exact: the compatibility ensures this is the map induced by q, not an unrelated abstract isomorphism. Both quotients are fields. |
| A regular system t_1,...,t_d of R | `∃ (d : ℕ) (t : Fin d → R), ringKrullDim R = d ∧ Ideal.span (Set.range t) = m_R` | Exact: the node explicitly defines a regular system as dim R generators. The span equality also places every generator in m_R. |
| Images extend to a regular system of S | `∃ (m : ℕ) (s : Fin m → S) (i : Fin d ↪ Fin m), ringKrullDim S = m ∧ Ideal.span (Set.range s) = m_S ∧ ∀ j, s (i j) = u (t j)` | Exact: an injection selects the images as part of the larger system, with arbitrary reordering allowed. No injectivity of u is assumed. |
| u is flat | `RingHom.Flat u` | Exact; read RingHom/Flat.lean:27, flatness for the module structure induced by this very u. |
| Closed fibre S/m_R S is regular local | `IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map u)` | Exact: `Ideal.map u` is the extended ideal generated by u(m_R); the regularity class includes local and Noetherian. |

Quantifier order is unchanged: given A, B and f with their hypotheses, choose R, S and
the three maps together; the residue-field identification and parameter families witness
properties of those same maps. Neither characteristic, finite type, an algebra structure,
nor formal smoothness is assumed. The latter is used only in the natural-language proof.

Edge cases: d = 0 uses `Fin 0`, gives the zero maximal ideal of R, and leaves the closed
fibre equal to S; the injection from `Fin 0` is harmless. m = 0 forces d = 0 through the
embedding, as the node's parameter-extension condition requires. Fields, equal and mixed
characteristic, and zero-dimensional regular local rings are included without restrictions.
The zero ring is excluded by local-ring nontriviality in both the source and Lean; empty
schemes are not objects of this algebraic node. Universes u and v are explicitly bound and
independent; the coefficient rings and finite-variable power-series rings in the source
construction can be taken in the respective universes of A and B (no universe increase).
Every other variable is explicitly bound; no auto-implicit variable is needed.

Independent searches (2026-10-11), logged by msearch.py in searches.jsonl:

- LeanSearch query: “A local ring homomorphism between complete Noetherian local rings lifts
  to a flat map between complete regular local rings with regular closed fibre”. The service
  returned Internal Server Error; no mathematical verdict is inferred from this failure.
- LeanFinder query: “Compatible Cohen presentations lifting a local homomorphism with
  images of parameters extending to regular parameters”. Eight hits, including
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` and StandardEtalePair lifts;
  none is a compatible regular presentation theorem. The formally smooth lifting signature
  assumes a formally smooth algebra and gives a lift into a quotient situation only.
- Pinned Mathlib grep: `Cohen|regular.*presentation|parameter.*system|system.*parameter` in
  RingTheory returned only the unrelated Cohen bibliography entry in Noetherian/OfPrime.
- Direct rg of Mathlib, WeilConjectures and lean/Sheaf for `IsSystemOfParameters`,
  `IsRegularSystemOfParameters`, `systemOfParameters`, `regularSystemOfParameters` found
  no declaration. Direct searches of WeilConjectures and lean/Sheaf for Cohen, regular
  presentations, parameters, and the proposed declaration name found no existing theorem
  with this statement. The upstream-name table has no collision either. The landed Cohen
  structure surjection theorem is only a one-ring presentation and lacks the compatible
  square and parameter-extension assertion. Nearby DAG nodes for flat presentations and
  Cohen presentations state respectively fewer and more clauses, and provide no existing
  declaration of this item. No missing notion requires a new definition.

Mismatches and repairs: H8, the original theorem docstring only summarized the proof in a
sentence, omitting the closed kernel, local lift, evaluation uniqueness, inverse substitution,
and separate flatness and quotient steps. Replaced it with all six node proof steps and
all the dependency IDs they use. H9, added the standard copyright/license/authors header.
The signature and node record were already correct and are unchanged. There is exactly
one theorem with proof `by sorry`, no definitions, no hollow data, and no proved assertion.
All three imports provide notions occurring in the signature. No line exceeds 100 columns.

Validation: scompile.py compiled the complete module on the server cleanly (1.6 seconds),
with no error or warning. Checked that lean.statement is verbatim the file's signature.
