## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RootDatumRealization` states
`AlgebraicGeometry.exists_split_reductive_root_datum_realization`, with one `sorry`
and no definitions. The node is unchanged except for its `lean` record. No new
nodes, dependency repairs, or statement corrections are needed.

Source read: Milne, Algebraic Groups (2017), Theorem 23.55, printed p.501
(PDF p.513), and Definition C.28 and its consequences, printed pp.613–614
(PDF pp.625–626). The existence theorem allows every reduced root datum.
C.28 uses a one-sided lattice reflection datum, which is retained verbatim
as hypotheses rather than replaced with a preconstructed Mathlib RootPairing.
The Mathlib RootDatum in the conclusion is the same notion used in the recorded
reductive Borel-pair interface.

Hypothesis-by-hypothesis rendering:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The free abelian group of finite rank is `(M : Type v) [AddCommGroup M]
  [Module.Free ℤ M] [Module.Finite ℤ M]`. Its universe is independent of F.
- The finite subset of nonzero lattice elements is `(R : Set M)`, `hR`, `hzero`.
- The bijection to a subset of the integral dual is `c : R → Module.Dual ℤ M`
  and `hc : Function.Injective c`; the coroot subset is its range, so
  surjectivity onto that subset is automatic, not an additional axiom.
- Pairing 2 is `hnorm : ∀ α : R, c α α = 2`.
- Root reflection stability is `hperm`, using the existing `Module.preReflection`;
  `Set.BijOn` expresses permutation of R. A reflection squares to the identity,
  so this is equivalent to Milne's inclusion condition as well as the node's
  permutation condition.
- Finiteness of the generated reflection group is `hW`, with `Subgroup.closure`
  of the range of `Module.reflection (hnorm α)` in the integral linear
  automorphism group. This is the group on the entire lattice, including centre.
- Reducedness is `hred`, the intersection of the rational line through α
  with the image of R in `ℚ ⊗[ℤ] M`, equal to the two signed images of α.
  The canonical rationalization map is injective for a free abelian group.

Conclusion-by-conclusion rendering:

- `G : Grp (Over (Spec (.of F)))` is an actual F-group scheme, and
  `ReductiveTorusCentralizer.IsReductive G` is the recorded reductivity predicate.
- `S` and `iS : S ⟶ G` give the subgroup;
  `ReductiveTorusCentralizer.IsMaximalTorus iS` includes closed immersion,
  torus structure, and maximality under inclusion. The rank existential
  `∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r)` states splitting.
  A reductive group with this split maximal torus is split reductive.
- The existential `IsCommMonObj` witnesses supply the ordinary commutative
  structures of S and G_m, as in the dependency. They are conclusions.
- `aG` is the torus action; its displayed `smul` equality pins it to conjugation
  along `iS`, so it is not an arbitrary representation.
- The finite root set `Φ` consists of actual additive characters
  `Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`.
  `P : RootDatum Φ ... ...` has the actual additive cocharacter Hom group
  as its second lattice. `P.IsReduced` records reducedness.
- `P.root α = α.val` pins its roots to those characters. The weight equivalence
  says that membership in Φ is exactly being a nonzero character with nonzero
  conjugation weight space on the tangent Lie algebra. This reuses
  `TorusCharacterTangent.weightSpace`, which tests characters, not differentials.
- The composition equation for every χ and ν pins `P.toLinearMap χ ν` to
  the actual integer power map on G_m, exactly as in the dependency.
- `eX` identifies the character lattice with M; `eY` identifies cocharacters
  with `Module.Dual ℤ M`. The equality `(eY ν) (eX χ) = P.toLinearMap χ ν`
  makes these equivalences mutually dual. The root-index equivalence `eR`
  and the final two equalities carry every root to its prescribed α and
  every coroot to `c α`. Thus both entire root sets are identified, with
  no discarded central character directions. These data are precisely an
  isomorphism of full root data, written out to accommodate the node's raw input.
  Finiteness of the output lattices follows from these equivalences and the
  finite free input; it is not an extra hypothesis.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: its `mathlib_match` explicitly includes
  `IsAlgClosed`, in `Mathlib.FieldTheory.IsAlgClosed.Basic`; no particular
  construction `AlgebraicClosure` is forced onto the arbitrary field F.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and `CategoryTheory.Grp`,
  in `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to `Over (Spec F)`.
  Read also `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` for its
  documented specialization, group homomorphisms and closed subgroup conventions.
- `lem-sfb-reductive-borel-pair-structure`:
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `AlgebraicGeometry.reductive_borel_pair_structure`. Read its complete signature
  and docstring. This module publicly exposes the exact reductivity/maximal torus
  predicates, split torus, G_m, character weight spaces and Mathlib RootDatum
  used here. No separate model of any of those notions is introduced.
- Proof-only imports: `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding`
  (`RootDatumLattice.lattice_embedding`) and
  `Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation`
  (`LieAlgebra.exists_chevalley_admissible_representation`). These are the
  two proof dependencies with recorded Lean statements. The root-exponential
  group and central-character-sublattice quotient nodes have no Lean record
  yet, so there is no recorded module to import for those proof-only inputs.
  Their steps are retained explicitly in the theorem's complete proof docstring.

Edge cases checked mathematically before writing:

- Empty R: all c/reflection/reducedness conditions quantify over the empty
  subtype; the generated group is trivial, and the conclusion is the split
  torus with character lattice M. Its conjugation action has no nonzero weights.
- Rank-zero M: R is empty by `hzero`; the zero-rank split torus and trivial
  reductive group are permitted. There is no `Nontrivial M` or `Nonempty R`.
- Central torus directions are retained because no root-spanning hypothesis
  is imposed and `eX` identifies the entire character lattice.
- Characteristic 2 and all other characteristics are allowed: no characteristic
  or separability assumption, no inversion of factorials in F. Pairing 2 is
  integral and the weights remain characters, not character differentials.
- The lattice and field universe levels are independent. Finite-rank lattice
  realizations are small up to equivalence even when the supplied lattice's
  carrier is in a larger universe. No test-algebra universe restriction is added.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Every reduced integral root datum is realized by
  a split reductive algebraic group with the prescribed roots and coroots"`:
  the available root-system matches concern abstract root pairings and Lie
  algebras, not existence of a reductive group scheme.
- `msearch.py ... loogle "RootDatum"`: the abstract `RootDatum` abbreviation,
  whose complete declaration and docstring were read. It is used for output;
  it is not an existence theorem.
- `msearch.py ... grep "RootDatum|root.datum|split.reductive"`: five matches,
  all in `Mathlib.LinearAlgebra/RootSystem/Defs.lean`; no group realization.
- `msearch.py ... leansearch "A split reductive algebraic group exists for every
  reduced root datum over an algebraically closed field"`: RootDatum,
  GeckConstruction semisimple Lie algebra, and algebraically closed field facts;
  no exact match. Read RootDatum and RootPairing Hom definitions to distinguish
  lattice data from a group-scheme realization theorem.
- `rg -n 'RootDatum|root.datum|rootDatum|lem-sfb-root-datum-realization'
  lean/WeilConjectures`: no matches. The same search in `lean/Sheaf` finds the
  lattice embedding, reductive Borel-pair conventions and downstream consumers,
  but no declaration of this existence theorem. Searched proposed full name
  through these sources as part of the duplicate check.
- Latest blueprint TeX search for root datum/C.28/23.55 returned no dedicated
  root-datum unit. The item's blueprint.is is null; its cited Milne source
  controls this supporting theorem.

Validation: `scompile.py NN lem-sfb-root-datum-realization <module>` compiled
both the sandbox and named library module cleanly (20.2 s and 2.6 s), with no
errors or non-sorry warnings. `autoImplicit false` binds every variable and universe.
The node signature is extracted verbatim from the theorem, preserving newlines.

No STATEMENT-DISPUTED flag or source discrepancy was found. The pre-existing
Borel-pair interface exposes coroots existentially; this delivery follows that
recorded convention and explicitly requires their compatibility with the
prescribed coroots.

## Second reading by NN

(Written by the maintainer's independent reviewer of delivery 21bec2100bc6, 2026-10-24;
the delivered section stated that no independent reading had been made.)

Node statement as a list, with its Lean rendering and verdict:

- F algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]` (def-weil-field Mathlib Field; def-weil-algebraic-closure mathlib_match IsAlgClosed). OK.
- M free abelian of finite rank: `[AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]`, own universe v. OK.
- R finite subset of M \ {0}: `R : Set M`, `hR : R.Finite`, `hzero`. OK.
- bijection α ↦ α^∨ onto a subset of Hom(M,ℤ): `c : R → Module.Dual ℤ M`, `hc : Injective c` (subset = range). OK.
- ⟨α,α^∨⟩ = 2: `hnorm`. OK.
- s_α(m) = m − ⟨m,α^∨⟩α permutes R: `hperm`, `Set.BijOn (Module.preReflection α (c α)) R R` (preReflection x f y = y − f y • x). OK.
- reflection group on M finite: `hW`, closure of `Module.reflection (hnorm α)` in `M ≃ₗ[ℤ] M`. OK.
- ℚα ∩ R = {α, −α}: `hred` in `ℚ ⊗[ℤ] M` (injective rationalization for free M). OK.
- These hypotheses are byte-for-byte the encoding of the landed proof dependency `RootDatumLattice.lattice_embedding`, so step 1 applies with no conversion (one encoding per notion).
- ∃ split reductive G, split maximal torus S ⊆ G: `G S : Grp (Over (Spec (.of F)))`, `iS`, `IsReductive G`, `IsMaximalTorus iS`, `∃ r, Nonempty (S ≅ splitTorus F r)` — exactly the predicates of lem-sfb-reductive-borel-pair-structure. OK.
- the group root datum of (G,S) in the meaning of borel-pair-structure: Φ ⊆ Additive(S ⟶ G_m), `P : RootDatum Φ X^* X_*`, `P.IsReduced`, `aG` pinned to conjugation along iS, `P.root α = α.val`, pairing pinned by `ν ≫ χ = 1^{⟨χ,ν⟩}`, and Φ = exactly the nonzero characters with nonzero weight space — clause-for-clause the dependency's conclusion. OK.
- isomorphism to the prescribed datum, X^*(S) ≃ M carrying roots and coroots to R, R^∨: `eX`, `eY` with `(eY ν)(eX χ) = ⟨χ,ν⟩` (mutually dual), `eR : Φ ≃ R` with `eX (root α) = eR α` and `eY (coroot α) = c (eR α)`. Every clause pinned; no arbitrary map remains. OK.

Edge cases: R = ∅ (all hypotheses vacuous, Φ = ∅, G = D_F(M) torus allowed); M = 0 (R = ∅ by hzero, trivial group, splitTorus F 0); non-spanning roots (central directions kept since eX is onto the whole M, no spanning hypothesis); every characteristic (no char or separability assumption); universes u, v independent.

Searches: loogle/grep `RootDatum`, rg `RootDatum|root.datum|Chevalley` on lean/Sheaf and lean/WeilConjectures of side-live: only Mathlib's abstract RootPairing/RootDatum, the lattice-embedding and Chevalley-representation proof dependencies, and the downstream citer CentralLatticeEnlargement; no existing realization theorem.

Records: node differs from live only by `lean`; `lean.statement` is verbatim the file's signature; docstrings carry Milne 23.55 / C.28 and `(blueprint: lem-sfb-root-datum-realization)`, theorem docstring carries the 5 proof steps; proof is `sorry`; no definitions. Proof-only private imports (lattice embedding, Chevalley representation) exist in live and do not import this module.

Mismatches found: none in the Lean. Changed: this section only.
