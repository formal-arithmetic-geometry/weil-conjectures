## Worker report

The module `Sheaf.RingTheory.TransitiveProductInertiaComponent` states
`RingTheory.transitive_product_inertia_component`, with `sorry` as its only proof.
It adds no definitions and changes only the item's `lean` record.

Source read: `literature/stacks-project/pione.tex`, Tag 0BST,
`lemma-inertia-invariants-etale`, especially the final paragraph (lines 2754–2784).
I also read the preceding reductions: the source first arranges that the factors are
permuted, then uses their unique primes and purely inseparable residue extensions.
The supplied node already includes all these hypotheses. Its six proof steps are
reproduced in the theorem docstring, including the explicit inverse calculation.
No source error or statement correction is needed.

Hypothesis and object correspondence:

| Node | Lean |
| --- | --- |
| Finite group acting by ring automorphisms on a commutative ring S | `G : Type u`, `[Group G]`, `[Finite G]`, `S : Type v`, `[CommRing S]`, `[MulSemiringAction G S]`. For a group, these endomorphisms are automorphisms. |
| The fixed subring S^H; B = S^G | Mathlib `FixedPoints.subring S H`; the statement uses `FixedPoints.subring S G` directly wherever B occurs. |
| A finite product with n ≥ 1 and its orthogonal idempotents | `J : Type w`, `[Fintype J]`, `j₀ : J`, `e : J → S`, `he : CompleteOrthogonalIdempotents e`. This says each e_j is idempotent, distinct ones are orthogonal, and their sum is 1. Mathlib `CompleteOrthogonalIdempotents.ringEquivOfComm` identifies S with the product of the corner rings, so this is the same product decomposition without naming auxiliary isomorphic factors. Conversely the given product supplies precisely this family. |
| G permutes those idempotents and factors | `hperm : ∀ g j, ∃ k, g • e j = e k`. The inverse group element gives the inverse permutation; orthogonality and the primes ensure different indices have different nonzero idempotents. |
| A prime p of B and the prime Q_j in each factor over p | `p : PrimeSpectrum (FixedPoints.subring S G)`, `Q : J → PrimeSpectrum S`, and `hQ` identify each contraction with p. |
| Q_j belongs to the j-th factor | `hfactor : ∀ j, e j ∉ (Q j).asIdeal`. In a prime quotient the complete orthogonal idempotents have exactly one image 1 and all others 0. |
| Each factor has exactly one prime over p | Existence is given by `Q`, `hQ`, and `hfactor`; `hunique` says every prime over p omitting e_j is Q_j. It does not require Q_j to be maximal or the factor to be local. |
| κ(Q_j)/κ(p) is purely inseparable, including the characteristic-zero convention | `hpure` applies `RingHom.IsPurelyInseparable` to the canonical `Ideal.ResidueField.map` of the fixed-subring inclusion, with contraction equality `hQ j`. Mathlib `Ideal.ResidueField` is the fraction field of the prime quotient (its `IsFractionRing` instance is in `LocalRing/ResidueField/Ideal.lean`); the predicate uses the canonical induced algebra structure and includes characteristic zero. |
| I is the inertia group of Q_1 | Throughout, `(Q j₀).asIdeal.inertia G`. Mathlib defines this by `∀ x, g • x - x ∈ Q`. This implies prime stability (`Ideal.inertia_le_stabilizer`), means identity on the quotient domain, and hence means identity on its fraction field. Conversely trivial residue action implies this formula by injectivity of the quotient into the residue field. Thus it is exactly the node's I. |

Conclusion correspondence, in the order of the Lean conjunctions:

1. `∀ j k, ∃ g, g • e j = e k` states transitivity on the factors.
2. `I = MulAction.stabilizer G (Q j₀).asIdeal` is equality with the prime stabilizer.
3. `I = MulAction.stabilizer G (e j₀)` is equality with the factor idempotent stabilizer.
4. `eI` is the first idempotent as an element of `FixedPoints.subring S I`;
   `(eI : S) = e j₀` identifies it canonically and `heI` supplies its idempotence.
   The ring `heI.Corner` is literally the inertia-fixed elements supported on e_1:
   membership is equivalent to `eI * x = x`. Therefore it is exactly `(e_1 S)^I`.
   In particular, this does not replace fixed points by the image of a projection.
   If a fixed element is supported on e_1, it is in this corner using itself as
   the corner witness; conversely, every corner element is fixed and supported.
5. `aC` and `P : @AlgEquiv B B heI.Corner ... aC` assert the required B-algebra
   equivalence. The formula `((P b).val : S) = e j₀ * (b : S)` fixes its underlying
   map to projection. Since an algebra equivalence commutes with the base map,
   it also fixes `aC` to precisely the structural B-action by that projection.
   The theorem does not assume an algebra structure or an equivalence in advance.
6. The universal clause over `r : J → G`, with `r j₀ = 1` and
   `∀ j, r j • e j₀ = e j`, gives the inverse formula
   `(P.symm a : S) = ∑ j, r j • (a.val : S)` for every fixed supported `a`.
   The established stabilizer equality makes these exactly the coset
   representatives specified in the node. The next conjunction explicitly says
   the two sums for any such `r` and `r'` agree.
7. `D : S^I ≃+* heI.Corner × heI.one_sub.Corner` is the asserted product
   decomposition. Its two formulas characterize it as the actual two projections
   `e₁*s` and `(1-e₁)*s`. The complementary corner is exactly `((1-e₁)S)^I`
   by the same supported-fixed-element description as in clause 4.
8. `W` is represented without an auxiliary variable by `Spec (CommRingCat.of
   heI.Corner)`. Its inclusion in `Spec S^I` is `Spec.map` of
   `(RingHom.fst ...).comp D.toRingHom`. `IsOpenImmersion` and
   `IsClosed (Set.range ...)` say that this first component is open and closed.
9. Membership of `PrimeSpectrum.comap (FixedPoints.subring S I).subtype (Q j₀)`
   in that range is the asserted containment of `Q_1 ∩ S^I`.
10. `bI` is characterized by `(bI b : S) = (b : S)`, so it is exactly the
    inclusion `B → S^I`. The equation of spectrum maps identifies the composite
    structural morphism `W → Spec S^I → Spec B` with `Spec.map P.toRingHom`.
    `IsIso` of that very morphism is the last assertion. These formulas prevent
    an arbitrary component inclusion or arbitrary isomorphism from standing in
    for the canonical structural maps.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, including their
  docstrings and full signatures at lines 470 and 479. These construct all three
  spectra and all induced morphisms in the conclusion.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` at lines 35–39, for the component inclusion.
- Proof dependency `lem-dl-a1-finite-invariant-prime-orbits-residues` is already a
  Mathlib match: `Algebra.IsInvariant.isIntegral`,
  `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `Ideal.IsFractionRing.normal`, `IsFractionRing.stabilizerHom_surjective`.
  I read their complete signatures and section hypotheses in
  `Mathlib.RingTheory.Invariant.Basic` and `.Galois`. The former is public
  because its exported fixed-ring and ideal-action interfaces occur in the
  statement; `.Galois` is imported privately for the recorded proof plan.
- Proof dependencies `lem-weil-pbc-finite-affine-coproduct-spectrum` and
  `lem-weil-pbc-scheme-coproduct-family` are Mathlib matches in
  `Mathlib.AlgebraicGeometry.Limits`, imported privately. I read `sigmaSpec`,
  `ι_sigmaSpec`, its finite-index `IsIso` instance, coproduct existence,
  `sigmaOpenCover`, and `disjoint_opensRange_sigmaι` with their hypotheses.
- Other standard interfaces used directly: `CompleteOrthogonalIdempotents`,
  `IsIdempotentElem.Corner`, the corner ring instances and corner membership
  lemmas in `Mathlib.RingTheory.Idempotents`; `Ideal.ResidueField.map` and
  the fraction-field instance in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`;
  `RingHom.IsPurelyInseparable` in `Mathlib.RingTheory.RingHom.PurelyInseparable`.
  No dependency declaration was repaired or copied.

Searches actually run:

- `msearch.py`, LeanFinder: “Projection from the fixed ring of a finite group
  acting transitively on product factors identifies invariants with the inertia
  stabilizer invariants of one factor”. Eight hits, chiefly
  `IsFractionRing.stabilizerHom_surjective`, `IsFractionRing.stabilizerHom`,
  `Ideal.Quotient.map_ker_stabilizer_subtype`, and quotient/stabilizer lemmas.
  None states the product equivalence, explicit inverse, and component conclusion.
- `msearch.py`, Loogle: `FixedPoints.subring, Ideal.inertia`. Zero hits.
- `msearch.py`, Mathlib grep:
  `(invariant|fixedPoints).*(transitive|[Pp]rod)|(transitive|stabilizer).*invariant`.
  Twenty-five returned hits in representation theory, dynamics, polynomial actions,
  measure theory, and related material. None matches the statement.
- `msearch.py`, LeanSearch: “Projection from invariants of a transitive product
  of commutative rings onto invariants of the stabilizer of one factor”. Eight
  hits concerning `Rep.invariantsFunctor`, representation averaging and
  invariants/coinvariants, and `prodXSubSMul.smul`; none is the ring theorem.
- `rg` in `lean/WeilConjectures` for inertia, fixed points and transitive product
  language found inertia/localization material and unrelated tensor-Galois
  invariance results, but no matching statement. Searching the exact item id,
  chosen declaration name and module name there and in
  `dag/lean_names_upstream.json` found no match.
- `rg` in `lean/Sheaf` found `Sheaf.RingTheory.TransitiveDomainProductInvariants`.
  I read the complete file: its theorem assumes domain factors and already-given
  transitivity and has fraction-field conclusions, without the present inertia
  and clopen-component assertions. Its coordinate fixed-ring helpers use a
  different supplied family of factor maps. It cannot replace this node's theorem
  for arbitrary commutative factors. The exact new declaration name and item id
  had no existing declaration. No new notion needed its own node: fixed rings,
  inertia, complete orthogonal idempotents and corners all exist in Mathlib.

Edge cases checked mathematically before delivery:

- One factor: e_1 = 1, uniqueness and pure inseparability give I = G; the first
  corner is S^G and the complementary corner is the zero ring. No nontriviality
  instance is imposed on it, so its spectrum is empty, as required.
- The empty product is excluded by `j₀ : J`, precisely matching n ≥ 1. A zero
  ring or zero factor cannot have the required prime, so those exclusions come
  from the node's hypotheses and were not added separately.
- The swap action on `k × k` has diagonal full invariants and trivial stabilizer;
  projection and the inverse sum give the usual diagonal/factor equivalence.
- A kernel in the group action lies in inertia; none of the formulas assumes
  faithfulness. In particular a trivial action and one factor are included.
- There is no averaging or division by |G|; characteristic dividing |G| is allowed.
  Pure inseparability in characteristic zero has its usual trivial-extension
  meaning. Nonreduced and non-Noetherian factors are permitted.
- Nonmaximal p and Q_j are allowed: residue fields are the canonical fraction
  fields of the prime quotients, not a quotient mistakenly assumed to be a field.
- `u`, `v`, and `w` are explicitly declared independently. Only a finite index
  is used, and there is no hidden equality of ring, group or index universes.

Validation: `scompile.py Q102 lem-dl-a1-transitive-product-inertia-component`
compiled the file both in sandbox mode and at its final library module path,
with no errors or warnings (reported 2.6 s and 4.2 s). Every theorem proof is
`sorry`; there are no helper proofs, definitions, local notations, local
instances, auto-bound variables, or lines exceeding 100 characters.

## Second reading by Q102

This is the author's own rereading; no second worker was started, following the
dispatcher's instruction. The maintainer supplies the independent review.
I reread the node, its six proof steps, Tag 0BST and the delivered theorem.
The main encoding choice is the corner *inside the fixed ring*, which gives
exactly the fixed ring of the factor rather than only the projection image.
The existential algebra structure is constrained by the projection formula and
`AlgEquiv`'s base-commutation law; the structural inclusion is constrained by
its ambient-value formula. Thus neither is extra assumed data. The conclusion
contains both stabilizer equalities, the universal inverse formula, explicit
representative independence, both product projections, the clopen range,
contracted-prime membership, and the canonical structural morphism's `IsIso`.
No mismatch or node correction was found.
