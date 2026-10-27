## Worker report

The module `Sheaf.RingTheory.GaloisEppReducedFibreCover` states
`IsLocalRing.exists_galois_epp_reduced_fibre_cover`. Its sole theorem has proof
`sorry`; its docstring reproduces all fourteen accepted DAG proof steps and their
citations. No definition or axiom is introduced. The node changes only in `lean`.

Source read directly: ILO, Travaux de Gabber, Exposé IV 4.2.3–4.2.5 and
4.3.3–4.3.7, printed pages 58–61 (PDF pages 64–67). In particular, 4.3.5
makes the constant extension generically Galois and normalizes; 4.3.7
identifies the resulting generic group as a subgroup of the constant group.
The node uses a component and its full generic Galois group, as its proof explains.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Commutative normal local domain A | `[CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]` |
| Noetherian A | `[IsNoetherianRing A]` |
| Complete at its maximal ideal | `[IsAdicComplete (maximalIdeal A) A]` |
| Mixed characteristic (0,p) | `[CharZero A]`, `[Fact p.Prime]`, `[CharP (ResidueField A) p]` |
| Dimension d ≥ 2 | `hd : 2 ≤ d` and `hdim : ringKrullDim A = (d : WithBot ℕ∞)` |
| Complete Noetherian normal local domain C | Existential `CommRing`, `IsDomain`, `IsLocalRing`, `IsNoetherianRing`, `IsIntegrallyClosed`, and `IsAdicComplete (maximalIdeal C) C` instances |
| Injective module-finite local A → C | Existential `Algebra A C`, `IsLocalHom (algebraMap A C)`, `Function.Injective (algebraMap A C)`, and `Module.Finite A C` |
| Complete mixed-characteristic DVR W | Existential `CommRing W`, `IsDomain W`, `IsDiscreteValuationRing W`, `IsAdicComplete (maximalIdeal W) W`, `CharZero W`, and `CharP (ResidueField W) p` |
| Perfect residue field k₀ | `k₀` is `ResidueField W`; `PerfectRing (ResidueField W) p` is exactly bijectivity of the pth-power Frobenius |
| Injective local W → C | Existential `Algebra W C`, `IsLocalHom (algebraMap W C)`, and `Function.Injective (algebraMap W C)` |
| Finite group G and actions by local automorphisms | `G`, `Group G`, `Finite G`, `ρC : G →* (C ≃+* C)`, `ρW : G →* (W ≃+* W)`, and the two universally quantified `IsLocalHom` clauses |
| Compatible actions | `ρC g (algebraMap W C w) = algebraMap W C (ρW g w)` for every g,w |
| Action fixes A pointwise | `ρC g (algebraMap A C a) = algebraMap A C a` for every g,a |
| The fraction-field extension induced by A → C | An existential `Algebra (FractionRing A) (FractionRing C)` together with its commuting equation on every `a : A`. This equation uniquely specifies the induced map on fractions |
| Finite Galois | `Module.Finite (FractionRing A) (FractionRing C)` and `IsGalois (FractionRing A) (FractionRing C)`, whose fields give normality and separable algebraicity |
| G identified with the full group of this extension | `e : G ≃* (FractionRing C ≃ₐ[FractionRing A] FractionRing C)`; the equation `e g (algebraMap C (FractionRing C) c) = algebraMap C (FractionRing C) (ρC g c)` ties this identification to the stated C-action |
| Uniformizer π | `∃ π : W, maximalIdeal W = Ideal.span {π}` |
| C/πC reduced | `IsReduced (C ⧸ Ideal.span {algebraMap W C π})` |
| Special-fibre dimension d−1 | `ringKrullDim (C ⧸ Ideal.span {algebraMap W C π}) = ((d - 1 : ℕ) : WithBot ℕ∞)` |
| Equidimensional with that dimension | Every `P` in the minimal primes of the zero ideal of the same quotient has `ringKrullDim ((C ⧸ Ideal.span {algebraMap W C π}) ⧸ P) = ((d - 1 : ℕ) : WithBot ℕ∞)` |
| dim C = d | `ringKrullDim C = (d : WithBot ℕ∞)` |
| C/n finite over A/m | `RingHom.Finite (ResidueField.map (algebraMap A C))`; this is module-finiteness for the induced residue-field map |
| C/n contains k₀ | `Function.Injective (ResidueField.map (algebraMap W C))`, specifying precisely the inclusion induced by W → C |

The dependency declarations were read with their full signatures and docstrings:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` and its ring-map form `RingHom.Finite`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  the uniformizer equality is the one in `irreducible_iff_uniformizer`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, used through
  `IsGalois` in `Mathlib.FieldTheory.Galois.Basic`.

These are public imports. Auxiliary public imports supply the standard fraction
rings, integral closedness, residue-field maps, perfect-ring predicate, and
minimal-prime predicate. Every recorded project proof-dependency module is
imported privately, including Cohen rings, complete-local excellence, complete
DVR normalization, the principal-quotient associated-prime height theorem,
Nagata/Japanese rings, finite complete-local algebras, going up/dimension, and
the product-of-associated-localizations injection. The Mathlib proof inputs
are imported privately where a public statement import does not already give them.
The proof nodes `lem-per-epp-perfect-core-complete-local`,
`lem-per-epp-finite-family-traits`, and `lem-per-epp-single-trait-base-change`
have no Lean records or Mathlib matches in this checkout, so there are no
recorded modules to import for those proof-only dependencies.

Edge cases checked mathematically before writing: d=2 gives fibre dimension 1;
no subtraction is taken in `WithBot ℕ∞`. The zero ring is excluded by the node's
domain hypothesis. Residue characteristic zero and p=0 or p=1 are excluded by
mixed characteristic with p prime. Imperfect residue fields of A and C are
allowed: perfection is required only of W's residue field. Trivial G is allowed;
no faithfulness is imposed on the W-action. A ramified coefficient extension
can move π; equivariance is imposed on W → C, without requiring π fixed.
The special fibre may have multiple minimal primes, all quantified explicitly.
All universes and variables are bound, with `autoImplicit false`.
The witnesses may be in A's universe because C is finite over A, W embeds in C,
and G is finite; this imposes no mathematical size restriction.

Searches actually run (through the prescribed `msearch.py NP <item>` wrapper):

- LeanSearch: `Epp elimination of wild ramification complete local normal ring reduced special fibre Galois`.
  Eight hits, including `Algebra.FormallyUnramified.isReduced_of_field`,
  ramification-index lemmas, and unramified loci; none states the node.
- LeanFinder: `A complete Noetherian normal local domain in mixed characteristic admits a finite Galois extension and coefficient complete DVR with perfect residue field and reduced equidimensional special fibre`.
  Eight hits: DVR TFAE, Henselian TFAE, formally smooth field extensions,
  finite residue-field instances and universal factorization; no complete match.
- Loogle: `IsDiscreteValuationRing, IsAdicComplete, IsGalois`.
  Successful search, zero hits.
- Mathlib grep: `Epp|epp|Galois.*reduced|reduced.*Galois`, under `RingTheory`.
  Four unrelated `ePp` local-variable hits in flat equalizers and smooth fibres.
- Project `rg`: `Galois Epp|reduced special|finite Galois|IsDiscreteValuationRing|Perfect|Equidimensional|normal local domain|complete.*Noetherian`,
  then `epp|Epp|reducedFibre|ReducedFibre` in the RingTheory/Paper directories.
  Existing Epp essentially-finite-type traits and common finite trait extensions
  concern different hypotheses and conclusions; neither is this Galois cover.
- Node-id search in `lean/WeilConjectures`, and searches for
  `Epp|galoisEpp|galois_epp` in `dag/lean_names_upstream.json`,
  `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration for this node.

No statement correction, new node, dependency repair, or disputed statement is needed.

Validation: the prescribed `scompile.py` compiled this module in sandbox mode
and library mode cleanly (2.1 s and 2.2 s respectively). The declaration is the
only `sorry`; no proof was attempted. All Lean lines are at most 98 characters.

## Second reading by NP

A separate clause-by-clause rereading of the node, source and completed file
checked all rows above, particularly the canonical fraction-field embedding,
the restriction equation for the full Galois action, Frobenius bijectivity,
and minimal-prime dimensions. No mismatch was found. The proof docstring was
rewrapped without breaking dependency identifiers. The commuting equation
prevents an unrelated field-algebra structure; the equation involving e
prevents an unrelated identification of G with the automorphism group.

This is the worker's second pass, not a claim of review by another agent:
the dispatch brief prohibits starting other agents and reserves independent
review to the maintainer.
