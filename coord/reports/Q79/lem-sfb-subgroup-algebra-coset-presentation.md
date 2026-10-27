## Worker report

The module `Sheaf.RingTheory.SubgroupAlgebraCosetPresentation` states
`AddMonoidAlgebra.subgroup_algebra_coset_presentation`, with one sorry and no proofs.
Its public helpers belong to the literal presentation in this node: the subgroup
scalar structure, Laurent group ring, relation ideal, quotient, and the two
normalization predicates. All definitions contain real data. No new mathematical
notion or separate DAG node is needed: Laurent rings here are precisely the
existing `AddMonoidAlgebra` on the finite integer exponent group. In particular,
no isomorphism or evaluation is chosen from a sorry-backed mere existence proof.

Hypotheses and clauses, in node order:

- `R : Type u`, `[CommRing R]`, `M : Type v`, `[AddCommGroup M]`, and
  `L : AddSubgroup M` are the arbitrary base ring, additive abelian group and subgroup.
  No finite generation, nontriviality or characteristic condition is imposed here.
- The group algebras are the same `AddMonoidAlgebra R M` used by the recorded
  diagonalizable-group dependency, whose full source was read. `single m 1` is e_m.
  The inclusion is Mathlib's `mapDomainRingHom R L.subtype`; its injectivity is
  the first conjunct. `subgroupAlgebra` is exactly this ring homomorphism's
  `toAlgebra`, so all later scalar structures are the specified inclusion.
- Any representatives are `t : M ⧸ L → M` with `(t c : M ⧸ L) = c` for every c.
  The second conjunct supplies a `Module.Basis (M ⧸ L)` over R[L] whose value at
  each c is `single (t c) 1`. `Module.Basis` means a linear equivalence with
  finitely supported coefficient families, hence exactly existence and uniqueness
  of the node's finite expansions. This clause has no finite-generation condition.
- `AddGroup.FG (M ⧸ L)` is precisely the hypothesis for the remaining conjunct.
  The conclusion contains `Algebra.FinitePresentation R[L] R[M]` for this scalar action.
- Every r,s is a natural number (including zero); `d : Fin s → ℕ` with `2 ≤ d j`
  gives the stated cyclic orders. `D` is an additive equivalence from M/L to
  `(Fin r → ℤ) × ((j : Fin s) → ZMod (d j))`. These are the node's finite direct
  sums, expressed as finite products. This is any chosen decomposition, not just
  the prime-power decomposition in the proof dependency.
- The equations for `D (a i)` and `D (b j)` use the respective coordinate vectors
  `(Pi.single i 1, 0)` and `(0, Pi.single j 1)`, so a,b are precisely lifts of the
  indicated generators, with no condition on their order in M.
- `l : Fin s → L` with `(l j : M) = d j • b j` records l_j=d_j b_j as a subgroup
  element. It is quantified with its defining equality, not an extra assumption:
  the preceding lift equations imply this multiple lies in L.
- `subgroupLaurentRing R L r s` is the finitely supported group algebra over R[L]
  on `((Fin r ⊕ Fin s) → ℤ)`. A coefficient monomial is `single n c`. Integer
  addition is multiplication of monomials, exactly the prescribed Laurent ring;
  the single exponent vectors ±1 give inverse variables with product 1.
- `subgroupLaurentRelations` is `Ideal.span (Set.range ...)` of the literal
  binomials `single (Pi.single (Sum.inr j) (d j : ℤ)) 1 - single 0 (single (l j) 1)`.
  Thus it is exactly (Y_j^d_j-e_(l_j)), with no free-generator relations.
  `subgroupLaurentQuotient` is the quotient by this actual ideal.
- The existential algebra equivalence e has `IsSubgroupLaurentEvaluation`:
  every class `single n c` maps to the inclusion of c times
  e_(sum_i n_Xi a_i + sum_j n_Yj b_j). Setting n=0 fixes coefficients via j;
  setting a single exponent to 1 gives X_i↦e_(a_i), Y_j↦e_(b_j), and setting it
  to -1 gives the specified inverses. These values on every coefficient monomial
  uniquely specify the node's displayed homomorphism, so the equivalence is the
  displayed map itself, not an arbitrary isomorphism between the same rings.
- For every `R' : Type w`, `[CommRing R']` and `f : R →+* R'`, the statement
  supplies e' with the identical evaluation normalization and the ring map g.
  `IsSubgroupLaurentBaseChange` sends `single n c` to
  `single n (mapRingHom L f c)` in the corresponding quotient. This is exactly
  the coefficient map, fixing variables and every subgroup index. The final
  equation `e' (g x) = mapRingHom M f (e x)` is the full commuting square on
  every quotient element. Hence the displayed map remains an isomorphism with
  the required coefficient compatibility (and its inverse is compatible too).

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup` and `ringDiagonalizableGroupMap`;
  their implementations use `AddMonoidAlgebra` and `mapDomainBialgHom`. The same
  underlying algebra and index maps are used here, with no duplicate group-scheme definition.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, `Module.Basis`, with
  `Module.Free.exists_basis` identifying the intended basis notion.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, whose
  full signature uses a finite-variable polynomial surjection with FG kernel.
- Proof imports: `Mathlib.GroupTheory.FiniteAbelian.Basic`, declaration
  `AddCommGroup.equiv_free_prod_directSum_zmod`; and `Mathlib.RingTheory.AdjoinRoot`,
  declaration `AdjoinRoot.powerBasis'`, with monic-quotient free/finite corollaries.
  Their full signatures and docstrings were read. These imports retain the DAG's
  proof plan and are not public statement dependencies.
- Mathlib's `AddMonoidAlgebra.mapDomainRingHom`, `mapRingHom`, `Ideal.span` and
  `Ideal.Quotient.mk` give all the canonical underlying constructions.

Edge checks: over the zero ring every group algebra and Laurent quotient is zero;
its arbitrary-index coefficient modules are zero too, so the stated basis is valid.
For L=M the quotient is trivial and the coset basis is a single unit e_t; for L=0
this recovers the ordinary e_m basis. For r=s=0 the exponent group is trivial and
the relation range is empty, giving R[L] itself; the normalization still fixes all
coefficients. With r=0 or s=0 only the appropriate variable family remains. Torsion
in M is not cancelled, and the orders d_j need not be units in R. None of the code
assumes an integral domain, a field, or that M or L is finitely generated.

Searches, all via the prescribed tools and read-only sources:

- `msearch.py ... leanfinder "For a subgroup of an abelian group the group algebra
  is free on coset representatives and has a finite Laurent polynomial presentation
  if the quotient is finitely generated"`: eight hits, including
  `AddMonoidAlgebra.finiteType_iff_group_fg`, `finiteType_of_fg`, free representation
  modules, and algebra presentations. None states the relative coset-basis/Laurent
  quotient theorem; finite type over the base ring is not this conclusion.
- `msearch.py ... loogle "AddMonoidAlgebra, Module.Free"`: only
  `AddMonoidAlgebra.instFree`, which gives freeness over the scalar base, not R[L].
- `msearch.py ... grep "coset|[Ss]ubgroup|[Ff]inite[Pp]resentation"
  Algebra/MonoidAlgebra`: zero hits.
- `msearch.py ... leansearch "subgroup group algebra free coset basis Laurent
  polynomial finite presentation"`: eight hits, mainly free groups and
  `Representation.freeAsModuleBasis`; none is the relative algebra presentation.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for groupAlgebra, subgroupAlgebra,
  Laurent, cosetPresentation, the item's id and the proposed declaration names:
  found only unrelated one-variable Laurent API and Laurent-stratum modules;
  no existing declaration of this theorem or the presentation helpers. The exact
  item-id search also finds no upstream implementation. The upstream-name index
  has no proposed declaration name.
- Read the relevant Mathlib source signatures for coefficient/domain maps,
  free modules, finite presentation, finite abelian decomposition and monic quotients.
  Read Milne's PDF using `pdftotext -layout`, Theorem 12.9(b), pp.233–234:
  it identifies the injection and quotient calculation; the node explicitly
  records its relative coset/Laurent strengthening, and its eight-step proof
  supplies the detailed normal forms used in the theorem docstring.

No statement correction, unusable dependency, or statement dispute was found.

## Second reading by Q79

This is the dispatcher's requested author self-check, not a claimed independent
agent review; the maintainer supplies the independent reading after delivery.
Re-read the node and the completed module together. The unconditional basis is
separate from the FG implication, so no quotient finiteness leaked into that clause.
The scalar action is the subgroup inclusion, not the ordinary R scalar action.
The Laurent exponents are all integers, and the relation's constant really is
indexed by l_j in L. Both lift equations use D in the quotient-to-coordinates
direction, and the subgroup equality uses natural-number repeated addition,
matching d_j b_j. The algebra equivalence fixes coefficients and all variables
by normalization on every monomial. The base-change clause includes both an
isomorphism over R' and the commuting square for all elements, with coefficient
maps retaining the same indices. Empty lists, zero rings and torsion remain in
scope. No mismatch or mathematical change was needed in this reading.
