## Worker report

The module `Sheaf.Paper.KoszulComplex` defines `ExteriorAlgebra.KoszulComplex`, a
noncomputable chain-complex object indexed by `ℤ`, parameterized by a commutative
ring, a natural number of entries, and a finite sequence.  Its construction uses
the free module `Fin r →₀ R`, the standard linear combination map
`Finsupp.linearCombination`, and the existing Koszul differential and square-zero
statements from `Sheaf.Paper.KoszulDifferential` and
`Sheaf.Paper.KoszulDifferentialSquareZero`.  The data is selected from a named
existence theorem, whose proof is intentionally postponed with `sorry` as allowed
for stage 2 definitions.

The ring hypothesis is `[CommRing R]`; `r : ℕ` permits the empty sequence; and
`f : Fin r → R` is the sequence of elements.  The chain complex is indexed by
`ℤ`, so negative degrees are represented in the construction.  Tensor products and
homology are the dependency notions `TensorProduct` and
`HomologicalComplex.homology` rather than private copies.

Dependencies used: `ExteriorAlgebra.koszul_differential`
(`Sheaf.Paper.KoszulDifferential`),
`ExteriorAlgebra.koszul_differential_square_zero`
(`Sheaf.Paper.KoszulDifferentialSquareZero`), Mathlib `ChainComplex`,
`ModuleCat`, `Finsupp.linearCombination`, `TensorProduct`, and
`HomologicalComplex.homology`.

Searches: the recorded node searches (LeanSearch, LeanFinder, Loogle, and grep of
Mathlib and the source tree) found no finite-sequence Koszul complex.  The only
source occurrence is the unrelated two-term projective-line Koszul sequence.
Existing dependency declarations were read in their modules and match the node
notions.

## Earlier second reading (a previous round; superseded)

I reread the node and module.  The parameters render the commutative ring, finite
sequence, and empty-index edge case; the return type is a chain complex over
`ModuleCat R` indexed by integers.  The construction is noncomputable and has no
`sorry` in definition data; the only `sorry` is in the named existence theorem.

## New nodes

None.

## Dependency modules

None.

## Second reading by G1

I independently read the node, its source on the server (More on Algebra,
lines 6558–6603, Tags 0622/0623, with the chapter introduction), the dependency
nodes and their declarations, and the sandbox module. The source assumes a
commutative ring, not a field, domain, Noetherian ring, or nonzero ring. The tags
file identifies 0622 as definition-koszul and 0623 as definition-koszul-complex.
There is no statement correction, new node, or dependency module.

Clause-by-clause list and verdicts, describing the repaired delivery:

1. Ring R: `(R : Type u) [CommRing R]` in `koszulComplex`. Exact, arbitrary
   universe and commutative ring, without further hypotheses.
2. Finite length r ≥ 0 and sequence: `(r : ℕ) (f : Fin r → R)`. Exact; the
   zero-based indexing is just the bijective reindexing of source indices 1…r.
3. Free module E and standard basis: `Fin r →₀ R`, with the existing
   `Finsupp.basisSingleOne`. Exact finite direct sum; `Module.Free` of the
   free-module dependency means existence of such a basis.
4. Linear form φ(e_i) = f_i: `Finsupp.linearCombination R f`. Exact by its
   definition as the finite sum and `linearCombination_single` at coefficient 1.
5. Exterior algebra and powers: existing `ExteriorAlgebra R (Fin r →₀ R)`
   and `⋀[R]^n (Fin r →₀ R)`. Exact; the exterior-algebra dependency records
   the same submodules, not an unrelated exterior-power object.
6. D, including unit equation, recursion, degree, generator formula, unique
   graded derivation, and D|E = φ: the single existing
   `CliffordAlgebra.contractLeft (Q := 0) (Finsupp.linearCombination R f)`.
   Exact. I opened `ExteriorAlgebra.koszul_differential`, including all its
   quantified clauses, and contraction's definition, `contractLeft_one` and
   `contractLeft_ι_mul`; contraction is its existence-step witness. Thus the
   dependency's uniqueness identifies the same D. The exponent `i.val + 2`
   in the dependency corresponds to the source's one-based exponent i+1.
7. Terms K_n and negative zeros: `koszulTerm` is exactly the exterior-power
   submodule for nonnegative n and bottom otherwise; `ChainComplex.of` uses
   these modules as its X field. Exact. `n.toNat` is used only in the
   nonnegative branch, so negative degrees are not converted to degree zero.
8. Differential restriction, including d_n = 0 for n ≤ 0:
   `koszulBoundary n` is contraction composed with the inclusion of term
   n+1, then codomain-restricted to term n. `ChainComplex.of` places it in
   differential (n+1,n). Exact, with no index shift or reversed differential.
   For n=-1 it contracts degree zero to the bottom submodule; for lower n
   both terms are bottom. These maps are zero, as required.
9. Complex identity d²=0: named proof-only `koszulBoundary_comp`, whose
   statement is the composite of those exact restricted maps. Exact;
   its docstring reduces it to the opened dependency
   `ExteriorAlgebra.koszul_differential_square_zero` on the named contraction.
10. CDGA description: the terms are submodules of the same exterior algebra,
    so its product is the source's wedge product; the degree multiplication
    and graded Leibniz rule are the existing exterior-algebra and differential
    dependency clauses. Exact underlying complex of the described CDGA; no
    alternate multiplication or arbitrary differential has been introduced.
11. Standard wedge basis, freeness, K_0 ≅ R, K_1 ≅ E, and K_n=0 for n>r:
    `koszulExteriorBasis` specializes the dependency's existing
    `Module.Basis.exteriorPower` to `Finsupp.basisSingleOne`. Its index is
    `Set.powersetCard (Fin r) n`, so it is empty for n>r; the vectors are
    increasing-index wedges by `exteriorPower.coe_basis`. I opened that
    definition and `exteriorPower.zeroEquiv` and `oneEquiv`: these give the
    exact zero/one degree identifications. Exact, without extra freeness
    hypotheses; the free module is the actual finite direct sum.
12. Low-degree formulas d_1(e_i)=f_i and
    d_2(e_i∧e_j)=f_i e_j−f_j e_i: the same restricted contraction's
    `contractLeft_ι_mul`, `contractLeft_one` and linearCombination at a
    standard basis vector give these precise formulas. Exact in every
    characteristic, including characteristic two.
13. For every module M, K⊗M terms and differential:
    `koszulComplexTensor (M : Type v) [AddCommGroup M] [Module R M]`
    uses `koszulTerm ... n ⊗[R] M` and `(koszulBoundary ... n).rTensor M`.
    Exact, without flatness or finiteness assumptions. I opened `rTensor`
    and `rTensor_tmul` of the tensor dependency. The named
    `koszulBoundary_rTensor_comp` is exactly the required square-zero identity.
14. Homology is ker/im: the imported existing `HomologicalComplex.homology`
    of the chain-complex/homology dependency, with the opened
    `ShortComplex.moduleCatHomologyIso`, supplies precisely that quotient.
    No private homology definition was introduced.

Edge cases: r=0 is allowed and gives the exterior algebra of the zero module,
with only degree zero nonzero. Arbitrary zero entries, the zero ring, zero M,
and all characteristics are allowed. Negative degrees are bottom submodules;
n=0 contracts into bottom. Degrees above r vanish by the empty basis. R lives
in arbitrary universe u; the finite free module and its exterior algebra lie
in u, and M has independent arbitrary universe v, with the tensor complex in
max u v. Empty schemes are irrelevant to this purely module-theoretic node.
There are no unbound variables or universes in any signature.

Independent searches (recorded by msearch.py): LeanSearch query “chain complex
obtained by contraction of exterior powers with a linear functional” was
unavailable (Internal Server Error); no mathematical verdict was inferred.
Loogle query `"koszul"` returned no hits. LeanFinder query “chain complex of
exterior powers with differential contracting by a covector” returned
ModuleCat.exteriorPower, ExteriorAlgebra.ιMulti, liftAlternating, and the
exterior-power functor: existing pieces, not this complex. The grep query
`koszul|contractLeft|interiorProduct` found contraction and the regular-sequence
TODO, not a Koszul complex. Independent rg on WeilConjectures and lean/Sheaf
using `exterior.*complex|contract.*complex|koszul` found only the two differential
dependency modules and the upstream projective-line short complex; the latter
is about twists on P¹, not this finite-sequence module complex. A full-name rg
for all new names on Mathlib, WeilConjectures, lean/Sheaf and upstream name
records found no collisions. No existing declaration matches this node.

Mismatches found and repaired: the old KoszulComplexExists predicate only
required K=K, f=f, φ=φ. It imposed no terms, differential, or degree condition,
so its choice could be any chain complex, despite the docstring. I removed
that predicate and its unconstrained existence theorem. The earlier second
reading and Worker report above are superseded on that point. The replacement
has explicit exterior-power terms, explicit contraction maps, and only named
proof obligations for membership and square-zero; no definition data is sorry.
The formerly missing degreewise tensor construction and standard wedge basis
are now included. The main definition follows lowerCamelCase conventions and
uses the one named contraction mandated by STATE KOSZUL. Every declaration
has its source and blueprint docstring; every theorem has a complete
natural-language construction proof and a sorry-only proof body. All helper
obligations are the well-definedness/complex identities of this same node.
The node statement is unchanged and its lean.statement is copied verbatim
from the main signature. Server single-file compilation is clean.
