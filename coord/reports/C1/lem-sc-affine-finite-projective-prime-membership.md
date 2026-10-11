## Worker report

The module states the prime-membership criterion for a finite projective module. It uses
`Module.Finite` and `Module.Projective` as the finiteness and projectivity hypotheses,
`Ideal.IsPrime` for the prime ideal, `LocalizedModule.mk s 1` for the canonical image of
`s`, and the submodule scalar products `p • (⊤ : Submodule R N)` and
`Ideal.map (algebraMap R (Localization p.primeCompl)) p • ⊤` for `pN` and its localized
counterpart. The theorem is `Module.prime_mem_localized_iff` in
`Sheaf.RingTheory.AffineFiniteProjectivePrimeMembership`.

The Lean binders render every hypothesis: `R` is a commutative ring; `N` is an additive
commutative group with an `R`-module structure; `[Module.Finite R N]` says `N` is finite;
`[Module.Projective R N]` says it is projective; `s : N`; `p : Ideal R`; and
`hp : p.IsPrime`. The left clause is membership of the canonical fraction `s/1` in the
extension of `p` to `Localization p.primeCompl`, acting on the top localized submodule.
The right clause is membership of `s` in `p` acting on the top submodule of `N`; the `↔`
connects the two clauses exactly.

Dependencies used are Mathlib declarations recorded by the dependency nodes:
`Module.Projective` (`Mathlib.Algebra.Module.Projective`), `Localization.AtPrime` /
`Ideal.ResidueField` (`Mathlib.RingTheory.Localization.AtPrime.Basic`), and
`LocalizedModule` (`Mathlib.Algebra.Module.LocalizedModule.Basic`). No project module
was needed. Searches recorded by stage 1 found no exact existing theorem: LeanSearch
(`finite projective module s in pN iff s/1 in p N_p`) and LeanFinder
(`prime ideal membership detected after localization for finite projective module`) found
only component lemmas; grep of Mathlib RingTheory/LinearAlgebra found no exact criterion.
The source is Stacks Project, algebra.tex, Lemma Tag 00NX.

Edge cases checked include `N = 0`, `s = 0`, `p = ⊥` when prime, and rank-zero/free
specializations; the scalar-product submodule formulation handles these without extra
nonemptiness assumptions. The theorem proof is intentionally `sorry` at stage 2.

## Earlier second reading (a previous round; superseded)

Independent rereading of the node and module found no mismatch. The commutative-ring, finite-projective, element, and prime-ideal hypotheses all occur explicitly, and the two membership clauses use the canonical localization fraction and the corresponding extended ideal submodule. No statement correction or dependency module is needed.

## Second reading by C1

I reread the node, its source place, all three dependency records, and the Lean file
independently. The node introduces: a commutative ring `R`; a finite projective
`R`-module `N`; an element `s : N`; a prime ideal `p ⊂ R`; the complement
`S = R \ p`; the module localization `N_p = S⁻¹N`; and the canonical fraction `s/1`.
The Lean renders these respectively as `{R : Type u} [CommRing R]`, `{N : Type v}`
with `[AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]`,
`s : N`, `p : Ideal R`, `hp : p.IsPrime`, `LocalizedModule p.primeCompl N`, and
`LocalizedModule.mk s 1`. The conclusion has exactly the two node clauses and the
same order: membership of `s/1` in the extension of `p` to the localized top
submodule iff membership of `s` in `p • (⊤ : Submodule R N)`. `Ideal.map` along
`algebraMap R (Localization p.primeCompl)` renders the extended ideal, so no
additional Noetherian, nonzero, rank, or universe restriction is present.

The source is Stacks, Algebra, Tag 00NX (finite projective modules), whose direct
summand characterization supplies the finite-free splitting used by the blueprint;
the membership criterion is the stated localization/direct-summand consequence.
Dependency declarations are `Module.Projective` (Mathlib.Algebra.Module.Projective),
`Localization.AtPrime` (Mathlib.RingTheory.Localization.AtPrime.Basic), and
`LocalizedModule` (Mathlib.Algebra.Module.LocalizedModule.Basic); each has the
notion recorded by its dependency node. Searches found no existing exact theorem:
LeanSearch query `finite projective module s in pN iff s/1 in p N_p`, LeanFinder query
`prime ideal membership detected after localization for finite projective module`,
and grep for `pN|Prime.*LocalizedModule|projective.*torsion` in Mathlib and
WeilConjectures. All returned only component declarations.

Edge cases checked are `N = 0`, `s = 0`, `p = ⊥` when prime, rank-zero/free modules,
the empty index set in a free presentation, and arbitrary universe levels `u,v`.
The scalar-product formulation handles zero modules and empty presentations without
extra assumptions; `n = 0` is included by the finite-free surjection argument.

The only mismatch found was documentary: the theorem docstring summarized the proof
without carrying its individual steps and dependency citations as required by H8.
I expanded it to state the finite surjection, projective lift, localized splitting,
forward projection through `i` and `π` using `lem-sc-free-prime-membership`, and the
converse by localization. The statement and node record were otherwise unchanged.
