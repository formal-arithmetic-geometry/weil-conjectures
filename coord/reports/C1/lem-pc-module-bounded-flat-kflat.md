## Worker report

`Sheaf.Algebra.Homology.BoundedFlatKFlat` states
`CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`; its proof is `sorry`.

Statement correspondence:

- The base ring is `{R : Type u} [CommRing R]`. The node says only "ring"; see the
  statement fault below.
- `P : CochainComplex (ModuleCat.{u} R) ℤ` is the integer-indexed cochain complex
  of R-modules.
- `hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)` says that P vanishes
  above a bound, including the zero and empty-support complexes.
- `hflat : ∀ i : ℤ, Module.Flat R (P.X i)` says that tensoring with every term
  preserves exact sequences. `Module.Flat.iff_lTensor_preserves_shortComplex_exact`
  in `Mathlib.RingTheory.Flat.CategoryTheory` verifies the match.
- `∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic → ...` quantifies over
  every acyclic complex, including the zero complex.
- `(mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic` is acyclicity
  of the total tensor complex. The K-flat terminology is the corresponding
  module specialization of `CochainComplex.IsKFlat` for sheaves of modules.

Dependencies read: `CochainComplex` from
`Mathlib.Algebra.Homology.HomologicalComplex`; `HomologicalComplex.Acyclic`
from `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`;
`CochainComplex.mapBifunctor` from
`Mathlib.Algebra.Homology.BifunctorShift` (the recorded
`HomologicalComplex.mapBifunctor` is in `Mathlib.Algebra.Homology.Bifunctor`);
`CochainComplex.IsKFlat` from `Sheaf.Algebra.Homology.KFlat`.
The last is sheaf-specific, so the module statement expands its defining
acyclic-tensor clause directly.

Searches: `msearch.py leanfinder` on "bounded above cochain complex of flat
modules is K-flat; tensor with every acyclic complex is acyclic" found flatness
criteria, not the theorem. `msearch.py loogle` on
`CochainComplex.kFlat_of_isStrictlyLE_of_flat, CochainComplex.KFlat, ModuleCat`
reported that the first name is unknown to Mathlib. `msearch.py grep` for
`kFlat_of_isStrictlyLE_of_flat|KFlat` under `Algebra/Homology` found no Mathlib
match. `rg` in `WeilConjectures` found
`CochainComplex.kFlat_of_isStrictlyLE_of_flat` in
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`: it concludes the
source's two-sided, quasi-isomorphism-based K-flat predicate, with extra
abstract category hypotheses, rather than the node's acyclic total tensor
statement. `rg` in `lean/Sheaf` found the sheaf-specific `IsKFlat`; the exact
declaration name is absent from Mathlib, the source, and Sheaf.
`grep -rn` for the node id in `WeilConjectures` found nothing. The Stacks
source file is absent on this machine; the node's recorded source and proof
were used.

STATEMENT-DISPUTED: The node says an arbitrary ring R and complexes of
R-modules on both sides of `L ⊗_R P`. For noncommutative R, the ordinary tensor
product needs a right R-module on one side. The recorded dependency
`def-pc-kflat-complex` is explicitly over a sheaf of commutative rings. The
Lean statement uses `[CommRing R]` to give the tensor expression its intended
meaning. The DAG statement should say "commutative ring" if that is intended.

## Second reading by C1

The node introduces a commutative ring `R` (corrected from the original
unqualified “ring”), a bounded-above cochain complex `P` of `R`-modules,
termwise flatness, an arbitrary acyclic cochain complex `L`, and the total tensor
complex. Lean renders these as `{R : Type u} [CommRing R]`,
`P : CochainComplex (ModuleCat.{u} R) ℤ`,
`∃ b : ℤ, ∀ i, b < i → IsZero (P.X i)`,
`∀ i, Module.Flat R (P.X i)`, and
`∀ L, L.Acyclic → (mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic`.
The conclusion is exactly acyclicity of the total tensor, with K-flatness supplied
by `def-pc-kflat-complex`.

Edge cases checked: the bound permits zero and empty-support complexes; `IsZero`
permits zero terms; `L` is universally quantified, including the zero complex;
`ℤ` includes degree zero and all integer degrees; no characteristic or
finite-generation hypothesis is introduced; and the universe is explicit. Tag
064K says “ring”; the project's commutative sheaf tensor dependency requires the
explicit `[CommRing R]` specialization.

Searches found no exact theorem in Mathlib or `WeilConjectures`. Mathlib provides
`Module.Flat` and `HomologicalComplex.Acyclic`; the source's
`CochainComplex.kFlat_of_isStrictlyLE_of_flat` is a different abstract
quasi-isomorphism predicate. No dependency module or new definition was needed.

The mismatch found was the missing commutativity hypothesis in the node statement.
I changed only the node statement, added `statement_change` with all eight citers,
and kept the compiling Lean declaration unchanged.

## Statement corrected

Old statement: “Let R be a ring and let P^\\bullet be a bounded-above cochain
complex of flat R-modules, where flat means that tensoring with the module
preserves exact sequences. Then for every acyclic cochain complex L^\\bullet of
R-modules, the total tensor complex Tot(L^\\bullet \\otimes_R P^\\bullet) is
acyclic; equivalently P^\\bullet is K-flat [def-pc-kflat-complex].” The recorded
Lean tensor construction is only over commutative rings, so the node was corrected
to say “commutative ring.” The correction follows Tag 064K, with Stacks' usual
commutative-ring convention made explicit (Stacks Conventions: a ring is a
commutative ring with 1). All eight citers hold: each is Stacks-sourced, so its
"ring" is commutative: `lem-sc-perfect-local-pseudocoherent-free-model`,
`lem-sc-complex-lift-class-projective`, `lem-pc-bounded-above-flat-kflat`,
`lem-pc-affine-perfect-hom-colimit`, `lem-pc-module-tor-amplitude-flat-model`,
`lem-pc-derived-pullback-tor-independent-flat-complex`,
`lem-pc-termwise-tor-acyclic-derived-tensor` and `lem-pc-base-change-rhom-perfect`.
(Reviewer R-bfk0853: C1 had marked the first six `holds: false`; corrected.)
