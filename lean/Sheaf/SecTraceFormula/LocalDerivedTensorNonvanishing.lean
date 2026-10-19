module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.RingTheory.ProjectiveOverLocalFree
import WeilConjectures.RingTheory.RingPseudoCoherent
import Sheaf.Algebra.Homology.PseudoCoherentTensorClosure
import Sheaf.Algebra.Homology.TopDegreeTensor
import Sheaf.RingTheory.LocalFiniteTensorNontrivial

/-!
# Tensor nonvanishing over a local ring

Source: literature/stacks-project/more-algebra.tex, Tag 0DJE (lemma-tensor-pseudo-coherent),
for closure under tensor; the nonvanishing assertion is an agent corollary from top cohomology
of bounded-above free resolutions and Nakayama (Tag 00DV)
(blueprint: lem-trf-local-derived-tensor-nonvanishing).

The derived tensor product `U ⊗ V` on `DerivedCategory (ModuleCat R)` is the canonical derived
monoidal structure of the project: `DerivedCategory.hasDerivedMonoidalCategory` (K-flat
derivability, from `ModuleCat.hasFunctorialFlatResolution`) and the monoidal structure
`DerivedMonoidal Qh` of `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`.
No monoidal structure is taken as a hypothesis.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w u

@[expose] public section

namespace DerivedCategory

/-- Let `R` be a commutative Noetherian local ring and `U`, `V` objects of the derived category
`D(R)` with cohomology bounded above and finitely generated in every degree. Then the derived
tensor product `U ⊗ V` (the canonical derived monoidal structure of `D(R)`) again has bounded
above, finitely generated cohomology, and `U ⊗ V = 0` if and only if `U = 0` or `V = 0`. No
finite Tor-dimension hypothesis is imposed.

Source: Stacks Project, More on Algebra, Tag 0DJE (lemma-tensor-pseudo-coherent), together
with the top-degree Nakayama argument (Tag 00DV)
(blueprint: lem-trf-local-derived-tensor-nonvanishing).

Proof (from the blueprint node):
1. If `U = 0` or `V = 0`, functoriality of the derived tensor and the zero object give
   `U ⊗ V = 0`. For the converse assume both are nonzero.
2. By the Noetherian pseudo-coherence criterion (Tag 066E) both `U` and `V` are
   pseudo-coherent; by Tag 0DJE (lem-trf-pseudocoherent-tensor-closure) `U ⊗ V` is
   pseudo-coherent, hence by the same criterion has bounded above, finitely generated
   cohomology.
3. Choose bounded-above finite free representatives. At the top term, if the top cohomology
   vanishes the preceding differential is split surjective with finite projective, hence free
   (Tag 0593, lem-trf-projective-over-local-free), kernel; cancel the contractible summand.
   Repeating reaches complexes `P`, `Q` with `P^i = 0` for `i > a`, `Q^j = 0` for `j > b`, and
   nonzero finitely generated `H^a(P) ≅ H^a(U)`, `H^b(Q) ≅ H^b(V)`.
4. All terms are flat, so by Tag 064K (lem-pc-module-bounded-flat-kflat) the derived tensor is
   the direct-sum total complex `T = Tot(P ⊗ Q)` with the Koszul differential.
5. By lem-trf-local-top-degree-tensor, `H^{a+b}(T) ≅ H^a(P) ⊗_R H^b(Q)`, which is nonzero by
   Nakayama (lem-trf-local-finite-module-tensor-nonzero). Hence `U ⊗ V ≠ 0`.
6. Combined with step 1 this proves `U ⊗ V = 0` iff `U = 0` or `V = 0`. -/
theorem local_derived_tensor_nonvanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (U V : DerivedCategory (ModuleCat.{u} R))
    (hU : ∃ n : ℤ, U.IsLE n)
    (hV : ∃ n : ℤ, V.IsLE n)
    (hUfin : ∀ i : ℤ, Module.Finite R
      ((homologyFunctor (ModuleCat.{u} R) i).obj U))
    (hVfin : ∀ i : ℤ, Module.Finite R
      ((homologyFunctor (ModuleCat.{u} R) i).obj V)) :
    (∃ n : ℤ, (U ⊗ V).IsLE n) ∧
      (∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj (U ⊗ V))) ∧
      (IsZero (U ⊗ V) ↔ IsZero U ∨ IsZero V) := by
  sorry

end DerivedCategory

end
