module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.AlgebraicGeometry.UniformInverseAffineSectionsBound
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherent

/-! # Extending perfect tensor tests to pseudo-coherent tensor tests

Source: Stacks Project, Derived Categories of Schemes, Tag 0CSH, `lemma-perfect-enough`
(blueprint: lem-sfb-perfect-to-pseudocoherent-tensor-tests).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wΓ wA

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- On a qcqs scheme over A, pseudo-coherence of all perfect tensor tests for a bounded-above
quasi-coherent K implies pseudo-coherence of every pseudo-coherent tensor test.
Derived sections are followed by exact restriction along the structure map A → Γ(X, O_X).
Source: Stacks Project, Derived Categories of Schemes, Tag 0CSH, `lemma-perfect-enough`
(blueprint: lem-sfb-perfect-to-pseudocoherent-tensor-tests).

Proof:
1. Apply lem-pc-uniform-inverse-affine-sections-bound to X → Spec Z. Combine its bound
N > 0 with lem-pc-unbounded-derived-functor-cohomological-bound: an upper cohomology bound t
for a quasi-coherent complex gives the bound t + N - 1 for derived sections. Global sections
commute with countable products. The A-valued and group-valued section complexes have the
same underlying abelian groups, so the vanishing bound holds over A as well.
2. Fix a pseudo-coherent E and an integer m. Set a = m - N - 1 - b. By
lem-sfb-pseudocoherent-perfect-approximation choose a perfect P → E which is an isomorphism
on H^i for i > a and surjective for i = a. Complete it to P → E → C → P[1]. By
lem-sc-pseudo-coherent-qcoh and lem-pc-supported-qcoh-triangulated, all vertices have
quasi-coherent cohomology.
3. The cohomology sequence (lem-sp-long-exact-of-triangle) gives H^i(C) = 0 for i ≥ a:
the first map into H^i(E) is surjective and H^{i+1}(P) → H^{i+1}(E) is injective.
4. Use def-sbc-standard-tstructure-derived-category to take representatives zero above a-1
and b. Apply lem-pc-kflat-bounded-flat-replacement and lem-pc-bounded-above-flat-kflat to
replace them by K-flat flat complexes with the same term bounds. Their total tensor has
zero terms in degrees greater than a-1+b. Hence H^j(C ⊗ K) = 0 for j ≥ m-N-1.
5. By lem-pc-canonical-derived-tensor-qcoh this tensor has quasi-coherent cohomology.
Step 1 therefore gives H^i(RΓ(X, C ⊗ K)) = 0 for i > m-3, in particular for i ≥ m-1.
6. Choose a flat-term K-flat representative of K by lem-weil-pbc-site-derived-tensor-descent.
Tensoring with it is triangulated (lem-weil-pbc-kflat-fixed-tensor-triangulated), and derived
sections are triangulated (lem-pc-right-derived-functor-triangulated). The resulting triangle
and lem-sp-long-exact-of-triangle show that RΓ(X, P ⊗ K) → RΓ(X, E ⊗ K) induces cohomology
isomorphisms in every degree i ≥ m.
7. The perfect-test hypothesis makes the source pseudo-coherent. By
lem-pc-ring-pseudo-coherent-iff-all-m it has a finite-free m-approximation. Compose that
approximation with the arrow in step 6; its cohomology maps are isomorphisms for i > m and
surjective for i = m. Thus the target is m-pseudo-coherent by def-pc-ring-m-pseudo-coherent.
As m was arbitrary, lem-pc-ring-pseudo-coherent-iff-all-m gives pseudo-coherence. -/
theorem isPseudoCoherent_tensor_sections_of_perfect_tests
    (A : CommRingCat.{u}) (X : Scheme.{u}) (p : X ⟶ Spec A)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{wΓ}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (hBound : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj K))
    (hTests : ∀ P : schemeDerivedCategory X, Scheme.IsPerfect X P →
      DerivedCategory.IsPseudoCoherent
        ((schemeDerivedGlobalSections X ⋙
          (affineGlobalSectionsRestriction p).mapDerivedCategory).obj (P ⊗ K))) :
    ∀ E : schemeDerivedCategory X, Scheme.IsPseudoCoherent X E →
      DerivedCategory.IsPseudoCoherent
        ((schemeDerivedGlobalSections X ⋙
          (affineGlobalSectionsRestriction p).mapDerivedCategory).obj (E ⊗ K)) := by
  sorry

end AlgebraicGeometry
