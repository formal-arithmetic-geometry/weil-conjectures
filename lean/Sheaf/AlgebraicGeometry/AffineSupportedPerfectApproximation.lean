module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SupportedPerfectApproximation

import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.PerfectThickClosure
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Topology.Sheaves.Stalks

/-! # Supported perfect approximation on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Tag 08EQ,
`lemma-approximation-affine`, including its final assertion
(blueprint: lem-sfb-affine-supported-perfect-approximation).

The first theorem gives the approximation at a specified degree and closed support.
The second states the uniform supported-approximation property for every affine scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An m-pseudo-coherent quasi-coherent derived object on an affine scheme has a perfect
approximation supported on T when the complement has s affine opens and its cohomology
vanishes there in degrees at least m-s+1. Surjectivity means an epimorphism of sheaves.
Source: Stacks Project, Derived Categories of Schemes, Tag 08EQ,
`lemma-approximation-affine`
(blueprint: lem-sfb-affine-supported-perfect-approximation).

Proof:
1. The same local approximations show that m-pseudo-coherence implies a-pseudo-coherence
   for a >= m. Their bounded strictly perfect sources locally bound the cohomology above.
   Quasi-compactness of the affine scheme (lem-weil-pbc-affine-scheme-qcqs) gives a global
   bound t. Induct on max(0,t-m+1). If t < m, the zero perfect object and map suffice.
2. For t >= m, the top cohomology is finite type by
   lem-sfb-ringed-site-pseudocoherent-top-finite-type, and is quasi-coherent. Apply
   lem-weil-pbc-quasi-coherent-finite-type-affine to choose finitely many global generators.
3. For each generator apply lem-sfb-affine-supported-class-lift to F[t]: its required
   degrees q satisfy t+q >= m-s+1. Shift back and take the finite direct sum Q of the
   resulting perfect supported objects (lem-pc-perfect-thick-closure). The resulting
   q : Q -> F has zero cohomology above t and surjects in degree t, since the generators
   generate the sheaf by lem-weil-pbc-affine-tilde-gamma-adjunction. Empty generators give Q=0.
4. Complete q to Q -> F -> F1 -> Q[1]. The perfect object Q is (m+1)-pseudo-coherent,
   so lem-sfb-ringed-site-m-pseudocoherent-triangle makes F1 m-pseudo-coherent.
   The long exact sequence (lem-sf-derived-homology-long-exact) gives vanishing in degrees
   >= t. Exact stalks (lem-weil-pbc-module-stalk-exact) preserve the support bound.
   Quasi-coherent cohomology persists by lem-pc-supported-qcoh-triangulated. Induction at
   bound t-1 supplies a perfect supported approximation v1 : P1 -> F1.
5. Complete P1 -> F1 -> Q[1] to a triangle Q -> P -> P1 -> Q[1]. Apply TR3 to the
   rotated triangles, with maps v1 and the identity of Q[1], then shift back to obtain
   v : P -> F and a triangle morphism with other components identity and v1.
   Perfect thick closure makes P perfect. Exact stalks outside T make P supported on T.
6. On each stalk, for i >= m, lift the image in H^i(F1) through H^i(v1), then through
   H^i(P); adjust by H^i(Q) to lift any class of H^i(F). For i > m, a class in the kernel
   comes from H^i(Q); its zero image in H^i(F) comes from H^(i-1)(F1), which lifts through
   H^(i-1)(v1) since i-1 >= m. The upper exact sequence kills the original class.
   Thus v is surjective at m and bijective above m on stalks. The stalk criterion
   (lem-weil-pbc-module-iso-on-stalks), also applied to its cokernel, gives the assertion. -/
theorem exists_supported_perfect_approximation_of_isAffine
    (Y : Scheme.{u}) [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (T : Set Y) (hT : IsClosed T) (m : ℤ) (s : ℕ)
    (F : schemeDerivedCategory Y) (hF : schemeDerivedQCohProperty Y F)
    (hFm : IsMPseudoCoherent Y m F)
    (hcover : ∃ U : Fin s → Y.Opens,
      (∀ k : Fin s, IsAffineOpen (U k)) ∧ (⋃ k : Fin s, (U k : Set Y)) = Tᶜ)
    (hvanish : ∀ i : ℤ, m - (s : ℤ) + 1 ≤ i → ∀ y : Y, y ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj F).val.presheaf y))) :
    ∃ (P : schemeDerivedCategory Y) (v : P ⟶ F),
      IsPerfect Y P ∧
      (∀ (i : ℤ) (y : Y), y ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj P).val.presheaf y))) ∧
      (∀ i : ℤ, m < i →
        IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).map v)) ∧
      Epi ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) m).map v) := by
  sorry

/-- Every affine scheme satisfies the uniform supported perfect approximation property.
Source: Stacks Project, Derived Categories of Schemes, Tag 08EQ, final assertion
(blueprint: lem-sfb-affine-supported-perfect-approximation).

Proof: For a closed subset T with retrocompact complement, test retrocompactness on the
whole affine scheme. Its complement is quasi-compact and has a finite affine cover
(lem-pqf-finite-affine-cover-qc-open), say with s members. Choose r=s in
 def-sfb-supported-perfect-approximation-property. An (m-s)-pseudo-coherent object is
m-pseudo-coherent by the same local approximations, and vanishing outside T for i >= m-s
implies vanishing for i >= m-s+1. The preceding theorem supplies the required approximation
for every m and F, with this same r. Empty complements, s=0, and the empty scheme are included. -/
theorem hasSupportedPerfectApproximation_of_isAffine
    (Y : Scheme.{u}) [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))] :
    HasSupportedPerfectApproximation Y := by
  sorry

end AlgebraicGeometry.Scheme
