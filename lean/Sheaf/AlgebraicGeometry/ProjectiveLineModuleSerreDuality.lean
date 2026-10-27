module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.ScalarCupCoefficientNaturality
import Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility
import Sheaf.Paper.ModuleCohomologyCupProduct
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Functorial Serre duality for invertible modules in arbitrary dimension

Source: Stacks Project, Duality for Schemes, Tags 0FVV, 0FVX and 0FW0;
Limits of Schemes, Tag 0E7D
(blueprint: lem-sfb-projective-line-module-serre-duality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The negative-degree convention in Serre duality: in nonnegative degree use the
recorded right-derived global sections and restrict scalars along the structure map;
in negative degree use the zero vector space and its constant functor.
Source: Stacks Project, Tag 0FVV, formula (5), applied to a module in degree zero
(blueprint: lem-sfb-projective-line-module-serre-duality). -/
noncomputable def lineSerreCohomology {F : Type u} [Field F] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of F)) (r : ℤ) : Y.Modules ⥤ ModuleCat.{u} F :=
  if 0 ≤ r then
    RingedSpace.moduleCohomology Y.toRingedSpace r.toNat ⋙
      ModuleCat.restrictScalars (scalarMap f ⊤)
  else
    (Functor.const Y.Modules).obj (ModuleCat.of F (Fin 0 → F))

/-- Functorial Serre duality for every invertible module on a smooth projective scheme
of pure dimension `n`. The canonical module is the top exterior power of the actual
relative differential sheaf. The same family of linear equivalences works for every
morphism of invertible modules, including zero and noninvertible morphisms.

Source: Stacks Project, Duality for Schemes, Tags 0FVV (5),(7), 0FVX and 0FW0;
Limits of Schemes, Tag 0E7D; Cohomology of Schemes, Tag 01XK
(blueprint: lem-sfb-projective-line-module-serre-duality).

Proof:
1. Projectivity implies properness by lem-kun-projective-implies-proper; hence the
structure morphism is separated, of finite type and quasi-compact. Smoothness of
relative dimension n makes the differential sheaf locally free of rank n by
lem-sc-smooth-omega-finite-locally-free. Wedges of local bases (the empty wedge for
n = 0) trivialize its top exterior power. Dual local frames trivialize the dual of
any invertible E, so omega tensor E-dual is invertible and quasi-coherent by
pqf-def-coherent.
2. For j <= n put i = n-j. Apply lem-sfb-smooth-proper-coherent-trace-pairing to E.
Its single trace and perfect cup-evaluation pairing give an isomorphism from
H^j(E-dual tensor omega) to the dual of H^i(E). Precompose with cohomology of the
symmetry omega tensor E-dual -> E-dual tensor omega. This defines theta.
3. For v : E -> E', evaluation satisfies ev(e, v-dual(lambda') tensor w) =
lambda'(v(e)) w. Coefficient naturality of the ordinary cup product follows from
lem-sc-scalar-cup-coefficient-naturality and lem-sc-scalar-cup-module-cup-compatibility:
the identical signs in source and target cancel. Applying the same trace gives
P_E(x, H^j(v-dual tensor id)y) = P_E'(H^i(v)x, y). Tensor symmetry commutes with
v-dual. Substitution gives the asserted pointwise naturality for theta.
4. For j > n, lem-sfb-proper-quasicoherent-fibre-dimension-vanishing applied to
omega tensor E-dual gives zero higher direct image. By
lem-pc-cohomology-sections-affine-base its cohomology is zero. The complementary
degree is negative, hence zero by convention. The unique map between these zero
spaces is an isomorphism, and all naturality equalities hold.
5. In the complementary nonnegative range both factors of the trace pairing are
finite dimensional; a finite dual basis proves the same for the dual space.
Above n both sides are zero. For n = 0 the same construction uses omega = O_Y.
For the empty scheme all groups are zero. Neither the pairing nor the vanishing
argument assumes connectedness or geometric integrality. -/
theorem projective_lineModule_serreDuality
    (F : Type u) [Field F] (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of F))]
    (n : ℕ) [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of F))]
    [IsProjective (Y ↘ Spec (CommRingCat.of F))] :
    ∃ θ : ∀ (E : Y.Modules) [IsInvertible E] (j : ℕ),
      (scalarCohomology (Y ↘ Spec (CommRingCat.of F))
        (exteriorSheaf (Y ↘ Spec (CommRingCat.of F)).relativeDifferentials n ⊗ dual E) j)
        ≃ₗ[F] Module.Dual F
          ((lineSerreCohomology (Y ↘ Spec (CommRingCat.of F))
            ((n : ℤ) - (j : ℤ))).obj E),
      (∀ (E : Y.Modules) [IsInvertible E] (j : ℕ),
        FiniteDimensional F (scalarCohomology (Y ↘ Spec (CommRingCat.of F))
          (exteriorSheaf (Y ↘ Spec (CommRingCat.of F)).relativeDifferentials n ⊗ dual E)
          j) ∧
        FiniteDimensional F (Module.Dual F
          ((lineSerreCohomology (Y ↘ Spec (CommRingCat.of F))
            ((n : ℤ) - (j : ℤ))).obj E))) ∧
      (∀ (E E' : Y.Modules) [IsInvertible E] [IsInvertible E'] (v : E ⟶ E')
        (j : ℕ)
        (z : scalarCohomology (Y ↘ Spec (CommRingCat.of F))
          (exteriorSheaf (Y ↘ Spec (CommRingCat.of F)).relativeDifferentials n ⊗ dual E')
          j)
        (x : (lineSerreCohomology (Y ↘ Spec (CommRingCat.of F))
          ((n : ℤ) - (j : ℤ))).obj E),
        θ E j (scalarCohomologyMap (Y ↘ Spec (CommRingCat.of F))
          (exteriorSheaf (Y ↘ Spec (CommRingCat.of F)).relativeDifferentials n ◁ dualMap v)
          j z) x =
        θ E' j z (((lineSerreCohomology (Y ↘ Spec (CommRingCat.of F))
          ((n : ℤ) - (j : ℤ))).map v).hom x)) ∧
      (∀ (E : Y.Modules) [IsInvertible E] (j : ℕ), n < j →
        Subsingleton (scalarCohomology (Y ↘ Spec (CommRingCat.of F))
          (exteriorSheaf (Y ↘ Spec (CommRingCat.of F)).relativeDifferentials n ⊗ dual E)
          j)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
