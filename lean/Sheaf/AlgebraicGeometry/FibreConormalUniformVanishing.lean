module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.RingTheory.AssociatedGradedRing
import WeilConjectures.RingTheory.AssociatedGradedFiniteType
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import WeilConjectures.AlgebraicGeometry.GradedSerreVanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism

/-! # Uniform vanishing for the conormal layers of an ample closed fibre

Source: Stacks Project, Cohomology of Schemes, Tag 0D2M, proof of
lemma-ample-on-fibre with F = O_X, the graded-module paragraph.
(blueprint: lem-trf-fibre-conormal-uniform-vanishing).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- One nonnegative twist bound kills H^1 of every successive conormal layer.
The residue field is the quotient by the unique maximal ideal. Its spectrum map
has kernel the maximal-ideal sheaf; `comap g` is its extension J to X.
The quotient `formalModuleQuotient J 1 (idealSheafPower J.toModulesι n).1`
is J^n/(J J^n), hence J^n/J^(n+1), also for n = 0 since J^0 = O_X.
Natural exponents encode all the nonnegative integers in the statement.

Source: Stacks Project, Cohomology of Schemes, Tag 0D2M,
lemma-ample-on-fibre, proof with F = O_X, coherent.tex lines 6013-6044.
(blueprint: lem-trf-fibre-conormal-uniform-vanishing).

Proof, following the node's five steps:
1. A and its residue field are Noetherian. Their spectra are Noetherian by affine
quasi-compactness, and properness makes X and its closed fibre Noetherian
(lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-proper-fp-permanence). The residue quotient spectrum is a closed immersion
(lem-weil-pbc-spec-quotient-closed-immersion); its kernel is the maximal-ideal sheaf
(def-sbc-closed-immersion-ideal-sheaf,
lem-weil-pbc-quasi-coherent-ideal-closed-subscheme). Base change gives the closed
fibre with ideal J = m O_X (lem-pc-closed-subscheme-base-change-ideal-image,
lem-pc-ideal-sheaf-comap-affine-extension).
2. Set Q_n = J^n/J^(n+1). The powers are quasi-coherent
(lem-weil-pbc-ideal-times-quasi-coherent-affine-sections). The structure sheaf is
coherent by pqf-lem-coherent-ft-locnoeth. Coherent kernels and cokernels make Q_n
coherent (lem-weil-pbc-coherent-kernel-cokernel-locnoeth). Multiplication by J kills
Q_n, so closed-immersion coherent equivalence realizes Q_n as i_*G_n with G_n
coherent on the closed fibre, G_0 = O_(X_0)
(lem-weil-pbc-closed-immersion-coherent-equivalence).
3. Let B = gr_m A. It is a finite type graded k-algebra
(lem-weil-pbc-associated-graded-ring-structure,
lem-weil-pbc-associated-graded-finite-type). Multiplication of representatives gives
B_r actions G_n -> G_(n+r): changing a representative changes the product by the
next ideal power. Restriction, addition, the unit and associativity are inherited
from the structure rings. Full faithfulness of the closed-immersion equivalence
transports this action to the fibre. Since Spec k has one point, this makes the
sum G of the G_n a graded module over g_0^*B-tilde. Finite partial sums are
quasi-coherent, and so is their directed colimit G
(lem-weil-pbc-quasi-coherent-module-direct-sum,
lem-weil-pbc-quasi-coherent-module-colimit-affine-sections). On affine charts,
(m R)^n = m^n R, so G is generated by 1 in degree zero
(lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).
4. Put L = i^*N, invertible by lem-weil-pbc-invertible-pullback-tensor and ample
by hypothesis. Apply lem-weil-pbc-formal-systems-graded-vanishing to G to obtain
one d_0 with H^1(G tensor L^d) = 0 for all d >= d_0. The degree inclusion and
projection make G_n a retract of G. Tensor and cohomology preserve their composite
identity, so H^1(G_n tensor L^d) = 0 for every n with the same bound
(pqf-def-cohomology), without interchanging cohomology and infinite sums.
5. The closed-immersion projection formula and cohomology comparison identify
H^1(X, Q_n tensor N^d) with H^1(X_0, G_n tensor i^*(N^d))
(lem-pc-closed-immersion-coherent-cohomology). Iterating the tensor-pullback
comparison, including the unit case, identifies i^*(N^d) with L^d and makes all
powers invertible (lem-weil-pbc-invertible-pullback-tensor). Step 4 gives the
claimed vanishing for all n and d with the same bound. -/
theorem fibre_conormal_uniform_vanishing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [IsProper g] (N : X.Modules) [N.IsInvertible]
    (hN : @IsAmple
      (Limits.pullback g (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))))
      ((tensorPullback (Limits.pullback.fst g (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))))).obj N)
      ((invertible_pullback_tensor (Limits.pullback.fst g (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))))).1 N).2) :
    ∃ d₀ : ℕ, ∀ n d : ℕ, d₀ ≤ d →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (formalModuleQuotient
          ((Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))).ker.comap g) 1
          (Scheme.idealSheafPower
            ((Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))).ker.comap g).toModulesι n).1
          ⊗ N.tensorPow d)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
