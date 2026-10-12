module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

@[expose] public section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The affine ideal tensor comparison, before identifying its source with `I/I²`.
Source: Stacks Project, Morphisms, Lemma 01R3 (2), and Schemes, Tag 01I9.
(blueprint: lem-weil-pbc-affine-ideal-tensor-sections)

Proof: Put A = Γ(X,U) and V = i⁻¹U. Since i is a closed immersion, V is affine
and A → Γ(Z,V) is surjective. The first isomorphism theorem and r identify
Γ(Z,V) with R/I. The inclusion of i.ker.toModules is injective on U and its
range is the kernel of this section map, so its sections identify with I
semilinearly along r. The ideal module is quasi-coherent: it is the kernel of
the structure-module map to the closed-subscheme pushforward, and structure
modules, closed-immersion pushforwards, and kernels are quasi-coherent.
Apply exists_tensorPullback_affine_sections to i, U, V and this ideal module.
Transport its bijective comparison along the two section identifications.
This gives the displayed semilinear equivalence on I ⊗[R] (R/I). Its formula
on a ⊗ 1 is the pure-tensor formula of the affine comparison at b = 1.
Pushforward sections on U are pullback sections on V with scalars restricted
along i.app U, which gives exactly the scalar action in the displayed target. -/
theorem affine_ideal_tensor_sections {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
      ∀ (U : X.affineOpens) (R : Type v) [CommRing R]
        (r : R ≃+* Γ(X, U.1)) (I : Ideal R),
        I = RingHom.ker ((i.app U.1).hom.comp (r : R →+* Γ(X, U.1))) →
        ∃ e : LinearEquiv (r : R →+* Γ(X, U.1))
            (σ' := (r.symm : Γ(X, U.1) →+* R)) (I ⊗[R] (R ⧸ I))
            Γ((pushforward i).obj ((tensorPullback i).obj i.ker.toModules), U.1),
          ∀ (a : I) (s : Γ(i.ker.toModules, U.1)),
            i.ker.toModulesι.app U.1 s = r (a : R) →
            e (a ⊗ₜ[R] (1 : R ⧸ I)) =
              ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).app U.1 s := by
  sorry

end AlgebraicGeometry.Scheme.Modules
