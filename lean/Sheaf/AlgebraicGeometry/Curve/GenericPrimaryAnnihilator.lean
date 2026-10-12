module
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.FieldTheory.OpenSubgroupFixedField
import Sheaf.RepresentationTheory.SylowModuleFiltration
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace AlgebraicGeometry.IsConnectedCurve
/-- A finite primary geometric stalk yields an ell-power annihilator.
Proof: the finite primary stalk has a largest exponent among the exponents
needed to kill its elements. The stalk functor is faithful on this site, so
the corresponding scalar multiple of the identity of `M` is zero.
(blueprint: lem-sc-generic-primary-annihilator) -/
theorem exists_primary_annihilator
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (hprimary : IsPGroup ℓ (Multiplicative (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))) :
    ∃ (e : ℕ), (ℓ ^ e) • 𝟙 M = 0 := by
  sorry
end AlgebraicGeometry.IsConnectedCurve
