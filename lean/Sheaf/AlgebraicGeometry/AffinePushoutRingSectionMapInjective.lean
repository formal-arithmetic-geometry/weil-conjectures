module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.AffinePushoutRingSectionMap
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {U X : Scheme.{u}} (f : U ⟶ X)
/-- The canonical affine tensor section map has zero kernel.
Source: Stacks Project, Morphisms, Tag 01SB, affine reduction; Schemes, Tags 01IA and 01HV.
(blueprint: stage3-affine-pushout-ring-section-map-injective).

Proof: Put D = Γ(X,V), W = f⁻¹V and C = Γ(U,W). W is affine. The regular
module of A = f_*O_U, restricted along O_X → A, is f_*O_U as an O_X-module.
It is quasi-coherent: O_U is quasi-coherent and f is affine, hence qcqs.
Specialize affine_module_tensor_baseChange to the regular A-module. The inverse
image of a regular algebra module is the regular module of the inverse-image
algebra: the inverse-image unit respects addition and multiplication, and these
operations determine their extensions uniquely. Extension of that module along
`t` is the regular B-module; the inverse maps before sheafification are
z ⊗ a ↦ z*t(a) and z ↦ z ⊗ 1, and they remain inverse after sheafification.
Thus the cancellation comparison identifies the underlying O_U-module of B
with tensor pullback of f_*O_U. The affine pullback sections comparison gives a
bijective D-linear map C ⊗[D] C → B(W), after swapping its tensor factors.
Its unit formula sends 1 ⊗ d to t(η(d)); O_U-linearity sends c ⊗ d to
b(c)*t(η(d)). This is exactly affinePushoutSectionMap_tmul. Additive tensor
induction identifies the linear map with the constructed ring map on all
inputs. Its injectivity gives the claim. No surjectivity of the constructed
ring map is asserted here. If C is the zero ring, the tensor is zero and the
same argument applies; no nonzero or nonempty assumption is used. -/
theorem affinePushoutSectionMap_injective [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B)
    (t : TopCat.Sheaf.inverseImageRing f.base
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf) ⟶ B)
    (hpushout : IsPushout (tensorPullbackRingMap f)
      ((TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map
        (show X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf from ⟨f.c⟩)) b t)
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    Function.Injective (affinePushoutSectionMap f B b t hpushout V).hom := by
  sorry
end
end AlgebraicGeometry.Scheme.Modules
