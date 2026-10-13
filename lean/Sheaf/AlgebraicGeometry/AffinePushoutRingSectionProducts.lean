module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.AffinePushoutRingSectionComm
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {U X : Scheme.{u}} (f : U ⟶ X)
/-- Affine pushout sections are finite sums of products of the two section legs.
Source: Stacks Project, Morphisms, Tag 01SB, affine reduction; Schemes, Tags 01IA and 01HV.
(blueprint: stage3-affine-pushout-ring-section-products).

Proof: Let W = f⁻¹V, D = Γ(X,V), C = Γ(U,W), and A = f_*O_U. Since f is
affine, W is affine and f_*O_U is quasi-coherent as an O_X-module. Use
pushout scalar-extension cancellation on the regular A-module. Its inverse
image is the regular module of f⁻¹A, since the inverse-image unit respects
ring operations. Extension along t identifies this with the regular B-module:
the maps z ⊗ a ↦ z*t(a) and z ↦ z ⊗ 1 are inverse by the balancing relation,
and descend through sheafification. The affine pullback section theorem now
gives a surjective linear map C ⊗[D] C → B(W). The cancellation unit formula
and O_U-linearity show that its pure-tensor value is b(c)*t(η(d)). Every tensor
is a finite sum of pure tensors: prove this by tensor induction, using the
empty list for zero, a singleton for a pure tensor, and concatenation for
addition. A preimage of a given section therefore gives the required list.
This uses only surjectivity of the linear comparison and makes no assertion
about uniqueness or tensor relations among the products. The zero ring and
empty W are covered by the empty-list case. -/
theorem affinePushoutSection_products [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B)
    (t : TopCat.Sheaf.inverseImageRing f.base
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf) ⟶ B)
    (hpushout : IsPushout (tensorPullbackRingMap f)
      ((TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map
        (show X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf from ⟨f.c⟩)) b t)
    (V : X.Opens) (hV : IsAffineOpen V) :
    ∀ z : B.obj.obj (op (f ⁻¹ᵁ V)),
      ∃ l : List (Γ(U, f ⁻¹ᵁ V) × Γ(U, f ⁻¹ᵁ V)),
        z = (l.map fun x ↦ (b.hom.app (op (f ⁻¹ᵁ V))).hom x.1 *
          affinePushoutSectionDelta f B t V x.2).sum := by
  sorry
end
end AlgebraicGeometry.Scheme.Modules
