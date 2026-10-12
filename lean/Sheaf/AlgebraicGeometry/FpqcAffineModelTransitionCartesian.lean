module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Cover.Directed
import Sheaf.AlgebraicGeometry.FpqcMorphismsDescend

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A reconstructed transition between Cartesian local models is Cartesian.
Source: Stacks Project, Descent, Tag 02W3 (nested affine models), using Tag 02W0.
(blueprint: lem-galois-fpqc-affine-model-transition-cartesian)

Proof: Put P = W_B times_B U and let k : W_U -> P be induced by t and the
structural map to U. The Cartesian squares hp B and the two canonical
restriction squares X_U -> X_B and V_U -> V_B identify the pullback of P along
X_U -> U with V_U. The square hp U makes the same identification for W_U.
The reconstruction equation identifies the base change of k with the identity
under these identifications. Hence that base change is an isomorphism.
The map X_U -> U is fpqc by base change of hf. Full faithfulness of fpqc descent
of morphisms (Tag 02W0) descends the inverse of the base-changed k: its descent
compatibility follows by taking inverses in the compatibility equation for k.
Faithfulness makes both inverse composites identities. Thus k is an isomorphism,
and composing the defining pullback square for P with k gives the asserted
Cartesian square. This argument includes empty opens and objects. -/
theorem fpqc_affine_model_transition_cartesian
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X}
    (W : ∀ U : S.affineOpens, Over U.1.toScheme)
    (r : ∀ U : S.affineOpens,
      pullback V.hom (pullback.fst f U.1.ι) ⟶ (W U).left)
    (hp : ∀ U, IsPullback (r U) (pullback.snd V.hom (pullback.fst f U.1.ι))
      (W U).hom (pullback.snd f U.1.ι))
    {U B : S.affineOpens} (i : U ⟶ B)
    (t : (W U).left ⟶ (W B).left)
    (ht : t ≫ (W B).hom = (W U).hom ≫ S.directedAffineCover.trans i)
    (hr : Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i ≫
      r B = r U ≫ t) :
    IsPullback t (W U).hom (W B).hom (S.directedAffineCover.trans i) := by
  sorry

end AlgebraicGeometry
