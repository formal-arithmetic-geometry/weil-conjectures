/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Scalar-compatible flat base change for additive first cohomology -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- The first cohomology comparison for additive structure sheaves preserves scalars
and the canonical base-change map. No Frobenius or constant-sheaf assertion is made.
Source: Stacks Project, Tags 0A3P (first sentence of proof), 02KH (flat base change),
03P2 (quasi-coherent comparison), and 02O6 (proper coherent finiteness).
(blueprint: lem-pbc-additive-scalar-base-change)

Proof: The natural section equivalences identify G and G' with the lifted additive
structure sheaves. Multiplication by the structural image of c is additive and
commutes with restriction, so defines μ on each sheaf. Applying additive cohomology
to the zero, identity, sum and product relations supplies the actual scalar action
on H¹. Compare it with coherent H¹(C,O_C) using the etale/Zariski comparison;
proper coherent finiteness makes the resulting k-module V finite-dimensional.
On the base change, use the same comparison and the canonical flat base-change
isomorphism, with tensor factors interchanged, to obtain b'. The two scalar actions
agree with multiplication on coherent cohomology by naturality in module maps.
For the last formula, compute on a finite affine cover of C and its pulled-back
cover. The adjoint section formula for q says precisely that its cochain map is
structural pullback, hence is s ↦ 1 tensor s under the affine-section tensor
identifications. Flat tensor product preserves kernels and images. The Cech
comparison therefore induces the displayed equality on H¹, in the specified Ext
model, using the natural Ext/derived comparison. If C has dimension zero,
coherent H¹ is zero and all these formulas still hold. This argument uses neither
Artin--Schreier exactness nor semilinear Frobenius invariance. -/
theorem exists_additive_scalar_base_change
    {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] [IsProper f]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : C'.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (ha' : ∀ (U V : C'.Etaleᵒᵖ) (g : U ⟶ V) (x : G'.obj.obj U),
      a' V (G'.obj.map g x) = g.unop.left.appTop (a' U x))
    (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
    (hq : (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι').homEquiv
            G G' q).hom.app U x) =
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x))) :
    ∃ (V : ModuleCat.{u + 1} k) (_ : FiniteDimensional k V)
      (b : Sheaf.H G 1 ≃+ V) (b' : Sheaf.H G' 1 ≃+ (k' ⊗[k] V)),
      (∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : Sheaf.H G 1,
          b (Sheaf.H.map μ 1 x) = c • b x) ∧
      (∀ c : k', ∃ μ : G' ⟶ G',
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) ∧
        ∀ x : Sheaf.H G' 1,
          b' (Sheaf.H.map μ 1 x) = c • b' x) ∧
      ∀ x, b' (Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)) = 1 ⊗ₜ[k] b x := by sorry

end AlgebraicGeometry.IsCurve
