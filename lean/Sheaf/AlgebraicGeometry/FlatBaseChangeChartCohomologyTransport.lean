/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.ResolutionSectionClassOpenRestriction
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison

/-! # Cohomology transport from the affine scalar-extension chart

Source: Stacks Project, Tags 02KH and 01FB.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- Transport along the affine chart identifies its unit map with open restriction
of the specified coefficient h-map. No Leray edge or higher image is involved.
Source: Stacks Project, Tag 02KH, first paragraph of the proof; Tag 01FB,
Remark 20.14.2; Tags 0096 (Lemma 6.26.2) and 0097 (Lemma 6.26.3).
(blueprint: new-flat-base-change-chart-cohomology-transport)

Proof: Write U0 = f inverse V and L = f' inverse W. The affine identifications
V = Spec Gamma(V) and W = Spec Gamma(W), together with the equality hAlgebra,
identify U0 times Spec Gamma(W) over Spec Gamma(V) with L. Construct the two inverse
maps by the fibre-product universal property, and check the inverse identities by
the two projections. Under this scheme isomorphism pullback composition identifies
the chart coefficient N_B with G restricted to L, where G = tensorPullback(g') F.
The tensor pullback adjunction and ordinary pullback adjunction determine the same
pullback functor up to their unique adjunction-compatible isomorphism. Composing
this with restrictFunctorIsoPullback gives the coefficient identification.
Apply module cohomology along the scheme isomorphism and this coefficient iso;
functoriality and the two inverse identities give an additive equivalence t.
The projection to Spec Gamma(W) equals the restricted f' followed by W.toSpecGamma,
so naturality for multiplication by a global section gives t's scalar equation.
To prove the last equation, transpose both coefficient maps across the pullback
adjunction. The composite-unit identities reduce their equality to D.unit_square
restricted to L. The restriction composition iso used in cohomologyOpenRestriction
is exactly the coefficient comparison in this calculation. Apply source and target
naturality and composition of moduleCohomologyFMap to this equality. This gives the
unit formula without inverting the unit h-map. The fibre-product and adjunction
arguments cover empty opens, degree zero and zero coefficients as well. -/
theorem exists_flatBaseChange_chart_cohomology_transport
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V) (D : FlatBaseChangeOpenChoices f g F I J V)
    [Algebra Γ(S, V) Γ(S', W)]
    (hAlgebra : algebraMap Γ(S, V) Γ(S', W) = (g.appLE V W eVW).hom) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (pullback (f ⁻¹ᵁ V).ι).obj F
    let T := baseChangedScheme (S := Γ(S', W)) h
    let A := baseChangedModule (S := Γ(S', W)) h N
    let C := RingedSpace.moduleCohomology T.toRingedSpace p
    let G := (tensorPullback (pullback.snd g f)).obj F
    let U := (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
    let L := (pullback.fst g f) ⁻¹ᵁ W
    let e : L ≤ U := by
      change (pullback.fst g f) ⁻¹ᵁ W ≤ (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
      rw [flatBaseChangeOpenEquality f g V]
      exact (pullback.fst g f).preimage_mono eVW
    let M := (restrictFunctor L.ι).obj G
    let C' := RingedSpace.moduleCohomology L.toScheme.toRingedSpace p
    let k := (pullback.fst g f).resLE W L le_rfl ≫ W.toSpecΓ
    ∃ t : C.obj A ≃+ C'.obj M,
      (∀ (a : Γ(S', W)) (y : C.obj A),
        t ((C.map (A.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
          (baseChangeSnd (S := Γ(S', W)) h).appTop).hom a))).hom y) =
        ((C'.map (M.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫ k.appTop).hom a))).hom
          (t y))) ∧
      (∀ x : (RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
          ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F),
        t (moduleCohomologyFMap (baseChangeFst (S := Γ(S', W)) h)
          (baseChangeUnit (S := Γ(S', W)) h N) p
          (((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).map
            ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).hom).hom x)) =
        cohomologyOpenRestriction G U L e p
          (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V) U le_rfl)
            D.psi p x)) := by sorry

end AlgebraicGeometry.Scheme.Modules
