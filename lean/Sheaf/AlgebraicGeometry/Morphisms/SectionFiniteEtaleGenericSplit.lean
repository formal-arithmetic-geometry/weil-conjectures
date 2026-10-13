/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
import Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull

/-! # Splitting the section pullback of a finite étale generic model
Source: Stacks Project, Tags 0EYJ and 0BQM.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite étale model of a generic torsor splits after pullback to the section on U.
Source: Stacks Project, Tag 0EYJ, the section fibre calculation; Tag 0BQM, full faithfulness.
(blueprint: lem-sbc-section-finite-etale-generic-split)

Proof: The nonempty open U of the normal integral S is normal integral with function field
k(S). The section b identifies the generic fibre of its PA pullback with the pullback of Z
along sη. Choose the rational point in hZ. Its G-translates give the canonical map from
G copies of Spec k(S) to this fibre. The torsor isomorphism, pulled back along that point,
shows this map is an isomorphism, including for disconnected torsors. Both the section
pullback and the constant G-indexed cover are finite étale over U. Extend the generic
isomorphism and its inverse by finiteEtale_normalIntegral_generic_hom_full. Its uniqueness
shows that both composites equal the identities. The extensions respect U, giving the
claimed equation for the isomorphism. No group-order assumption is used. U may equal S;
the trivial group gives a single copy. The generic point hypothesis excludes empty U. -/
theorem GaloisCover.section_finiteEtale_generic_split {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S)
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (b : U.toScheme ⟶ (c ⁻¹ᵁ U).toScheme)
    (hb : b ≫ (c ⁻¹ᵁ U).ι = U.ι ≫ σ) :
    ∃ e : (∐ fun _ : G ↦ U.toScheme) ≅ pullback PA.obj.hom b,
      e.hom ≫ pullback.snd PA.obj.hom b = Sigma.desc (fun _ : G ↦ 𝟙 U.toScheme) := by sorry

end AlgebraicGeometry.Scheme
