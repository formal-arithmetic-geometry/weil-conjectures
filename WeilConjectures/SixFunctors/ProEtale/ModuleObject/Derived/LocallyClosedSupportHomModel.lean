/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyClosedAmbientSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyClosedSupportFiniteTor

/-! # Locally closed support and internal Hom

Source: current blueprint, internal-Hom stability proof, Steps 8--10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private def supportAdjointComparison
    {S X : Scheme.{u}}
    (F : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)) ⥤ DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (R : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤ DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
    (ambient : F ⊣ R)
    (h : ∀ M, localizingClosureProEtale Λ S M → localizingClosureProEtale Λ X (F.obj M))
    (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ S).FullSubcategory)
    (adj : (localizingClosureProEtale Λ X).lift
      ((localizingClosureProEtale Λ S).ι ⋙ F) (fun M ↦ h M.obj M.property) ⊣ G)
    (N : (localizingClosureProEtale Λ X).FullSubcategory)
    (hR : localizingClosureProEtale Λ S (R.obj N.obj)) :
    (⟨R.obj N.obj, hR⟩ : (localizingClosureProEtale Λ S).FullSubcategory) ≅ G.obj N := by
  let T : (localizingClosureProEtale Λ S).FullSubcategory := ⟨R.obj N.obj, hR⟩
  let LF := (localizingClosureProEtale Λ X).lift
    ((localizingClosureProEtale Λ S).ι ⋙ F) (fun M ↦ h M.obj M.property)
  let H := LF.op ⋙ yoneda.obj N
  let e : H.RepresentableBy T :=
    { homEquiv := fun {B} ↦
        ((localizingClosureProEtale Λ S).fullyFaithfulι.homEquiv
          (X := B) (Y := T)) |>.trans
          ((ambient.homEquiv B.obj N.obj).symm) |>.trans
          ((localizingClosureProEtale Λ X).fullyFaithfulι.homEquiv
            (X := LF.obj B) (Y := N)).symm
      homEquiv_comp := by
        intro B B' f g
        apply (localizingClosureProEtale Λ X).ι.map_injective
        change (ambient.homEquiv B.obj N.obj).symm (f.hom ≫ g.hom) =
          F.map f.hom ≫ (ambient.homEquiv B'.obj N.obj).symm g.hom
        exact ambient.homEquiv_naturality_left_symm f.hom g.hom }
  exact e.uniqueUpToIso (adj.representableBy N)

/-- The support model of a locally closed exceptional adjoint, with its ambient
internal-Hom formula and constructible finite-Tor preservation on the given object.
Source: internal-Hom stability proof, Steps 8--10
(blueprint: lem-sfb-locally-closed-support-hom-model).

Proof: For the closed immersion i choose the complementary open v. The ambient closed
support right adjoint RΓ_Z has the fiber formula i^*fib(L -> Rv_*v^*L). Pullback and
direct-image stability and triangulated closure therefore put this object in Dctf.
Compose RΓ_Z with j^* to obtain T. The ambient adjunctions i_* ⊣ RΓ_Z and j_! ⊣ j^*
compose to an ambient adjunction for F=i_*j_!. The compactification formula and
coproduct preservation show that F preserves the localizing closures. Brown
representability gives the restricted right adjoint G. Take N to be L with the
localizing membership induced by its Dctf membership. The object T also lies in the
full localizing closure, by its Dctf membership. For every object B of that closure,
the ambient adjunction and the restricted adjunction identify Hom(B,T) and
Hom(B,G(N)). Transposing their counits gives inverse maps by the triangle identities,
so G(N) is isomorphic to T and lies in Dctf. This comparison requires no assertion
that the ambient support functor preserves the entire localizing closure.
The ambient closed and open internal-Hom isomorphisms give successively
Hom_X(i_*j_!P,L) = i_*Hom_Z(j_!P,RΓ_Z L)
= i_*Rj_*Hom_S(P,j^*RΓ_Z L). The derived pushforward composition comparison and the
exactness of closed direct image identify the last object with Ra_*Hom_S(P,G(N)).
The equality a=j≫i identifies the maps. These are identities in the full ambient
derived categories, not merely identities of global Hom or tests on the localizing
closure. Empty strata give the zero adjoint and zero formula; the identity immersion
gives the identity adjunction and formula. -/
theorem locallyClosed_support_hom_model
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (L : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hL : constantModelBoundedConstructible Λ X L ∧ DerivedCategory.finiteTorAmplitude _ L)
    (S Z : Scheme.{u}) (a : S ⟶ X) (j : S ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] (ha : a = j ≫ i) :
    let F := (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
      (lowerStar Λ i).rightDerivedFunctor
    ∃ (h : ∀ M, localizingClosureProEtale Λ S M →
        localizingClosureProEtale Λ X (F.obj M))
      (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
        (localizingClosureProEtale Λ S).FullSubcategory),
      Nonempty ((localizingClosureProEtale Λ X).lift
        ((localizingClosureProEtale Λ S).ι ⋙ F) (fun M ↦ h M.obj M.property) ⊣ G) ∧
      ∃ N : (localizingClosureProEtale Λ X).FullSubcategory, N.obj = L ∧
        (constantModelBoundedConstructible Λ S (G.obj N).obj ∧
          DerivedCategory.finiteTorAmplitude _ (G.obj N).obj) ∧
        ∀ P : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))),
      Nonempty (((derivedHom Λ X).obj (op (F.obj P))).obj L ≅
          (lowerStar Λ a).rightDerivedFunctor.obj
            (((derivedHom Λ S).obj (op P)).obj (G.obj N).obj)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  dsimp
  obtain ⟨h, G, adj⟩ := locallyClosed_support_adjunction Λ ℓ k hΛ S Z a j i ha
  obtain ⟨R, ⟨adjR⟩, hformula⟩ := locallyClosed_ambient_support Λ a j i ha
  have hT := locallyClosed_support_finiteTor Λ ℓ k hΛ j i R adjR L hL
  have hN : localizingClosureProEtale Λ X L := by
    intro Q hQ hPQ
    exact hPQ L hL
  have hRT : localizingClosureProEtale Λ S (R.obj L) := by
    intro Q hQ hPQ
    exact hPQ (R.obj L) hT
  let N : (localizingClosureProEtale Λ X).FullSubcategory := ⟨L, hN⟩
  obtain ⟨adjG⟩ := adj
  let e := (localizingClosureProEtale Λ S).ι.mapIso
    (supportAdjointComparison Λ _ R adjR h G adjG N hRT)
  have : (constantModelBoundedConstructible Λ S).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ S).2.1
  refine ⟨h, G, ⟨adjG⟩, N, rfl, ?_, ?_⟩
  · exact ObjectProperty.prop_of_iso
      (constantModelBoundedConstructible Λ S ⊓ DerivedCategory.finiteTorAmplitude _) e hT
  · intro P
    obtain ⟨eP⟩ := hformula P L
    exact ⟨eP ≪≫ (lowerStar Λ a).rightDerivedFunctor.mapIso
      (((derivedHom Λ S).obj (op P)).mapIso e)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
