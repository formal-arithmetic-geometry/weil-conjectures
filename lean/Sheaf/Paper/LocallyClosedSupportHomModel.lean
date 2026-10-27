/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

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
            (((derivedHom Λ S).obj (op P)).obj (G.obj N).obj)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
