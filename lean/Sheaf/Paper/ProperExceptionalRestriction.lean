/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.ExceptionalInverseImageExistence
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Restriction of the Brown adjoint for a proper morphism

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-existence-ii,
sk-cor-existence-ii-restriction.md and its proof
(blueprint: det-cor-existence-ii-restriction).

The compact-support functor and its right adjoint are those of sk-thm-existence.
The membership witness `h` and adjunction specify those already existing objects.
The comparison on the localizing closures is a natural isomorphism. The equalities
through the full inclusions specify both restricted functors on objects and maps.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For proper `p`, the chosen compactification lower shriek is naturally isomorphic
on the localizing closures to the restriction of the ambient total right derived
pushforward. That pushforward preserves Dctf, and the given Brown right adjoint
restricts to a right adjoint on Dctf. The existential `hSY` only witnesses the full
inclusion of Dctf in its defining localizing intersection. No regularity or Gorenstein
condition is imposed on finite coefficients.

Source: blueprint main-20261015, det-cor-existence-ii-restriction, clauses (1)--(2)
(blueprint: det-cor-existence-ii-restriction).

Proof:
1. The standing target Y is qcqs by lem-weil-pbc-qcqs-over-affine. Properness
   (def-weil-proper-morphism) includes separatedness and finite type. Thus
   (id_X,p) is a compactification (sk-def-nagata-sketch-data); id_X is a
   quasi-compact open immersion since it preserves every affine open.
2. Left Kan extension along the identity and sheafification give id_! = id
   (def-sfb-finite-extension-by-zero). The analogous calculation gives id^* = id
   (def-sfb-finite-upper-star). The forward direct-image compositor
   (def-sfb-finite-lower-star-comp) is the identity under the fibre-product
   identification. Its inverse-image mate (def-sfb-finite-upper-star-comp),
   using def-sfb-finite-upper-lower-star-adjunction, def-weil-pbc-composite-adjunction
   and def-weil-pbc-adjunction-mate, is the identity by the triangle identity
   epsilon_F(A) F(eta_A) = id. The coefficient compositor and coefficient map
   (sk-def-sfb-coefficient-morphisms, sk-def-sfb-pullback-from-point-comp) are
   therefore identities. The projection-formula map of lem-sfb-open-projection-formula
   is the transpose of the identity Kan-extension unit. Thus the module action
   in def-sfb-module-open-lower-shriek and def-sfb-module-linear-open-lower-shriek
   is the original action, giving id_! = id on modules. Apply this termwise
   (sk-def-sfb-module-derived-lower-shriek) to identify the candidate with Rp_*.
3. Apply det-sf-comp-coherence-single to (id_X,p). The closures are replete by
   det-def-localizing-closure-existence, so Rp_* preserves them. The comparison
   of det-sf-comp-coherence-cocycle with the chosen compactification gives the
   natural isomorphism in clause (1), with the actual ambient pushforward.
4. By sk-thm-existence (2), lower shriek preserves Dctf; transport through the
   comparison using repleteness (det-def-sfb-constructible-tor-amplitude).
   By sk-thm-existence (4), its Brown right adjoint also preserves Dctf.
   Any specified adjoint G is isomorphic to that one by uniqueness of right
   adjoints, so the same preservation applies to G.
5. Every property in the intersection of sk-def-localizing-closure contains
   Dctf, giving hSY. Both inclusions are full, with the ambient derived Hom sets.
   For K,L in Dctf, precompose a map Rp_* K -> L with alpha_K, then apply the
   given adjunction bijection. Its inverse applies the inverse bijection and
   precomposes with alpha_K^{-1}. Naturality follows from alpha and adjunction
   naturality. These are the restricted adjunction Hom equivalences; equivalently
   transport the adjunction by alpha and apply Adjunction.restrictFullyFaithful.
   The unit is G(alpha_K) after eta_K and the counit is epsilon_L after
   alpha_{G L}^{-1}. Their objects belong to Dctf by step 4, proving clause (2).
-/
theorem proper_exceptional_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (h : ∀ K, localizingClosureProEtale Λ X.left K →
      localizingClosureProEtale Λ Y.left
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField p)).obj K))
    (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (_adj : localizingLowerShriek Λ (compactificationOverField p) h ⊣ G) :
    ∃ hStar : ∀ K, localizingClosureProEtale Λ X.left K →
        localizingClosureProEtale Λ Y.left ((R((p.left)_*⟦Λ⟧)).obj K),
      Nonempty (localizingLowerShriek Λ (compactificationOverField p) h ≅
        (localizingClosureProEtale Λ Y.left).lift
          ((localizingClosureProEtale Λ X.left).ι ⋙ R((p.left)_*⟦Λ⟧))
          (fun K ↦ hStar K.obj K.property)) ∧
      (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
        constantModelBoundedConstructible Λ Y.left ((R((p.left)_*⟦Λ⟧)).obj K.obj) ∧
          DerivedCategory.finiteTorAmplitude _ ((R((p.left)_*⟦Λ⟧)).obj K.obj)) ∧
      ∃ (hSY : (constantModelBoundedConstructible Λ Y.left ⊓
          fun K ↦ DerivedCategory.finiteTorAmplitude _ K) ≤
            localizingClosureProEtale Λ Y.left)
        (F₀ : ConstantModelConstructibleFiniteTor Λ X.left ⥤
          ConstantModelConstructibleFiniteTor Λ Y.left)
        (G₀ : ConstantModelConstructibleFiniteTor Λ Y.left ⥤
          ConstantModelConstructibleFiniteTor Λ X.left),
        F₀ ⋙ (constantModelBoundedConstructible Λ Y.left ⊓
            fun K ↦ DerivedCategory.finiteTorAmplitude _ K).ι =
          (constantModelBoundedConstructible Λ X.left ⊓
            fun K ↦ DerivedCategory.finiteTorAmplitude _ K).ι ⋙ R((p.left)_*⟦Λ⟧) ∧
        G₀ ⋙ (constantModelBoundedConstructible Λ X.left ⊓
            fun K ↦ DerivedCategory.finiteTorAmplitude _ K).ι =
          ObjectProperty.ιOfLE hSY ⋙ G ⋙ (localizingClosureProEtale Λ X.left).ι ∧
        Nonempty (F₀ ⊣ G₀) := by
  classical
  let SX := constantModelBoundedConstructible Λ X.left ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let SY := constantModelBoundedConstructible Λ Y.left ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let LX := localizingClosureProEtale Λ X.left
  let LY := localizingClosureProEtale Λ Y.left
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X.left).2.1
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X.left).2.2.2.1
  have := (constantModelConstructibleFiniteTor_wellDefined Λ Y.left).2.1
  have := (constantModelConstructibleFiniteTor_wellDefined Λ Y.left).2.2.2.1
  have : LY.IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK P hP hS
    have := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)
  obtain ⟨_, _, hSX, hSY, _, _, _, hex⟩ :=
    exceptionalInverseImage_exists Λ ℓ k p _hΛ
  obtain ⟨_, _, _, _, hF, hcomp, ⟨G', _, _, hnon, hpres⟩, _⟩ := hex
  obtain ⟨adj'⟩ := hnon
  let eShriek : openImmersionLowerShriek Λ (𝟙 X.left) ≅ 𝟭 _ :=
    ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X.left)).ofNatIsoRight
      (upperStarId Λ X.left)).leftAdjointUniq Adjunction.id
  let eId : (openImmersionLowerShriek Λ (𝟙 X.left)).mapDerivedCategory ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryNatIso eShriek ≪≫ Functor.mapDerivedCategoryIdIso _
  let ec : rightDerivedLowerShriekOfCompactification Λ
      (Compactification.ofIsProper p.left) ≅ R((p.left)_*⟦Λ⟧) :=
    Functor.isoWhiskerRight eId _ ≪≫ Functor.leftUnitor _
  obtain ⟨bc⟩ := hcomp (Compactification.ofIsProper p.left)
  let beta : localizingLowerShriek Λ (compactificationOverField p) h ⋙ LY.ι ≅
      LX.ι ⋙ R((p.left)_*⟦Λ⟧) :=
    bc ≪≫ Functor.isoWhiskerLeft LX.ι ec
  have hStar : ∀ K, LX K → LY ((R((p.left)_*⟦Λ⟧)).obj K) := by
    intro K hK
    exact LY.prop_of_iso (beta.app ⟨K, hK⟩) (h K hK)
  let FStar := LY.lift (LX.ι ⋙ R((p.left)_*⟦Λ⟧)) (fun K ↦ hStar K.obj K.property)
  let alpha : localizingLowerShriek Λ (compactificationOverField p) h ≅ FStar :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk LY (beta.app K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact beta.hom.naturality f)
  have hRp : ∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      SY ((R((p.left)_*⟦Λ⟧)).obj K.obj) := by
    intro K
    exact SY.prop_of_iso (beta.app ((ObjectProperty.ιOfLE hSX).obj K))
      (hF ((ObjectProperty.ιOfLE hSX).obj K) K.property)
  let eg : G' ≅ G := adj'.rightAdjointUniq _adj
  have hGpres : ∀ K : ConstantModelConstructibleFiniteTor Λ Y.left,
      SX (G.obj ((ObjectProperty.ιOfLE hSY).obj K)).obj := by
    intro K
    exact SX.prop_of_iso (LX.ι.mapIso (eg.app ((ObjectProperty.ιOfLE hSY).obj K)))
      (hpres ((ObjectProperty.ιOfLE hSY).obj K) K.property)
  let F₀ := SY.lift (SX.ι ⋙ R((p.left)_*⟦Λ⟧)) hRp
  let G₀ := SX.lift (ObjectProperty.ιOfLE hSY ⋙ G ⋙ LX.ι) hGpres
  refine ⟨hStar, ⟨alpha⟩, hRp, hSY, F₀, G₀, rfl, rfl, ⟨?_⟩⟩
  exact _adj.restrictFullyFaithful (ObjectProperty.fullyFaithfulιOfLE hSX)
    (ObjectProperty.fullyFaithfulιOfLE hSY)
    (Functor.isoWhiskerLeft (ObjectProperty.ιOfLE hSX) alpha) (Iso.refl _)

end AlgebraicGeometry.ProEtale.CondensedRing
