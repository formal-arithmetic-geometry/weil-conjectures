/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalRestrictionGlue
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExceptionalInverseImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The native constructible exceptional inverse image

The finite coefficient functor is the published comparison composite
`Scheme.finiteExceptionalInverseImage`. At non-finite coefficients we restrict the
single Brown adjunction on the native condensed localizing closures. In particular,
the algebraic-closure coefficient is `Profinite.padicAlgClRingObj`, not a category of
common representatives of rationalized coefficient systems.

The restriction and its right adjoint are constructed directly from the native
coefficient predicate; no finite-level system is used in this module.

Source: current blueprint, sec-six-functors-basics/sk-thm-existence/
def-weil-exceptional-inverse-image.md, non-finite Brown restriction paragraph
(blueprint: def-weil-exceptional-inverse-image).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The non-finite condensed coefficients of the exceptional inverse image, allowing
isomorphic presentations. The last clause is the finite-subextension-valued condensed
algebraic closure. Source: the coefficient convention and non-finite paragraph
(blueprint: def-weil-exceptional-inverse-image). -/
def IsNativeExceptionalCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))

private theorem nativeCoefficient_admissible (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsNativeExceptionalCoefficient ℓ Λ) : IsLocalizingAdmissibleCoefficient ℓ Λ := by
  rcases hΛ with h | h | ⟨E, h | h⟩ | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- Restrict a localizing adjunction along the full constructible inclusions.
The two comparison isomorphisms are identities on the original objects and maps.
Source: non-finite Brown restriction paragraph
(blueprint: def-weil-exceptional-inverse-image). -/
def nativeConstructibleRestrictionAdjunction
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ A, localizingClosureProEtale Λ X A → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c).obj A))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adj : localizingLowerShriek Λ c h ⊣ G)
    (hX : constantModelBoundedConstructible Λ X ≤ localizingClosureProEtale Λ X)
    (hY : constantModelBoundedConstructible Λ Y ≤ localizingClosureProEtale Λ Y)
    (hF : ∀ A, constantModelBoundedConstructible Λ X A →
      constantModelBoundedConstructible Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c).obj A))
    (hG : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      constantModelBoundedConstructible Λ Y K.obj →
      constantModelBoundedConstructible Λ X (G.obj K).obj) :
    restrictionGlueLowerShriek Λ c hF ⊣ restrictionGlueUpperShriek Λ G hY hG := by
  let comm1 : ObjectProperty.ιOfLE hX ⋙ localizingLowerShriek Λ c h ≅
      restrictionGlueLowerShriek Λ c hF ⋙ ObjectProperty.ιOfLE hY :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let comm2 : ObjectProperty.ιOfLE hY ⋙ G ≅
      restrictionGlueUpperShriek Λ G hY hG ⋙ ObjectProperty.ιOfLE hX :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  exact adj.restrictFullyFaithful (ObjectProperty.fullyFaithfulιOfLE _)
    (ObjectProperty.fullyFaithfulιOfLE _) comm1 comm2

/-- The actual compact-support functor restricts to the native bounded constructible
categories and has a right adjoint there. This is a theorem, not an input to the
exceptional-inverse-image definition.
Source: sk-thm-existence (3), (4), and Dctf = Dbc in sk-def-localizing-closure
(blueprint: def-weil-exceptional-inverse-image).

Proof: obtain the localizing adjunction and preservation from sk-thm-existence.
At each endpoint Dctf = Dbc by the non-finite coefficient Tor theorem. Consequently
both adjoints preserve the bounded constructible full subcategories. Restrict the
adjunction along their fully faithful inclusions; the comparison squares retain
literally the original objects and arrows. -/
theorem nativeConstructibleLowerShriek_hasRightAdjoint :
    ∃ hF : ∀ A, constantModelBoundedConstructible Λ X.left A →
      constantModelBoundedConstructible Λ Y.left
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj A),
      (restrictionGlueLowerShriek Λ (compactificationOverField f) hF).IsLeftAdjoint := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have eX := (localizingClosure_ctf_equals_bc ℓ X.left Λ hΛ).1.2.2.1
  have eY := (localizingClosure_ctf_equals_bc ℓ Y.left Λ hΛ).1.2.2.1
  obtain ⟨hX, hY, hSX, hSY, h, sX, sY, H⟩ :=
    exceptionalInverseImage_exists Λ ℓ k hcd f (nativeCoefficient_admissible Λ ℓ hΛ)
  let := hX
  let := hY
  let := sX
  let := sY
  obtain ⟨_, _, _, _, hFctf, _, ⟨G, s, _, ⟨adj⟩, hGctf⟩, _⟩ := H
  have iX : constantModelBoundedConstructible Λ X.left ≤
      localizingClosureProEtale Λ X.left := by rwa [eX] at hSX
  have iY : constantModelBoundedConstructible Λ Y.left ≤
      localizingClosureProEtale Λ Y.left := by rwa [eY] at hSY
  have hF : ∀ A, constantModelBoundedConstructible Λ X.left A →
      constantModelBoundedConstructible Λ Y.left
        ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).obj A) := by
    intro A hA
    have ht := hFctf ⟨A, iX A hA⟩ (by rwa [eX])
    rwa [eY] at ht
  have hG : ∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
      constantModelBoundedConstructible Λ Y.left K.obj →
      constantModelBoundedConstructible Λ X.left (G.obj K).obj := by
    intro K hK
    have ht := hGctf K (by rwa [eY])
    rwa [eX] at ht
  exact ⟨hF, ⟨⟨_, ⟨nativeConstructibleRestrictionAdjunction Λ _ h G adj iX iY hF hG⟩⟩⟩⟩

/-- The actual compact-support functor on the native condensed constructible categories.
Only its membership proof is selected; its object and arrow maps are those of the
published compactification functor. Source: the non-finite restriction paragraph
(blueprint: def-weil-exceptional-inverse-image). -/
def nativeConstructibleLowerShriek :
    ConstantModelBoundedConstructible Λ X.left ⥤ ConstantModelBoundedConstructible Λ Y.left :=
  restrictionGlueLowerShriek Λ (compactificationOverField f)
    (nativeConstructibleLowerShriek_hasRightAdjoint Λ ℓ k hcd f hΛ).choose

/-- The native condensed exceptional inverse image. Its defining right-adjoint property
specifies it up to unique counit-compatible natural isomorphism. It is obtained from
one localizing Brown adjunction and restriction, without passage through finite levels.
Source: the non-finite restriction paragraph
(blueprint: def-weil-exceptional-inverse-image). -/
def nativeConstructibleExceptionalInverseImage :
    ConstantModelBoundedConstructible Λ Y.left ⥤ ConstantModelBoundedConstructible Λ X.left :=
  (nativeConstructibleLowerShriek Λ ℓ k hcd f hΛ).rightAdjoint

/-- The natural Hom bijections and both triangle identities for the native functor.
Source: the defining adjunction paragraph
(blueprint: def-weil-exceptional-inverse-image). -/
def nativeConstructibleExceptionalAdjunction :
    nativeConstructibleLowerShriek Λ ℓ k hcd f hΛ ⊣
      nativeConstructibleExceptionalInverseImage Λ ℓ k hcd f hΛ :=
  Adjunction.ofIsLeftAdjoint _

/-- Any other right adjoint to the same native compact-support functor, in particular
a compactification construction, has a unique counit-compatible comparison with this
exceptional inverse image. Source: uniqueness paragraph, det-sp-unique-right-adjoint
(blueprint: def-weil-exceptional-inverse-image).

Proof: transpose the two counits by the two adjunctions. The triangle identities make
the transposes inverse; injectivity of the Hom bijections proves uniqueness. -/
theorem nativeConstructibleExceptionalInverseImage_unique
    (G : ConstantModelBoundedConstructible Λ Y.left ⥤
      ConstantModelBoundedConstructible Λ X.left)
    (adj : nativeConstructibleLowerShriek Λ ℓ k hcd f hΛ ⊣ G) :
    ∃! e : nativeConstructibleExceptionalInverseImage Λ ℓ k hcd f hΛ ≅ G,
      ∀ N, (nativeConstructibleLowerShriek Λ ℓ k hcd f hΛ).map (e.hom.app N) ≫
        adj.counit.app N =
          (nativeConstructibleExceptionalAdjunction Λ ℓ k hcd f hΛ).counit.app N :=
  (nativeConstructibleExceptionalAdjunction Λ ℓ k hcd f hΛ).existsUnique_iso_comp_counit adj

/-- The native constructible adjunction is exact, for the inherited triangulations
and the adjoint shift structure. Source: sk-thm-existence (3), restriction paragraph
(blueprint: def-weil-exceptional-inverse-image).

Proof: admissible bounded constructibility is triangulated. The restricted compact
support functor inherits its shift and triangle structures from the ambient derived
functor. Its adjoint receives the canonical adjoint shift structure; the triangulated
right-adjoint theorem proves exactness and compatibility of the adjunction. -/
theorem nativeConstructibleExceptionalAdjunction_exact :
    ∃ (hX : (constantModelBoundedConstructible Λ X.left).IsTriangulated)
      (hY : (constantModelBoundedConstructible Λ Y.left).IsTriangulated),
      (fun [_triX : (constantModelBoundedConstructible Λ X.left).IsTriangulated]
          [_triY : (constantModelBoundedConstructible Λ Y.left).IsTriangulated] ↦
        ∃ s : (nativeConstructibleLowerShriek Λ ℓ k hcd f hΛ).CommShift ℤ,
          ∃ t : (nativeConstructibleExceptionalInverseImage Λ ℓ k hcd f hΛ).CommShift ℤ,
            (fun [_leftShift : (nativeConstructibleLowerShriek Λ ℓ k hcd f hΛ).CommShift ℤ]
                [_rightShift : (nativeConstructibleExceptionalInverseImage
                  Λ ℓ k hcd f hΛ).CommShift ℤ] ↦
              (nativeConstructibleExceptionalAdjunction Λ ℓ k hcd f hΛ).IsTriangulated)
              (_leftShift := s) (_rightShift := t)) (_triX := hX) (_triY := hY) := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  let hX := admissible_boundedConstructible_isTriangulated Λ ℓ k
    (X := X.left) (nativeCoefficient_admissible Λ ℓ hΛ)
  let hY := admissible_boundedConstructible_isTriangulated Λ ℓ k
    (X := Y.left) (nativeCoefficient_admissible Λ ℓ hΛ)
  let := hX
  let := hY
  let F := nativeConstructibleLowerShriek Λ ℓ k hcd f hΛ
  let G := nativeConstructibleExceptionalInverseImage Λ ℓ k hcd f hΛ
  let adj := nativeConstructibleExceptionalAdjunction Λ ℓ k hcd f hΛ
  let s : F.CommShift ℤ := by
    dsimp [F, nativeConstructibleLowerShriek, restrictionGlueLowerShriek]
    infer_instance
  let : F.IsTriangulated := by
    dsimp [F, nativeConstructibleLowerShriek, restrictionGlueLowerShriek]
    infer_instance
  let t : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨hX, hY, s, t, Adjunction.IsTriangulated.mk' adj⟩

/-- Over the algebraically closed field of the blueprint, finite cohomological
dimension is a theorem. Thus this specialization has no extra cohomological-
dimension hypothesis. Source: the non-finite restriction paragraph
(blueprint: def-weil-exceptional-inverse-image). -/
def constructibleExceptionalInverseImage :
    ConstantModelBoundedConstructible Λ Y.left ⥤ ConstantModelBoundedConstructible Λ X.left :=
  nativeConstructibleExceptionalInverseImage Λ ℓ k
    (BaseFieldFiniteCD.of_isAlgClosed ℓ k) f hΛ

/-- The compact-support adjunction characterizing the exceptional inverse image over
an algebraically closed base. Source: defining Hom isomorphisms
(blueprint: def-weil-exceptional-inverse-image). -/
def constructibleExceptionalAdjunction :
    nativeConstructibleLowerShriek Λ ℓ k (BaseFieldFiniteCD.of_isAlgClosed ℓ k) f hΛ ⊣
      constructibleExceptionalInverseImage Λ ℓ k f hΛ :=
  nativeConstructibleExceptionalAdjunction Λ ℓ k (BaseFieldFiniteCD.of_isAlgClosed ℓ k) f hΛ

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hcd : BaseFieldFiniteCD ℓ k)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (hΛ : IsNativeExceptionalCoefficient ℓ Λ)

include ℓ hcd hΛ in
section AlgebraicallyClosed

variable [IsAlgClosed k]

end AlgebraicallyClosed

end AlgebraicGeometry.ProEtale.CondensedRing
