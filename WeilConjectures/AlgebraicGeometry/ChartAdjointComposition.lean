/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginAdjointClass
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Composition of exceptional adjoints on a purity chart

Source: `literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors-basics/sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/
sk-prop-sp-et-proet/thm-pur-general-admissibility.proof.md`, opening paragraph and Step 1
(blueprint: thm-pur-general-admissibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.defProp false
set_option warn.classDefReducibility false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The adjunction obtained by restricting a `ComparisonClassAdjunction` to the two
full comparison subcategories.  The hom-equivalence and its two naturality equations are
the data used by `Adjunction.mkOfHomEquiv`; no ambient unbounded adjunction is introduced.
Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/sk-prop-sp-et-proet/
thm-pur-general-admissibility.proof.md`, Step 1
(blueprint: thm-pur-general-admissibility). -/
noncomputable def comparisonClassRestrictedAdjunction
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (c : Compactification f)
    (G : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (a : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (P : ObjectProperty (DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))))
    (Q : ObjectProperty (DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))))
    (h : ComparisonClassAdjunction A f c G a P Q)
    (h₁ : ∀ K : P.FullSubcategory,
      Q ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj))
    (h₂ : ∀ L : Q.FullSubcategory,
      P ((R(ν_*(Y)[ModuleCat.{u + 1} A]) ⋙ G ⋙
        D(ν^*(X)[ModuleCat.{u + 1} A])).obj L.obj)) :
    Q.lift (P.ι ⋙ rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c) h₁ ⊣
      P.lift (Q.ι ⋙ (R(ν_*(Y)[ModuleCat.{u + 1} A]) ⋙ G ⋙
        D(ν^*(X)[ModuleCat.{u + 1} A]))) h₂ :=
  Adjunction.mkOfHomEquiv
    { homEquiv K L :=
        { toFun g := ObjectProperty.homMk
            (h.homEquiv c K.obj K.property L.obj L.property g.hom)
          invFun g := ObjectProperty.homMk
            ((h.homEquiv c K.obj K.property L.obj L.property).symm g.hom)
          left_inv g := by
            ext
            exact (h.homEquiv c K.obj K.property L.obj L.property).symm_apply_apply g.hom
          right_inv g := by
            ext
            exact (h.homEquiv c K.obj K.property L.obj L.property).apply_symm_apply g.hom }
      homEquiv_naturality_left_symm {K K' L} φ g := by
        ext
        change (h.homEquiv c K.obj K.property L.obj L.property).symm
            (φ.hom ≫ g.hom) =
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map φ.hom ≫
            (h.homEquiv c K'.obj K'.property L.obj L.property).symm g.hom
        apply (h.homEquiv c K.obj K.property L.obj L.property).injective
        rw [Equiv.apply_symm_apply]
        rw [h.naturality_left c K.obj K'.obj K.property K'.property L.obj L.property
          φ.hom ((h.homEquiv c K'.obj K'.property L.obj L.property).symm g.hom)]
        rw [(h.homEquiv c K'.obj K'.property L.obj L.property).apply_symm_apply]
      homEquiv_naturality_right {K L L'} g φ := by
        ext
        change h.homEquiv c K.obj K.property L'.obj L'.property (g.hom ≫ φ.hom) =
          h.homEquiv c K.obj K.property L.obj L.property g.hom ≫
            (R(ν_*(Y)[ModuleCat.{u + 1} A]) ⋙ G ⋙
              D(ν^*(X)[ModuleCat.{u + 1} A])).map φ.hom
        exact h.naturality_right c K.obj K.property L.obj L'.obj L.property L'.property
          g.hom φ.hom }

/-! The chart closure theorem and the two canonical mate isomorphisms. -/

/-- The seven étale-origin closure clauses required in the chart construction.

This is the closure part of the opening paragraph and Step 1 of the source: the ordinary
right adjoints, and the transported open adjunction, preserve the bounded-below
étale-origin comparison classes.  The two canonical mate isomorphisms are defined below
from these closure witnesses, rather than being round-trip equations.

Proof (node lem-pur-chart-adjoint-composition, Steps 1 and 3):
1. Work at `A = A_{E,n}` and `Z = 𝔸^d_V`.  The presentation `u ≫ f = i ≫ π` is a
   hypothesis.  All schemes are separated of finite type over the field, hence Noetherian
   (lem-weil-pbc-finite-type-over-noetherian).  So `u` is quasi-compact and of finite type
   (lem-sfb-noetherian-open-immersion-qc, lem-weil-pbc-qc-open-immersion-finite-type).  It is
   separated, and `i`, `π` are separated of finite type.
2. For `g = f, i, π, h`, thm-sf-ambient-adjoint-class (2) gives the Hom bijection for `Rg_!`
   and `Rg^× = ν^* g^× Rν_*`.  By the bounded-below typing of def-weil-exceptional-inverse-image,
   `N = g^× Rν_* L` is a bounded-below étale complex, and `(N, 𝟙)` witnesses `Rg^× L` in
   def-sf-etale-origin-subcategory.  This gives clauses 1–4 and 7.
3. For the open immersion, prop-exc-open-adjoint gives `u_! ⊣ Lu^*`.
   lem-trf-witnessed-open-pullback (morphism `u`, auxiliary opens the identities) gives the
   witness `(u_et^{-1} N, α_u)` for `Lu^* M`: this is clause 6.  The same lemma with morphism
   `𝟙 U`, `j = u`, `i = 𝟙 U` gives preservation by `u_!`: this is clause 5.
Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/sk-prop-sp-et-proet/
thm-pur-general-admissibility.proof.md`, opening paragraph and Step 1
(blueprint: thm-pur-general-admissibility). -/
theorem chartAdjointComposition_closure
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {V X U : Scheme.{u}} [IsAffine V] [IsAffine U]
    (f : X ⟶ V) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u]
    (d : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [IsClosedImmersion i]
    (_hfac : u ≫ f = i ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
    [HasCompactification u] [HasCompactification f] [HasCompactification (u ≫ f)]
    [HasCompactification i]
    [HasCompactification (AffineSpace (ULift.{u} (Fin d)) V ↘ V)] :
    letI : Finite P.Coefficient := by
      letI : Finite P.Ring :=
        Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
      exact Finite.of_injective ULift.down ULift.down_injective
    let A := P.Coefficient
    let M := ModuleCat.{u + 1} A
    let Z := AffineSpace (ULift.{u} (Fin d)) V
    let π : Z ⟶ V := Z ↘ V
    let PU := DerivedCategory.plusEtaleOrigin M U
    let PZ := DerivedCategory.plusEtaleOrigin M Z
    let PV := DerivedCategory.plusEtaleOrigin M V
    let PX := DerivedCategory.plusEtaleOrigin M X
    let cU := HasCompactification.compactification u
    let cI := HasCompactification.compactification i
    let cPi := HasCompactification.compactification π
    let cHOpen := HasCompactification.compactification (u ≫ f)
    letI : HasCompactification (i ≫ π) := ⟨⟨_hfac ▸ cHOpen⟩⟩
    let cHChart := HasCompactification.compactification (i ≫ π)
    let cF := HasCompactification.compactification f
    (∀ (GI : DerivedCategory (Sheaf Z.smallEtaleTopology M) ⥤
        DerivedCategory (Sheaf U.smallEtaleTopology M))
      (aI : Etale.rightDerivedLowerShriekOfCompactification M cI ⊣ GI)
      (hI : ComparisonClassAdjunction A i cI GI aI PU PZ)
      (GPi : DerivedCategory (Sheaf V.smallEtaleTopology M) ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology M))
      (aPi : Etale.rightDerivedLowerShriekOfCompactification M cPi ⊣ GPi)
      (hPi : ComparisonClassAdjunction A π cPi GPi aPi PZ PV)
      (GHChart : DerivedCategory (Sheaf V.smallEtaleTopology M) ⥤
        DerivedCategory (Sheaf U.smallEtaleTopology M))
      (aHChart : Etale.rightDerivedLowerShriekOfCompactification M cHChart ⊣ GHChart)
      (hHChart : ComparisonClassAdjunction A (i ≫ π) cHChart GHChart aHChart PU PV)
      (GHOpen : DerivedCategory (Sheaf V.smallEtaleTopology M) ⥤
        DerivedCategory (Sheaf U.smallEtaleTopology M))
      (aHOpen : Etale.rightDerivedLowerShriekOfCompactification M cHOpen ⊣ GHOpen)
      (hHOpen : ComparisonClassAdjunction A (u ≫ f) cHOpen GHOpen aHOpen PU PV)
      (hU : ComparisonClassAdjunction A u cU
        (D(Etale.upperStar M u))
        ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction M u).ofNatIsoLeft
          (Etale.rightDerivedLowerShriekIso A cU ≪≫
            Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion A u).symm) PU PX)
      (GF : DerivedCategory (Sheaf V.smallEtaleTopology M) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology M))
      (aF : Etale.rightDerivedLowerShriekOfCompactification M cF ⊣ GF)
      (hF : ComparisonClassAdjunction A f cF GF aF PX PV),
      (∀ L : PZ.FullSubcategory,
          PU ((R(ν_*(Z)[M]) ⋙ GI ⋙ D(ν^*(U)[M])).obj L.obj)) ∧
      (∀ L : PV.FullSubcategory,
          PZ ((R(ν_*(V)[M]) ⋙ GPi ⋙ D(ν^*(Z)[M])).obj L.obj)) ∧
      (∀ L : PV.FullSubcategory,
          PU ((R(ν_*(V)[M]) ⋙ GHChart ⋙ D(ν^*(U)[M])).obj L.obj)) ∧
      (∀ L : PV.FullSubcategory,
          PU ((R(ν_*(V)[M]) ⋙ GHOpen ⋙ D(ν^*(U)[M])).obj L.obj)) ∧
      (∀ K : PU.FullSubcategory,
          PX ((rightDerivedLowerShriekOfCompactification M cU).obj K.obj)) ∧
      (∀ L : PX.FullSubcategory,
          PU ((R(ν_*(X)[M]) ⋙ D(Etale.upperStar M u) ⋙ D(ν^*(U)[M])).obj L.obj)) ∧
      (∀ L : PV.FullSubcategory,
          PX ((R(ν_*(V)[M]) ⋙ GF ⋙ D(ν^*(X)[M])).obj L.obj))) := by
  sorry

/-- Canonical chart right-adjoint identification.

The value is the inverse of the mate of the canonical `originComposition` compositor,
with all adjunctions restricted by `comparisonClassRestrictedAdjunction` using the closure
witnesses supplied by `chartAdjointComposition_closure`.  It has the orientation
`R(i ≫ π)^× ≅ R(i)^× ⋙ R(π)^×`.

Construction (node Steps 2 and 4): thm-sf-comp-composition supplies the compositor
`α_{π,i} = originComposition A i π : Rπ_! Ri_! ≅ Rh_!` on the étale-origin classes.  The
restricted adjunctions compose, giving the natural chain
`Hom(K, Ri^× Rπ^× L) ≅ Hom(Ri_! K, Rπ^× L) ≅ Hom(Rπ_! Ri_! K, L) ≅ Hom(Rh_! K, L) ≅ Hom(K, Rh^× L)`.
By lem-cat-right-adjoint-composition, applied to `F = Ri_!`, `G = Rπ_!` and `α_{π,i}`, the two
right adjoints are identified as the mate (`conjugateIsoEquiv`) of `α_{π,i}`, in reversed order.
Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/sk-prop-sp-et-proet/
thm-pur-general-admissibility.proof.md`, Step 1
(blueprint: thm-pur-general-admissibility). -/
noncomputable def chartRightAdjointIso
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {U Z V : Scheme.{u}} (i : U ⟶ Z) (π : Z ⟶ V)
    [QuasiCompact i] [QuasiCompact π] [HasCompactification i]
    [HasCompactification π] [HasCompactification (i ≫ π)]
    (GI : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (aI : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (HasCompactification.compactification i) ⊣ GI)
    (hI : ComparisonClassAdjunction A i (HasCompactification.compactification i) GI aI (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z))
    (hI₂ : ∀ L : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).FullSubcategory,
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) ((R(ν_*(Z)[ModuleCat.{u + 1} A]) ⋙ GI ⋙
        D(ν^*(U)[ModuleCat.{u + 1} A])).obj L.obj))
    (GPi : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (aPi : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (HasCompactification.compactification π) ⊣ GPi)
    (hPi : ComparisonClassAdjunction A π (HasCompactification.compactification π) GPi aPi (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V))
    (hPi₂ : ∀ L : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).FullSubcategory,
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z) ((R(ν_*(V)[ModuleCat.{u + 1} A]) ⋙ GPi ⋙
        D(ν^*(Z)[ModuleCat.{u + 1} A])).obj L.obj))
    (GH : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (aH : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (HasCompactification.compactification (i ≫ π)) ⊣ GH)
    (hH : ComparisonClassAdjunction A (i ≫ π)
      (HasCompactification.compactification (i ≫ π)) GH aH (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V))
    (hH₂ : ∀ L : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).FullSubcategory,
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) ((R(ν_*(V)[ModuleCat.{u + 1} A]) ⋙ GH ⋙
        D(ν^*(U)[ModuleCat.{u + 1} A])).obj L.obj)) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U).lift ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).ι ⋙ R(ν_*(V)[ModuleCat.{u + 1} A]) ⋙ GH ⋙
        D(ν^*(U)[ModuleCat.{u + 1} A])) hH₂ ≅
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).lift ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).ι ⋙ R(ν_*(V)[ModuleCat.{u + 1} A]) ⋙ GPi ⋙
      D(ν^*(Z)[ModuleCat.{u + 1} A])) hPi₂ ⋙
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U).lift ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι ⋙ R(ν_*(Z)[ModuleCat.{u + 1} A]) ⋙ GI ⋙
        D(ν^*(U)[ModuleCat.{u + 1} A])) hI₂) :=
  let adjI := comparisonClassRestrictedAdjunction i
    (HasCompactification.compactification i) GI aI (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z) hI
    (fun K ↦ K.property.rightDerivedLowerShriek_obj i) hI₂
  let adjPi := comparisonClassRestrictedAdjunction π
    (HasCompactification.compactification π) GPi aPi (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V) hPi
    (fun K ↦ K.property.rightDerivedLowerShriek_obj π) hPi₂
  let adjH := comparisonClassRestrictedAdjunction (i ≫ π)
    (HasCompactification.compactification (i ≫ π)) GH aH (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V) hH
    (fun K ↦ K.property.rightDerivedLowerShriek_obj (i ≫ π)) hH₂
  (conjugateIsoEquiv (adjI.comp adjPi) adjH
    (originComposition A i π).symm).symm

/-- Canonical open-chart right-adjoint identification.

The value is the mate of the canonical `originComposition` compositor after restricting
`D(u_!) ⊣ D(u^*)` (transported to compact support) and the comparison-class adjunction
for `f`.  It has the orientation `Lu^* Rf^× ≅ R(u ≫ f)^×`.

Construction (node Steps 2, 3 and 5): `R(u)_! = u_!` through the compactification
identification, and thm-sf-comp-composition supplies `α_{f,u} = originComposition A u f :
Rf_! u_! ≅ Rh_!`.  The open adjunction `u_! ⊣ Lu^*` (prop-exc-open-adjoint), restricted by
the closure of Step 3, composes with the restricted adjunction for `f`, giving the chain
`Hom(K, Lu^* Rf^× L) ≅ Hom(u_! K, Rf^× L) ≅ Hom(Rf_! u_! K, L) ≅ Hom(Rh_! K, L) ≅ Hom(K, Rh^× L)`,
whose third bijection is `α_{f,u}`.  By lem-cat-right-adjoint-composition the identification
is the mate (`conjugateIsoEquiv`) of `α_{f,u}`.
Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/sk-prop-sp-et-proet/
thm-pur-general-admissibility.proof.md`, Step 1
(blueprint: thm-pur-general-admissibility). -/
noncomputable def openRightAdjointIso
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {U X V : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ V)
    [IsOpenImmersion u] [QuasiCompact u] [QuasiCompact f]
    [HasCompactification u] [HasCompactification f] [HasCompactification (u ≫ f)]
    (hU : ComparisonClassAdjunction A u (HasCompactification.compactification u)
      (D(Etale.upperStar (ModuleCat.{u + 1} A) u))
      ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) u).ofNatIsoLeft
        (Etale.rightDerivedLowerShriekIso A
          (HasCompactification.compactification u) ≪≫
          Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion A u).symm)
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X))
    (hU₁ : ∀ K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U).FullSubcategory,
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X) ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification u)).obj K.obj))
    (hU₂ : ∀ L : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory,
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) ((R(ν_*(X)[ModuleCat.{u + 1} A]) ⋙
        D(Etale.upperStar (ModuleCat.{u + 1} A) u) ⋙
        D(ν^*(U)[ModuleCat.{u + 1} A])).obj L.obj))
    (GF : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (aF : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (HasCompactification.compactification f) ⊣ GF)
    (hF : ComparisonClassAdjunction A f (HasCompactification.compactification f)
      GF aF (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V))
    (hF₂ : ∀ L : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).FullSubcategory,
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X) ((R(ν_*(V)[ModuleCat.{u + 1} A]) ⋙ GF ⋙
        D(ν^*(X)[ModuleCat.{u + 1} A])).obj L.obj))
    (GH : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (aH : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (HasCompactification.compactification (u ≫ f)) ⊣ GH)
    (hH : ComparisonClassAdjunction A (u ≫ f)
      (HasCompactification.compactification (u ≫ f)) GH aH (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V))
    (hH₂ : ∀ L : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).FullSubcategory,
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) ((R(ν_*(V)[ModuleCat.{u + 1} A]) ⋙ GH ⋙
        D(ν^*(U)[ModuleCat.{u + 1} A])).obj L.obj)) :
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).lift ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).ι ⋙ R(ν_*(V)[ModuleCat.{u + 1} A]) ⋙ GF ⋙
      D(ν^*(X)[ModuleCat.{u + 1} A])) hF₂ ⋙
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U).lift ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙ R(ν_*(X)[ModuleCat.{u + 1} A]) ⋙
        D(Etale.upperStar (ModuleCat.{u + 1} A) u) ⋙
        D(ν^*(U)[ModuleCat.{u + 1} A])) hU₂) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U).lift ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V).ι ⋙ R(ν_*(V)[ModuleCat.{u + 1} A]) ⋙ GH ⋙
        D(ν^*(U)[ModuleCat.{u + 1} A])) hH₂ :=
  let adjU := comparisonClassRestrictedAdjunction u
    (HasCompactification.compactification u)
    (D(Etale.upperStar (ModuleCat.{u + 1} A) u))
    ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) u).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIso A
        (HasCompactification.compactification u) ≪≫
        Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion A u).symm)
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X) hU hU₁ hU₂
  let adjF := comparisonClassRestrictedAdjunction f
    (HasCompactification.compactification f) GF aF (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V) hF
    (fun K ↦ K.property.rightDerivedLowerShriek_obj f) hF₂
  let adjH := comparisonClassRestrictedAdjunction (u ≫ f)
    (HasCompactification.compactification (u ≫ f)) GH aH (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U) (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) V) hH
    (fun K ↦ K.property.rightDerivedLowerShriek_obj (u ≫ f)) hH₂
  conjugateIsoEquiv (adjU.comp adjF) adjH (originComposition A u f).symm

end AlgebraicGeometry.ProEtale
