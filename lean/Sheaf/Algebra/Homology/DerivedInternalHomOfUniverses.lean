/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Derived internal Hom without identifying the site universes

Source: Stacks Project, Sections 08J7, 0A8X and 07A5
(blueprint: def-pur-derived-internal-hom).
This is the same Hom-complex localization as derivedInternalHom, with the module
universe large enough to contain the site objects and arrows independently.
The ordinary-etale fixed-coefficient specialization is also publicly available through
Etale.derivedHom and Etale.derivedTensorHomAdjunction. Their original definitions
are imported directly; the generic construction and its comparisons are unchanged.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The usual Hom-complex bifunctor with functorial K-injective replacement
inverts quasi-isomorphisms in each variable.
Source: Stacks Project, Section 08J7, Lemma 0A95
(blueprint: def-pur-derived-internal-hom).
Proof:
1. Factor a pair of quasi-isomorphisms into its two separate variable maps.
2. Naturality of η and two-out-of-three show that I sends quasi-isomorphisms
to quasi-isomorphisms between K-injectives.
3. For a K-injective target the sheaf Hom complex sends a quasi-isomorphism
in the first variable to a quasi-isomorphism (Stacks 0A95). A quasi-isomorphism
between K-injectives is a homotopy equivalence, so Hom also inverts it in the
second variable. The derived localization inverts both resulting chain maps.
The lifted size changes neither sections nor differentials. -/
theorem derivedInternalHomOfUniverses_inverts
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    ((HomologicalComplex.quasiIso
      (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) (ComplexShape.up ℤ)).op.prod
      (HomologicalComplex.quasiIso
        (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
        (ComplexShape.up ℤ))).IsInvertedBy
        ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
          DerivedCategory.Q) := by
  sorry

/-- Derived internal Hom on the full module derived category, computed with the
canonical functorial K-injective replacement in its second variable.
Source: Stacks Project, Sections 08J7, 0A8X and 07A5
(blueprint: def-pur-derived-internal-hom). -/
noncomputable def derivedInternalHomOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :
    (DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⥤
        DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
  letI : IsGrothendieckAbelian.{max c v r} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  Localization.lift
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{max c v r} _) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q)
    (derivedInternalHomOfUniverses_inverts.{c, v, r, w} J R _
      (CochainComplex.toKInjectiveResolution.{max c v r} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r}
        _ M).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r}
          _ M⟩))
    ((DerivedCategory.Q).op.prod DerivedCategory.Q)

/-- Comparison with any functorial K-injective replacement, naturally in both variables.
Source: Stacks Project, Section 08J7 and Lemma 0A95
(blueprint: def-pur-derived-internal-hom).
Proof:
1. For the canonical replacement I₀ used in the definition, apply Localization.fac.
2. For another replacement I compare both through I(I₀(M)). Naturality and
   two-out-of-three make η at I₀(M) and I applied to η₀ at M quasi-isomorphisms
   between K-injectives. The Hom-complex functor followed by Q inverts them by
   derivedInternalHomOfUniverses_inverts, separately in the second variable.
3. Compose the factorization comparison with the first resulting natural
   isomorphism and the inverse of the second. This gives the stated comparison
   without choosing chain-map lifts of derived morphisms. -/
theorem derivedInternalHomOfUniverses_comparison
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    Nonempty (((DerivedCategory.Q).op.prod DerivedCategory.Q) ⋙
      derivedInternalHomOfUniverses.{c, v, r, w} J R ≅
        (𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
          DerivedCategory.Q) := by
  sorry

/-- Independence of the source representative and of any K-injective target representative.
Source: Stacks Project, Section 08J7 and Lemma 0A95
(blueprint: def-pur-derived-internal-hom).
Proof:
1. Apply derivedInternalHomOfUniverses_comparison to the canonical replacement I₀
   and evaluate at (op Lc, Ic).
2. The map Ic → I₀(Ic) is a quasi-isomorphism between K-injectives. Applying the
   Hom complex with source Lc and then Q gives an isomorphism, by the invariance
   clause of this node (lem-pur-rhom-well-defined).
3. Compose the comparison from Step 1 with the inverse of Step 2. Transport along
   eL and eM using the bifunctor's mapIso to obtain the claimed isomorphism. -/
theorem derivedInternalHomOfUniverses_obj_iso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (L M : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (Lc Ic : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    [Ic.IsKInjective]
    (_eL : DerivedCategory.Q.obj Lc ≅ L) (_eM : DerivedCategory.Q.obj Ic ≅ M) :
    Nonempty ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op L, M) ≅
      DerivedCategory.Q.obj (homComplex (R := R) Lc Ic)) := by
  sorry

end CategoryTheory
