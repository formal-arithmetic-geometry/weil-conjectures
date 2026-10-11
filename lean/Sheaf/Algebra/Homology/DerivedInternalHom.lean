/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Derived internal Hom on a ringed site

Source: Stacks Project, sites-cohomology.tex, Sections 08J7, 0A8X and 07A5
(blueprint: def-pur-derived-internal-hom).

`derivedInternalHom J R : D(O)ᵒᵖ × D(O) ⥤ D(O)` is the functor induced, through the
product localization `Q.op.prod Q`, by `(L, M) ↦ Q (Hom^•(L, I(M)))`, where `I` is the
functorial K-injective resolution `CochainComplex.kInjectiveResolutionFunctor` of the
Grothendieck abelian category of `O`-modules (`SheafOfModules.isGrothendieckAbelian`).
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory

/-- After any functorial K-injective replacement `I` in the second variable, the
localized Hom-complex bifunctor sends quasi-isomorphisms in either variable to
isomorphisms.

Source: Stacks Project, sites-cohomology.tex, Section 08J7, Lemma 0A95
(blueprint: def-pur-derived-internal-hom).

Proof:
1. A morphism of `W.op.prod W` is a pair `(t.op, s)` of quasi-isomorphisms; it factors as
   `(t.op, 𝟙) ≫ (𝟙, s)`, so it suffices to treat each variable separately.
2. For `s : M ⟶ M'` a quasi-isomorphism, naturality `η.app M ≫ I.map s = s ≫ η.app M'`
   and two-out-of-three make `I.map s` a quasi-isomorphism between K-injective complexes.
3. `quasiIso_homComplex_map` (`lem-pur-rhom-well-defined`), with `t = 𝟙` resp. `s = 𝟙`,
   makes the induced Hom-complex maps quasi-isomorphisms, so `DerivedCategory.Q` inverts
   them. -/
theorem derivedInternalHom_inverts
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    ((HomologicalComplex.quasiIso (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (ComplexShape.up ℤ)).op.prod
      (HomologicalComplex.quasiIso (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (ComplexShape.up ℤ))).IsInvertedBy
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        DerivedCategory.Q) := by
  sorry

/-- Derived internal Hom `R𝓗om_O : D(O)ᵒᵖ × D(O) ⥤ D(O)` on a small ringed site: the
functor induced through the localization `Q.op.prod Q` by
`(L, M) ↦ Q (𝓗om^•(L, I(M)))`, with `I` the functorial K-injective resolution
`CochainComplex.kInjectiveResolutionFunctor` of the Grothendieck abelian category of
`O`-modules. The Hom complex is `homComplexFunctor` (`def-pur-hom-complex`).

Source: Stacks Project, sites-cohomology.tex, Sections 08J7, 0A8X and 07A5
(blueprint: def-pur-derived-internal-hom). -/
noncomputable def derivedInternalHom
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤ DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  Localization.lift
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{u} _) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts J R _ (CochainComplex.toKInjectiveResolution.{u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    ((DerivedCategory.Q).op.prod DerivedCategory.Q)

/-- Computation of derived internal Hom with any functorial K-injective replacement
`η : 𝟭 ⟶ I`: `R𝓗om(Q L, Q M) ≅ Q (𝓗om^•(L, I(M)))`, naturally in both variables
(contravariant in `L`, covariant in `M`).

Source: Stacks Project, sites-cohomology.tex, Section 08J7 and Lemma 0A95
(blueprint: def-pur-derived-internal-hom).

Proof:
1. For the resolution used in `derivedInternalHom`, this is `Localization.fac`.
2. For another replacement `I`, the maps `I₀(M) ← M → I(M)` are quasi-isomorphisms into
   K-injective complexes, so `Q(η₀)⁻¹ ≫ Q(η)` lifts to a homotopy class of chain maps
   `I₀(M) ⟶ I(M)`, natural up to homotopy, each a quasi-isomorphism.
3. `quasiIso_homComplex_map` (`lem-pur-rhom-well-defined`) makes the induced maps of Hom
   complexes quasi-isomorphisms; homotopic maps give equal maps after `Q`, so these form a
   natural isomorphism after localization. -/
theorem derivedInternalHom_comparison
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    Nonempty ((DerivedCategory.Q.op).prod DerivedCategory.Q ⋙ derivedInternalHom J R ≅
        (𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
          DerivedCategory.Q) := by
  sorry

/-- Independence of the representatives and of an arbitrary K-injective target:
for complexes `Lc` representing `L` and a K-injective `Ic` representing `M`,
`R𝓗om(L, M) ≅ Q (𝓗om^•(Lc, Ic))`.

Source: Stacks Project, sites-cohomology.tex, Section 08J7 and Lemma 0A95
(blueprint: def-pur-derived-internal-hom).

Proof:
1. Compute with the functorial resolution via `derivedInternalHom_comparison`.
2. Represent the comparison `Q(I₀(Ic)) ≅ Q(Ic)` of two K-injective complexes by a chain
   map; it is a quasi-isomorphism since it represents an isomorphism.
3. Lemma 0A95 (`lem-pur-rhom-well-defined`) makes the induced Hom-complex map a
   quasi-isomorphism, hence an isomorphism after localization.
4. Apply the functor to the representative isomorphisms of `L` and `M` and compose. -/
theorem derivedInternalHom_obj_iso
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (L M : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (Lc Ic : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) [Ic.IsKInjective]
    (_eL : DerivedCategory.Q.obj Lc ≅ L) (_eM : DerivedCategory.Q.obj Ic ≅ M) :
    Nonempty ((derivedInternalHom J R).obj (op L, M) ≅
      DerivedCategory.Q.obj (homComplex (C := C) (J := J) (R := R) Lc Ic)) := by
  sorry

end CategoryTheory
