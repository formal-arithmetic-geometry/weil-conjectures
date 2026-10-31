/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteCounitRestrictionData
import WeilConjectures.SecSmoothPurity.ProperFiniteCoefficientExtension
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import WeilConjectures.SixFunctors.FiniteCounitRestrictionCoherence
import WeilConjectures.SixFunctors.FiniteCounitRestrictionTargets

/-! # Restriction squares for finite exceptional counits -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteCounitRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [hsep : IsSeparated (X ↘ Spec (.of D.k))]
  (c : Compactification (X ↘ Spec (.of D.k)))

omit hft hsep in
private theorem compactComparison_counit {m n : ℕ} (h : n ≤ m) :
    compactComparison l E D X c h ≫ etaleCounit l E D X c n =
      (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
        (etaleCounit l E D X c m) ≫
      (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
        (Spec (.of D.k))).hom := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have hi : IsIso (Etale.ExceptionalCoefficients.compactSupportMap
      (finiteDualizingQuotient l E h) c (etaleOmega l E D X c m)) := by
    have := (Etale.properFiniteCoefficientExtension (finiteDualizingQuotient l E h)
      c.g).1 ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) c.i).mapDerivedCategory.obj
          (etaleOmega l E D X c m))
    unfold Etale.ExceptionalCoefficients.compactSupportMap
    infer_instance
  have he := ((etaleAdjunction l E D X c n).homEquiv _ _).symm_apply_apply
    (Etale.ExceptionalCoefficients.comparisonInverse (finiteDualizingQuotient l E h) c
      (etaleOmega l E D X c m) ≫
      (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
        (etaleCounit l E D X c m) ≫
      (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
        (Spec (.of D.k))).hom)
  change (etaleSupport l E D X c n).map (comparison l E D X c h) ≫
    etaleCounit l E D X c n = _ at he
  unfold compactComparison
  rw [Category.assoc, he]
  simp only [Etale.ExceptionalCoefficients.comparisonInverse, dif_pos hi,
    IsIso.hom_inv_id_assoc]

omit hft hsep in
private theorem etale_counit_square {m n : ℕ} (h : n ≤ m) :
    etaleTransition l E D X c h ≫
      (Sheaf.derivedRestrictScalars (Spec (.of D.k)).smallEtaleTopology
        (finiteDualizingQuotient l E h)).map (etaleCounit l E D X c n) =
    etaleCounit l E D X c m ≫ etaleUnitTransition l E D h := by
  let adj := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
    (Spec (.of D.k)).smallEtaleTopology (finiteDualizingQuotient l E h))
  change adj.homEquiv _ _ (compactComparison l E D X c h) ≫ _ =
    _ ≫ adj.homEquiv _ _ _
  rw [← adj.homEquiv_naturality_right, compactComparison_counit]
  exact adj.homEquiv_naturality_left (etaleCounit l E D X c m)
    (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
      (Spec (.of D.k))).hom

private theorem transport_square
    {A B C H : Type*} [Category A] [Category B] [Category C] [Category H]
    (R : B ⥤ A) (F : A ⥤ C) (G : B ⥤ H) (S : H ⥤ C)
    (e : G ⋙ S ≅ R ⋙ F)
    {M U : A} {N V : B} {M' U' : C} {N' V' : H}
    (a : M' ≅ F.obj M) (b : N' ≅ G.obj N)
    (c : U' ≅ F.obj U) (d : V' ≅ G.obj V)
    (t : M ⟶ R.obj N) (v : U ⟶ R.obj V) (f : M ⟶ U) (g : N ⟶ V)
    (h : t ≫ R.map g = f ≫ v) :
    (a.hom ≫ F.map t ≫ e.inv.app N ≫ S.map b.inv) ≫
        S.map (b.hom ≫ G.map g ≫ d.inv) =
      (a.hom ≫ F.map f ≫ c.inv) ≫
        (c.hom ≫ F.map v ≫ e.inv.app V ≫ S.map d.inv) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← S.map_comp_assoc b.inv b.hom, b.inv_hom_id, S.map_id, Category.id_comp,
    c.inv_hom_id_assoc]
  have hn := e.inv.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← F.map_comp_assoc, h, F.map_comp]
  simp only [Category.assoc]

omit hft hsep in
private theorem counit_square {m n : ℕ} (h : n ≤ m) :
    transition l E D X c h ≫
      (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
        (finiteDualizingQuotient l E h)).map (counit l E D X c n) =
      counit l E D X c m ≫ unitTransition l E D h := by
  exact transport_square
    (Sheaf.derivedRestrictScalars (Spec (.of D.k)).smallEtaleTopology
      (finiteDualizingQuotient l E h))
    (realization l E (Spec (.of D.k)) m) (realization l E (Spec (.of D.k)) n)
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
      (finiteDualizingQuotient l E h))
    (ProEtale.pbcDerivedComparisonRestrict.{u} (Spec (.of D.k))
      (finiteDualizingQuotient l E h))
    (valueOrigin l E D X c m) (valueOrigin l E D X c n)
    (unitOrigin l E D m).symm (unitOrigin l E D n).symm
    (etaleTransition l E D X c h) (etaleUnitTransition l E D h)
    (etaleCounit l E D X c m) (etaleCounit l E D X c n)
    (etale_counit_square l E D X c h)

private theorem targetConstantMap_isIso (n : ℕ) :
    IsIso (targetConstantMap l E D n) := by
  let : IsAlgClosed D.k := pointFibreBaseIsAlgClosed D
  let J := ProEt.topology (Spec (.of D.k))
  let A := ModuleCat.{u + 1} (integralRing l E)
  let M := quotientModule l E n
  have hi : IsIso ((toSheafify J ((Functor.const _).obj M)).app
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) := by
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (ProEtale.bijective_toSheafify_app_of_iso (Iso.refl (Spec (.of D.k)))
        ((Functor.const _).obj M))
  have hu : IsIso ((constantSheafAdj J A (ProEt.isTerminalMkId _)).unit.app M) := by
    dsimp only [constantSheafAdj]
    rw [Adjunction.comp_unit_app]
    change IsIso (𝟙 M ≫ (toSheafify J ((Functor.const _).obj M)).app
      (op (ProEt.mk (𝟙 (Spec (.of D.k))))))
    simpa only [Category.id_comp] using hi
  have hc : IsIso (constantSections l E D n) := by
    unfold constantSections
    infer_instance
  unfold targetConstantMap
  infer_instance

omit hft hsep in
private theorem sections_square {m n : ℕ} (h : n ≤ m) :
    sectionTransition l E D X c h ≫
      (finiteSections l E D n).map (counit l E D X c n) =
    (finiteSections l E D m).map (counit l E D X c m) ≫
      sectionUnitTransition l E D h := by
  let R := Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
    (finiteDualizingQuotient l E h)
  let Im := Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
    (integralQuotient l E m)
  let In := Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
    (integralQuotient l E n)
  let e : R ⋙ Im ≅ In := integralRestrictionComp l E D h
  let S := (sections l E D).mapDerivedCategory
  have hn := e.hom.naturality (counit l E D X c n)
  dsimp only [Functor.comp_map] at hn
  have hs : (Im.map (transition l E D X c h) ≫ e.hom.app (value l E D X c n)) ≫
        In.map (counit l E D X c n) =
      Im.map (counit l E D X c m) ≫
        (Im.map (unitTransition l E D h) ≫ e.hom.app (𝟙_ _)) := by
    rw [Category.assoc, ← hn, ← Im.map_comp_assoc, counit_square, Im.map_comp,
      Category.assoc]
  exact (S.map_comp _ _).symm.trans
    ((congrArg S.map hs).trans (S.map_comp _ _))

include hft hqc hsep

/-- The finite restriction-form counit square, canonical coefficient targets, and all
identity and successive-quotient compatibilities. The target isomorphisms are fixed
by being inverse to the actual regular constant-section map, so they are canonical.

Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2,
final sentences (blueprint: lem-coef-finite-counit-restriction-square).

Proof:
1. At the retained compactification c, lem-asd-proper-finite-coefficient-extension makes
compactSupportMap invertible. The inverse-transpose identity of the exceptional
adjunction at c gives F(u) followed by the counit; cancelling the compact comparison with
its inverse gives epsilon_n b = lambda T epsilon_m.
2. Take scalar-adjunction transposes. Naturality of homEquiv on both sides gives
Res(epsilon_n) d = v epsilon_m on the ordinary etale side. Transport through valueOrigin,
unitOrigin and the natural isomorphism pbcDerivedComparisonRestrict (transport_square).
3. At the algebraically closed point, lem-trf-point-sheafification-final makes the
constant-sheaf adjunction unit bijective, so targetConstantMap is invertible; iota is its
actual inverse, and its normalization follows by cancellation.
4. Apply integral restriction to step 2; naturality of integralRestrictionComp and
functoriality of exact sections give the section counit square. The regular quotient
equation lem-coef-finite-counit-constant-targets, cancelled against iota, identifies
sectionUnitTransition with quotientMap in degree zero; substitute it.
5. The sheaf identity and composition laws for d and v and the section laws for d are
lem-coef-finite-counit-restriction-coherence. The section laws for v follow from step 4
and the identity and composition of the actual quotient maps, by cancelling iota.
No strict representative or test object is used. -/
theorem finiteCounitRestrictionSquare (_hl : l ≠ D.p) :
    (∀ {m n : ℕ} (h : n ≤ m),
      transition l E D X c h ≫
        (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
          (finiteDualizingQuotient l E h)).map (counit l E D X c n) =
      counit l E D X c m ≫ unitTransition l E D h) ∧
    (∀ n : ℕ,
      transition l E D X c (le_refl n) ≫
        (restrictionUnit l E D n).hom.app (value l E D X c n) = 𝟙 _) ∧
    (∀ n : ℕ,
      unitTransition l E D (le_refl n) ≫
        (restrictionUnit l E D n).hom.app (𝟙_ _) = 𝟙 _) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      transition l E D X c (hmn.trans hrm) ≫
        (restrictionComp l E D hrm hmn).inv.app (value l E D X c n) =
      transition l E D X c hrm ≫
        (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
          (finiteDualizingQuotient l E hrm)).map (transition l E D X c hmn)) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      unitTransition l E D (hmn.trans hrm) ≫
        (restrictionComp l E D hrm hmn).inv.app (𝟙_ _) =
      unitTransition l E D hrm ≫
        (Sheaf.derivedRestrictScalars.{u} (ProEt.topology (Spec (.of D.k)))
          (finiteDualizingQuotient l E hrm)).map (unitTransition l E D hmn)) ∧
    ∃ ι : ∀ n : ℕ,
      (finiteSections l E D n).obj (𝟙_ _) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (integralRing l E)) 0).obj
          (quotientModule l E n),
      (∀ n : ℕ, targetConstantMap l E D n ≫ (ι n).hom = 𝟙 _) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        sectionUnitTransition l E D h ≫ (ι n).hom =
          (ι m).hom ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (integralRing l E)) 0).map
              (quotientMap l E h)) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        sectionTransition l E D X c h ≫
            (finiteSections l E D n).map (counit l E D X c n) ≫ (ι n).hom =
          (finiteSections l E D m).map (counit l E D X c m) ≫ (ι m).hom ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (integralRing l E)) 0).map
              (quotientMap l E h)) ∧
      (∀ n : ℕ, sectionTransition l E D X c (le_refl n) = 𝟙 _) ∧
      (∀ n : ℕ, sectionUnitTransition l E D (le_refl n) = 𝟙 _) ∧
      (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
        sectionTransition l E D X c (hmn.trans hrm) =
          sectionTransition l E D X c hrm ≫ sectionTransition l E D X c hmn) ∧
      (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
        sectionUnitTransition l E D (hmn.trans hrm) =
          sectionUnitTransition l E D hrm ≫ sectionUnitTransition l E D hmn) := by
  obtain ⟨hdid, hvid, hdcomp, hvcomp, hsid, hscomp⟩ :=
    restriction_coherence l E D X c _hl
  have hi := targetConstantMap_isIso l E D
  have hq {m n : ℕ} (h : n ≤ m) := constant_targets l E D h
  let : ∀ n : ℕ, IsIso (targetConstantMap l E D n) := hi
  let ι := fun n ↦ (asIso (targetConstantMap l E D n)).symm
  have hv {m n : ℕ} (h : n ≤ m) :
      sectionUnitTransition l E D h ≫ (ι n).hom =
        (ι m).hom ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (integralRing l E)) 0).map
            (quotientMap l E h) := by
    apply (cancel_epi (targetConstantMap l E D m)).mp
    dsimp only [ι, Iso.symm_hom, asIso_inv]
    rw [← Category.assoc, hq]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  have hqid (n : ℕ) : quotientMap l E (le_refl n) = 𝟙 _ := by
    ext x
    exact DFunLike.congr_fun (finiteDualizingQuotient_id l E n) x
  have hqcomp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
      quotientMap l E (hmn.trans hrm) =
        quotientMap l E hrm ≫ quotientMap l E hmn := by
    ext x
    exact DFunLike.congr_fun (finiteDualizingQuotient_comp l E hrm hmn) x
  refine ⟨fun h ↦ counit_square l E D X c h, hdid, hvid,
    fun h₁ h₂ ↦ hdcomp h₁ h₂, fun h₁ h₂ ↦ hvcomp h₁ h₂, ι, ?_,
    fun h ↦ hv h, ?_, hsid, ?_, fun h₁ h₂ ↦ hscomp h₁ h₂, ?_⟩
  · intro n
    exact (asIso (targetConstantMap l E D n)).hom_inv_id
  · intro m n h
    rw [← Category.assoc, sections_square, Category.assoc, hv h]
  · intro n
    apply (cancel_mono (ι n).hom).mp
    rw [Category.id_comp, hv (le_refl n), hqid]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  · intro r m n hrm hmn
    apply (cancel_mono (ι n).hom).mp
    rw [Category.assoc, hv hmn, ← Category.assoc, hv hrm, Category.assoc,
      ← Functor.map_comp, ← hqcomp, hv (hmn.trans hrm)]

end WeilConjectures.FiniteCounitRestriction
