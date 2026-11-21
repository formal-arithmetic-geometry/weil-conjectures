/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.NumberTheory.Padics.IntegersDvdPow
public import WeilConjectures.PoincareDuality.Biduality.CoefficientChangeBraided
public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IhomCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClAdditive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper
public import WeilConjectures.TraceFormula.ExternalProductExtendScalars
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral

/-!

# Traces under the extension of scalars `𝒪_E ⟶ ℚ̄_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and write
`T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`
(`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgCl`). This file proves:

* `T_X` preserves categorical traces: `tr(T_X f) = T_X(tr f)`, up to the unit isomorphism of the
  monoidal functor `T_X`
  (`ProEtale.CondensedRing.trace_boundedConstructibleIntegersToPadicAlgCl_map`), `T_X` being
  braided for the Koszul braidings;
* over a separably closed field, every endomorphism of the unit of `Dᵇc(Spec k)⟦𝒪_E⟧` is a scalar
  of `𝒪_E` (`ProEtale.CondensedRing.surjective_pointIntegersBoundedConstructibleUnitEndRingHom`),
  and `T` is injective on these endomorphisms
  (`ProEtale.CondensedRing.eq_zero_of_boundedConstructibleIntegersToPadicAlgCl_map_eq_zero`), since
  a nonzero `r ∈ 𝒪_E` divides a power of `ℓ`, whose image in `ℚ̄_ℓ` is nonzero.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding
  PadicIntegersRingObj.boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- **The extension of scalars `𝒪_E ⟶ ℚ̄_ℓ` preserves categorical traces**: for an endomorphism `f`
of a dualizable bounded constructible `𝒪_E`-complex `A`, `tr(T_X f) = ε ≫ T_X(tr f) ≫ η`, where
`ε : 𝟙 ⟶ T_X 𝟙` is the unit of the monoidal functor `T_X` and `η` its inverse. -/
theorem trace_boundedConstructibleIntegersToPadicAlgCl_map
    {A : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧} [hA : HasRightDual A]
    [hTA : HasRightDual ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj A)] (f : A ⟶ A) :
    trace ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).map f) =
      ε (boundedConstructibleIntegersToPadicAlgCl ℓ E X) ≫
        (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map (trace f) ≫
        η (boundedConstructibleIntegersToPadicAlgCl ℓ E X) := by
  let : BraidedCategory Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧ :=
    @ObjectProperty.fullBraidedSubcategory _ _ _ _ _ (DerivedCategory.braidedCategory' _)
  let : (boundedConstructibleExtendScalars X.left ℓ E).Braided :=
    { boundedConstructibleExtendScalarsLaxBraided ℓ E X with }
  let : (constructibleToPadicAlgCl X.left ℓ E).Braided :=
    { constructibleToPadicAlgClLaxBraided ℓ E X with }
  let : HasRightDual ((boundedConstructibleExtendScalars X.left ℓ E).obj A) :=
    { rightDual := _
      exact := ExactPairing.map (boundedConstructibleExtendScalars X.left ℓ E) A Aᘁ }
  let : HasRightDual ((constructibleToPadicAlgCl X.left ℓ E).obj
      ((boundedConstructibleExtendScalars X.left ℓ E).obj A)) :=
    inferInstanceAs (HasRightDual ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj A))
  have h₁ := (boundedConstructibleExtendScalars X.left ℓ E).map_trace f
  have h₂ := (constructibleToPadicAlgCl X.left ℓ E).map_trace
    ((boundedConstructibleExtendScalars X.left ℓ E).map f)
  refine h₂.trans ?_
  simp only [h₁]
  simp only [Functor.map_comp, comp_ε, comp_η, Functor.comp_map, Category.assoc]

section Point

open MonObj PadicAlgCl

variable (ℓ k)

/-- The single complex functor `Mod_{𝒪̲_E,s} ⥤ D(Mod_{𝒪̲_E,s})` in degree `0`. -/
noncomputable abbrev pointIntegersSingleFunctor :
    PointModIntegral ℓ k E ⥤ DerivedCategory (PointModIntegral ℓ k E) :=
  HomologicalComplex.single (PointModIntegral ℓ k E) (ComplexShape.up ℤ) 0 ⋙
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The unit of the localization `Qh` is an isomorphism. -/
instance : IsIso (ε (DerivedCategory.Qh (C := PointModIntegral ℓ k E))) :=
  inferInstanceAs (IsIso (𝟙 _))

/-- The scalars `𝒪_E` acting on the unit of `D(Mod_{𝒪̲_E,s})`. -/
noncomputable def pointIntegersDerivedUnitEndRingHom :
    integers ℓ E.1 →+* End (𝟙_ (DerivedCategory (PointModIntegral ℓ k E))) :=
  (asIso (ε (DerivedCategory.Qh (C := PointModIntegral ℓ k E)))).symm.conjRingEquiv.toRingHom.comp
    (((pointIntegersSingleFunctor ℓ k E).mapEndRingHom (𝟙_ (PointModIntegral ℓ k E))).comp
      (pointIntegersUnitEndRingHom ℓ k E))

/-- The endomorphisms of the unit of `Dᵇc(Spec k)⟦𝒪̲_E⟧` are those of `D(Mod_{𝒪̲_E,s})`. -/
noncomputable def pointIntegersBoundedConstructibleUnitEndRingEquiv :
    End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)) ≃+*
      End (𝟙_ (DerivedCategory (PointModIntegral ℓ k E))) :=
  RingEquiv.ofBijective ((ObjectProperty.ι _).mapEndRingHom (𝟙_
      (Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)))
    ((ObjectProperty.fullyFaithfulι _).mulEquivEnd _).bijective

/-- The scalars `𝒪_E` acting on the unit of `Dᵇc(Spec k)⟦𝒪̲_E⟧`: a scalar `a` acts on `𝒪_{E,s}` by
multiplication by the constant global section `a`, placed in degree `0`. -/
noncomputable def pointIntegersBoundedConstructibleUnitEndRingHom :
    integers ℓ E.1 →+*
      End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)) :=
  (pointIntegersBoundedConstructibleUnitEndRingEquiv ℓ k E).symm.toRingHom.comp
    (pointIntegersDerivedUnitEndRingHom ℓ k E)

variable {ℓ k} [IsSepClosed k]

omit [Fact (ringChar k).Prime] in
/-- For `k` separably closed, every endomorphism of the unit of `Dᵇc(Spec k)⟦𝒪̲_E⟧` is a scalar
of `𝒪_E`. -/
theorem surjective_pointIntegersBoundedConstructibleUnitEndRingHom :
    Function.Surjective (pointIntegersBoundedConstructibleUnitEndRingHom ℓ k E) := by
  let A := PointModIntegral ℓ k E
  have : (pointIntegersSingleFunctor ℓ k E).Full := Functor.Full.of_iso
    ((DerivedCategory.singleFunctorIsoCompQ A 0).trans
      (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso A).symm))
  have : (pointIntegersSingleFunctor ℓ k E).Faithful := Functor.Faithful.of_iso
    ((DerivedCategory.singleFunctorIsoCompQ A 0).trans
      (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso A).symm))
  have hF : Function.Bijective
      ((pointIntegersSingleFunctor ℓ k E).mapEndRingHom (𝟙_ (PointModIntegral ℓ k E))) :=
    ((Functor.FullyFaithful.ofFullyFaithful (pointIntegersSingleFunctor ℓ k E)).mulEquivEnd
      (𝟙_ (PointModIntegral ℓ k E))).bijective
  intro y
  obtain ⟨z, hz⟩ := (RingEquiv.bijective
    (pointIntegersBoundedConstructibleUnitEndRingEquiv ℓ k E).symm).2 y
  obtain ⟨z', hz'⟩ := (RingEquiv.bijective
    (asIso (ε (DerivedCategory.Qh (C := PointModIntegral ℓ k E)))).symm.conjRingEquiv).2 z
  obtain ⟨w, hw⟩ := hF.2 z'
  obtain ⟨r, hr⟩ := surjective_pointIntegersUnitEndRingHom ℓ k E w
  refine ⟨r, ?_⟩
  rw [← hz, ← hz', ← hw, ← hr]
  rfl

/-- **The extension of scalars `𝒪_E ⟶ ℚ̄_ℓ` is injective on the endomorphisms of the unit** over a
separably closed field: if `T(g) = 0` for an endomorphism `g` of the unit of `Dᵇc(Spec k)⟦𝒪̲_E⟧`,
then `g = 0`. -/
theorem eq_zero_of_boundedConstructibleIntegersToPadicAlgCl_map_eq_zero
    (g : 𝟙_ (Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) ⟶ 𝟙_ _)
    (h : (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map g = 0) : g = 0 := by
  let T := boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)
  let Tmap : End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)) →+*
      End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
    (Functor.Monoidal.εIso T).symm.conjRingEquiv.toRingHom.comp (T.mapEndRingHom (𝟙_ _))
  let ψ : integers ℓ E.1 →+* PadicAlgCl ℓ := (unitEndRingEquiv ℓ k).toRingHom.comp
    (Tmap.comp (pointIntegersBoundedConstructibleUnitEndRingHom ℓ k E))
  obtain ⟨r, hr⟩ := surjective_pointIntegersBoundedConstructibleUnitEndRingHom E (End.of g)
  have hψ : ψ r = 0 := by
    have : Tmap (End.of g) = 0 := by
      ext1
      change _ ≫ T.map g ≫ _ = _
      rw [h, Limits.zero_comp, Limits.comp_zero]
      rfl
    change unitEndRingEquiv ℓ k (Tmap (pointIntegersBoundedConstructibleUnitEndRingHom ℓ k E r)) = 0
    rw [hr, this, map_zero]
  by_contra hg
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hg (congrArg End.asHom ((map_zero _).symm.trans hr).symm)
  obtain ⟨s, N, hrs⟩ := PadicAlgCl.exists_mul_eq_pow_of_ne_zero hr0
  have h' := congrArg ψ hrs
  rw [map_mul, hψ, zero_mul, map_pow, map_natCast] at h'
  exact pow_ne_zero N (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) h'.symm

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
