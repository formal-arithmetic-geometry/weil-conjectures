/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteRationalDerivedOperations
public import WeilConjectures.Algebra.Homology.SitePerfectScalarHomComparison
public import WeilConjectures.CategoryTheory.ExactEquivalenceDerivedSquares
import WeilConjectures.CategoryTheory.CochainUniversalCounitTransport
@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Opposite AlgebraicGeometry WeilConjectures
open AlgebraicGeometry.Scheme
namespace WeilConjectures
private def prescribedOrdinaryIso
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    (O : C → D) (f : ∀ {M N : C}, (M ⟶ N) → (O M ⟶ O N))
    (a : ∀ M, F.obj M = O M) (b : ∀ M, G.obj M = O M)
    (ha : ∀ {M N} (g : M ⟶ N),
      F.map g = eqToHom (a M) ≫ f g ≫ eqToHom (a N).symm)
    (hb : ∀ {M N} (g : M ⟶ N),
      G.map g = eqToHom (b M) ≫ f g ≫ eqToHom (b N).symm) : F ≅ G :=
  NatIso.ofComponents (fun M ↦ eqToIso ((a M).trans (b M).symm)) (by
    intro M N g
    simp only [ha, hb, eqToIso.hom, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans])

private theorem prescribedKanIso
    {C D H : Type*} [Category C] [Category D] [Category H]
    (Q : C ⥤ D) (F G : C ⥤ H) (S T : D ⥤ H)
    (α : Q ⋙ S ⟶ F) (β : Q ⋙ T ⟶ G)
    (hα : S.IsRightKanExtension α) (hβ : T.IsRightKanExtension β) (b : F ≅ G) :
    ∃ e : S ≅ T, ∀ P, e.hom.app (Q.obj P) ≫ β.app P = α.app P ≫ b.hom.app P := by
  letI := hα
  letI := hβ
  let e := Functor.rightKanExtensionUniqueOfIso S α b T β
  refine ⟨e, fun P ↦ ?_⟩
  exact T.liftOfIsRightKanExtension_fac_app β S (α ≫ b.hom) P

/-- The universal derived scalar extension is identified with the explicit finite quotient
model by an isomorphism normalized against the two universal counits. The ordinary
comparison is required to be the componentwise equality induced by the prescribed
object equations, so the derived comparison cannot be rescaled.
Source: Stacks 06YY; (blueprint: lem-sf-finite-quotient-hom-model-comparison-existence).

Proof: identify the ordinary extensions using the object and map equations carried by
the scalar model and by the finite quotient calculus. Transport the finite quotient
counit across this componentwise ordinary isomorphism. The uniqueness theorem for
left-derived functors then supplies an isomorphism whose hom is compatible with the
two counits at every cochain complex. -/
theorem finiteQuotient_homModel_comparison_exists
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n)
    [EssentiallySmall.{max u (u + 1)} W.ProEt]
    (A : SitePerfectScalarHomData.{u + 1, u, u, u + 2} (ProEt.topology W)
      (coefficientFiniteQuotient l E W h)) :
    ∃ (e : (SheafOfModules.DerivedChangeOfRingsCochainModel.T.{u + 1, u, u + 1, u + 2, u + 2}
        (SitePerfectScalarHomData.scalar.{u + 1, u, u, u + 2} A) ≅
          coefficientFiniteQuotientDerived l E W h))
      (o : (SitePerfectScalarHomData.scalar.{u + 1, u, u, u + 2} A).E ≅
        coefficientFiniteQuotientExtension l E W h),
      (∀ M, o.hom.app M =
        eqToHom (((SitePerfectScalarHomData.scalar A).obj_eq M).trans
          (coefficientFiniteQuotientExtension_obj l E W h M).symm)) ∧
      (letI : (coefficientFiniteQuotientExtension l E W h).PreservesZeroMorphisms := by
        letI : (coefficientFiniteQuotientExtension l E W h).Additive :=
          coefficientFiniteQuotientExtensionAdditive l E W h
        exact CategoryTheory.Functor.preservesZeroMorphisms_of_additive _
      ∀ P : CochainComplex (normalizedDVRModules l E W n) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫
            (CategoryTheory.derivedCochainCounit
              (coefficientFiniteQuotientExtension l E W h)
              (coefficientFiniteQuotientDerived l E W h)
              (coefficientFiniteQuotientCounit l E W h)).app P =
          (SitePerfectScalarHomData.scalar A).ε.app P ≫
            DerivedCategory.Q.map
            (show ((SitePerfectScalarHomData.scalar A).E.mapHomologicalComplex (.up ℤ)).obj P ⟶
                ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
                  (.up ℤ)).obj P from
              { f := fun i => o.hom.app (P.X i)
                comm' := by
                  intro i j _hij
                  change o.hom.app (P.X i) ≫
                      (coefficientFiniteQuotientExtension l E W h).map (P.d i j) =
                    (SitePerfectScalarHomData.scalar A).E.map (P.d i j) ≫
                      o.hom.app (P.X j)
                  exact (o.hom.naturality (P.d i j)).symm })) := by
  classical
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W m)
  let o : (show normalizedDVRModules l E W n ⥤ normalizedDVRModules l E W m
      from (SitePerfectScalarHomData.scalar A).E) ≅
      coefficientFiniteQuotientExtension l E W h :=
    prescribedOrdinaryIso _ _ _ (fun {_ _} f ↦
      SheafOfModules.changeOfRingsHom (coefficientFiniteQuotient l E W h) _ f)
      (SitePerfectScalarHomData.scalar A).obj_eq
      (coefficientFiniteQuotientExtension_obj l E W h)
      (SitePerfectScalarHomData.scalar A).map_eq
      (coefficientFiniteQuotientExistence l E W h).choose_spec.choose_spec.choose
  have ho : ∀ M, o.hom.app M =
      eqToHom (((SitePerfectScalarHomData.scalar A).obj_eq M).trans
        (coefficientFiniteQuotientExtension_obj l E W h M).symm) := by
    intro M
    rfl
  letI : (coefficientFiniteQuotientExtension l E W h).PreservesZeroMorphisms := by
    letI : (coefficientFiniteQuotientExtension l E W h).Additive :=
      coefficientFiniteQuotientExtensionAdditive l E W h
    exact CategoryTheory.Functor.preservesZeroMorphisms_of_additive _
  let T := coefficientFiniteQuotientDerived l E W h
  let ε := coefficientFiniteQuotientCounit l E W h
  letI : T.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (normalizedDVRModules l E W n) (.up ℤ)) :=
    (coefficientFiniteQuotientDerivedExistence l E W h).choose_spec.choose_spec.1
  have hε : T.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension T ε
      (HomotopyCategory.quasiIso (normalizedDVRModules l E W n) (.up ℤ))
  letI : T.IsRightKanExtension ε := hε
  let β := CategoryTheory.derivedCochainCounit
    (coefficientFiniteQuotientExtension l E W h) T ε
  have hβ := CategoryTheory.cochainUniversalCounitTransport
    (coefficientFiniteQuotientExtension l E W h) T ε
  letI : (show normalizedDVRModules l E W n ⥤ normalizedDVRModules l E W m
      from (SitePerfectScalarHomData.scalar A).E).PreservesZeroMorphisms :=
    inferInstanceAs (SitePerfectScalarHomData.scalar A).E.PreservesZeroMorphisms
  let b := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex o (.up ℤ))
    (DerivedCategory.Q (C := normalizedDVRModules l E W m))
  letI := (SitePerfectScalarHomData.scalar A).universal
  have hA : (SitePerfectScalarHomData.scalar A).T.IsRightKanExtension
      (SitePerfectScalarHomData.scalar A).ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso
        (ringedSiteModules.{u + 1, u + 1, u, u + 1}
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
            (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n))) (.up ℤ))
  obtain ⟨e, he⟩ := prescribedKanIso
    (DerivedCategory.Q (C := normalizedDVRModules l E W n)) _ _
    (show normalizedDVRDerived l E W n ⥤ normalizedDVRDerived l E W m
      from (SitePerfectScalarHomData.scalar A).T) T
    (SitePerfectScalarHomData.scalar A).ε β hA hβ.1 b
  refine ⟨e, o, ho, ?_⟩
  intro P
  exact he P
end WeilConjectures
