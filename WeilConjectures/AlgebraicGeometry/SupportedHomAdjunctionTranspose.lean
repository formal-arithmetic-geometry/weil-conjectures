/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.CategoryTheory.R.RHomDerivedRoof
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.SupportedHomTransposeAux
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective

/-!
# The normalized supported-Hom map and the adjunction transpose

Source: blueprint `sec-smooth-purity/sk-thm-regular`, proof Step 5
(blueprint: lem-pur-supported-hom-adjunction-transpose).

The normalization is specified on every bounded-below injective complex. Naturality
then specifies it on every bounded-below object, independently of a resolution.
The degree-a single object is the canonical presentation of A[-a].
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Supported cohomology, as an additive-group-valued functor on D+.
Source: the definition of H^a RΓ_Z (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomCohomologyFunctor (a : ℤ) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.ι ⋙ supportedSectionsDerived A i ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}

/-- Morphisms from i_*A_Z in degree zero into the shifted bounded-below object.
Source: supported-Hom identification (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomMorphismFunctor (a : ℤ) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.ι ⋙
    shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) a ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
        ((supportedCoefficients A i).obj (ModuleCat.of A A))))

/-- The actual derived unit on a cochain representative, with the canonical localization
comparison on its source. Source: Stacks Tags 05TH, 05TI and the prescribed injective
normalization (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomDerivedUnit
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      (supportedSectionsDerived A i).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} A)).inv.app _ ≫
    (supportSections i A).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)

/-- The class of an abstract cycle of Γ_Z(I), transported by the actual derived unit.
Source: Stacks Tags 05TH, 05TI (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomCycleClass
    (I : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (s : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a) :
    (supportedHomCohomologyFunctor A i a).obj (DerivedCategory.Plus.Q.obj I) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a).map
    (supportedHomDerivedUnit A i I.obj)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) a).inv.app _
      ((((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).homologyπ a s))

/-- Evaluation at 1 on the degree-a cohomology of a map A[-a] → RΓ_Z(F).
This is the inverse of the cocycle-to-morphism identification in the statement.
Source: the specified cocycle convention
(blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomClassOfMorphism
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomCohomologyFunctor A i a).obj F :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a).map f
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u + 1} A) a).inv.app
      (ModuleCat.of A A) (1 : A))

variable [IsLocallyNoetherian X]

/-- Derive the normalized ordinary adjunction with its exact left adjoint.
Source: blueprint `def-pur-supported-exterior-product`, K-flat and injective derivation
(blueprint: def-pur-proetale-supported-exterior-product). -/
noncomputable def supportedCoefficientDerivedAdjunction :
    (supportedCoefficients A i).mapDerivedCategory ⊣ supportedSectionsDerived A i :=
  (supportedCoefficientAdjunction A i).mapDerivedCategoryRightDerivedAdjunction

/-- The adjoint of A[-a] → RΓ_Z(F), shifted by a. The two comparison isomorphisms
identify C_i(A[-a])[a] with C_i(A)[0]. Source: the cochain shift convention and the
normalized supported adjunction (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomShiftedTranspose
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomMorphismFunctor A i a).obj F :=
  ((DerivedCategory.singleFunctors
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).shiftIso a 0 a
      (add_zero a)).inv.app ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≫
    (((supportedCoefficients A i).mapDerivedCategorySingleFunctor a).inv.app
      (ModuleCat.of A A))⟦a⟧' ≫
    (((supportedCoefficientDerivedAdjunction A i).homEquiv _ _).symm f)⟦a⟧'

/-- The supported-Hom isomorphism has exactly the evaluation normalization on injectives.
For a cocycle f, its supported section is the ordinary adjoint evaluated at 1; the
ordinary quotient normalization identifies this with f_X(q_i(1)). The right side is
precisely the derived-Hom cocycle formula. Source: Stacks Tags 06XR, 070I
(blueprint: lem-pur-supported-hom-adjunction-transpose). -/
def SupportedHomEvaluationNormalization (a : ℤ)
    (χ : supportedHomCohomologyFunctor A i a ≅ supportedHomMorphismFunctor A i a) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_hi : ∀ r : ℤ, Injective (I.obj.X r))
    (f : (supportedCoefficients A i).obj (ModuleCat.of A A) ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0)
    (s : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a),
    (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).iCycles a s =
      ((supportedCoefficientAdjunction A i).homEquiv _ _ f) 1 →
    χ.hom.app (DerivedCategory.Plus.Q.obj I) (supportedHomCycleClass A i I a s) =
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app
          ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧'

/-- Finiteness of the coefficient quotient in the purity conventions.
Source: finite coefficient datum, sk-def-purity-conv
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
instance purityCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  haveI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

omit [IsLocallyNoetherian X] in
/-- Evaluation at `1` on the degree-`a` cohomology of a map `A[-a] ⟶ RΓ_Z(F)` is bijective,
since `A` is free of rank one. -/
lemma supportedHomClassOfMorphism_bijective
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) : Function.Bijective (supportedHomClassOfMorphism A i F a) := by
  have hev (M : ModuleCat.{u + 1} A) :
      Function.Bijective (fun φ : ModuleCat.of A A ⟶ M => φ (1 : A)) := by
    refine ⟨fun φ ψ h => ?_, fun m => ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton A M m), ?_⟩⟩
    · ext
      exact h
    · simp
  exact (hev _).comp (DerivedCategory.homSingleEquivOfProjective (ModuleCat.of A A) a
    ((supportedSectionsDerived A i).obj F.obj)).bijective

omit [IsLocallyNoetherian X] in
/-- The supported cohomology class of a map `A[-a] ⟶ RΓ_Z(F)`, as an additive equivalence. -/
noncomputable def supportedHomClassAddEquiv
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) :
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) ≃+
      (supportedHomCohomologyFunctor A i a).obj F :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (supportedHomClassOfMorphism A i F a)
      (fun _ _ => by simp [supportedHomClassOfMorphism]))
    (supportedHomClassOfMorphism_bijective A i F a)

omit [IsLocallyNoetherian X] in
lemma supportedHomClassAddEquiv_apply
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    supportedHomClassAddEquiv A i F a f = supportedHomClassOfMorphism A i F a f :=
  rfl

/-- The shifted transpose is bijective: it is the derived adjunction bijection, followed by
the shift and the composition with isomorphisms. -/
lemma supportedHomShiftedTranspose_bijective
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) : Function.Bijective (supportedHomShiftedTranspose A i F a) := by
  let e := ((DerivedCategory.singleFunctors
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).shiftIso a 0 a
      (add_zero a)).symm.app ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≪≫
    (shiftFunctor _ a).mapIso
      (((supportedCoefficients A i).mapDerivedCategorySingleFunctor a).symm.app
        (ModuleCat.of A A))
  have h : supportedHomShiftedTranspose A i F a = e.symm.homFromEquiv ∘
      (fun φ => (shiftFunctor _ a).map φ) ∘
      ((supportedCoefficientDerivedAdjunction A i).homEquiv _ _).symm := by
    funext f
    simp [supportedHomShiftedTranspose, e]
  rw [h]
  exact e.symm.homFromEquiv.bijective.comp
    (((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ a)).map_bijective _ _).comp
    ((supportedCoefficientDerivedAdjunction A i).homEquiv _ _).symm.bijective)

/-- The shifted transpose, as an additive equivalence. -/
noncomputable def supportedHomShiftedTransposeAddEquiv
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ) :
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) ≃+
      (supportedHomMorphismFunctor A i a).obj F :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (supportedHomShiftedTranspose A i F a)
      (fun _ _ => by simp [supportedHomShiftedTranspose]))
    (supportedHomShiftedTranspose_bijective A i F a)

omit [IsLocallyNoetherian X] in
/-- Naturality of the supported cohomology class of a map `A[-a] ⟶ RΓ_Z(F)`. -/
lemma supportedHomClassOfMorphism_naturality
    {F G : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (g : F ⟶ G) (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomCohomologyFunctor A i a).map g (supportedHomClassOfMorphism A i F a f) =
      supportedHomClassOfMorphism A i G a
        (f ≫ (supportedSectionsDerived A i).map (DerivedCategory.Plus.ι.map g)) := by
  simp [supportedHomCohomologyFunctor, supportedHomClassOfMorphism]

/-- Naturality of the shifted transpose. -/
lemma supportedHomShiftedTranspose_naturality
    {F G : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (g : F ⟶ G) (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomMorphismFunctor A i a).map g (supportedHomShiftedTranspose A i F a f) =
      supportedHomShiftedTranspose A i G a
        (f ≫ (supportedSectionsDerived A i).map (DerivedCategory.Plus.ι.map g)) := by
  simp [supportedHomMorphismFunctor, supportedHomShiftedTranspose,
    Adjunction.homEquiv_naturality_right_symm, preadditiveCoyoneda_obj_map_apply]

/-- The component at `F` of the supported-Hom isomorphism: the inverse of the cohomology class
of maps `A[-a] ⟶ RΓ_Z(F)`, followed by the shifted transpose. -/
noncomputable def supportedHomIsoApp (a : ℤ)
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (supportedHomCohomologyFunctor A i a).obj F ≅ (supportedHomMorphismFunctor A i a).obj F :=
  ((supportedHomClassAddEquiv A i F a).symm.trans
    (supportedHomShiftedTransposeAddEquiv A i F a)).toAddCommGrpIso

lemma supportedHomIsoApp_hom_apply (a : ℤ)
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomIsoApp A i a F).hom (supportedHomClassOfMorphism A i F a f) =
      supportedHomShiftedTranspose A i F a f :=
  congrArg (supportedHomShiftedTranspose A i F a)
    ((supportedHomClassAddEquiv A i F a).symm_apply_apply f)

/-- The supported-Hom isomorphism: the inverse of the cohomology class of maps
`A[-a] ⟶ RΓ_Z(F)`, followed by the shifted transpose. -/
noncomputable def supportedHomIso (a : ℤ) :
    supportedHomCohomologyFunctor A i a ≅ supportedHomMorphismFunctor A i a :=
  NatIso.ofComponents (supportedHomIsoApp A i a) (fun {F G} g => by
    ext x
    obtain ⟨f, rfl⟩ := (supportedHomClassAddEquiv A i F a).surjective x
    rw [supportedHomClassAddEquiv_apply, AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply,
      supportedHomClassOfMorphism_naturality, supportedHomIsoApp_hom_apply,
      supportedHomIsoApp_hom_apply, supportedHomShiftedTranspose_naturality])

lemma supportedHomIso_hom_app_supportedHomClassOfMorphism (a : ℤ)
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomIso A i a).hom.app F (supportedHomClassOfMorphism A i F a f) =
      supportedHomShiftedTranspose A i F a f :=
  supportedHomIsoApp_hom_apply A i a F f

omit [IsLocallyNoetherian X] in
/-- The class of an abstract cycle `s` of `Γ_Z(I)` is the class of the localized cochain map
`A[-a] ⟶ Γ_Z(I)` sending `1` to `s`, followed by the derived unit. -/
lemma supportedHomCycleClass_eq_supportedHomClassOfMorphism
    (I : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (b : ModuleCat.of A A ⟶
      (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).X a)
    (hb : ∀ k, (ComplexShape.up ℤ).Rel a k →
      b ≫ (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).d a k = 0)
    (s : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a)
    (hs : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      I.obj).iCycles a s = b 1) :
    supportedHomCycleClass A i I a s =
      supportedHomClassOfMorphism A i (DerivedCategory.Plus.Q.obj I) a
        (DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle b hb) ≫
          supportedHomDerivedUnit A i I.obj) := by
  have h := DerivedCategory.homSingleToHomology_Q_map_mkHomFromSingle (ModuleCat.of A A) a _ b hb
  rw [← Iso.app_hom, ← Iso.eq_comp_inv] at h
  have hs' : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      I.obj).liftCycles b (a + 1) (by simp) (hb _ rfl) 1 = s := by
    apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles _ a)).1 inferInstance
    rw [hs, ← ModuleCat.comp_apply, HomologicalComplex.liftCycles_i]
  have h1 := congrArg (fun φ => φ (1 : A)) h
  simp only [DerivedCategory.homSingleToHomology, Iso.app_inv, CategoryTheory.comp_apply] at h1
  rw [hs'] at h1
  simp only [supportedHomCycleClass, supportedHomClassOfMorphism, Functor.map_comp,
    CategoryTheory.comp_apply]
  exact congrArg (fun y => (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a).map
    (supportedHomDerivedUnit A i I.obj) y) h1.symm

/-- The canonical, evaluation-normalized supported-Hom isomorphism equals the shifted
transpose under the supported adjunction. Source: blueprint sk-thm-regular, proof Step 5
(blueprint: lem-pur-supported-hom-adjunction-transpose).

Proof:
1. Put P=C_i(A) and G=Γ_Z. The quotient normalization of
   def-pur-proetale-supported-exterior-product identifies the ordinary adjoint b of f
   by f_X(q_i(1))=b(1). Evaluation at 1 identifies Hom_A(A,G(M)) with G(M), naturally.
2. On the chosen small pro-etale site, prop-pur-kinjective-resolutions-exist and
   lem-sp-grothendieck-enough-injectives supply injectives. By
   lem-sc-bounded-below-injective-resolution choose F→I, bounded below, termwise
   injective and K-injective. The derived unit computes RG there, by
   lem-weil-pbc-right-derived-plus-injective.
3. The ordinary evaluation bijection is a natural additive isomorphism. Apply it
   degreewise to I and derive its inverse. Uniqueness of the right-derived extension
   identifies the result on I with its termwise map, sending s to its ordinary adjoint f_s.
4. By lem-sc-p1-rhom-hom-derived-roof, f_s represents the derived morphism
   P[0]→I[a]→F[a]. This gives χ, its naturality, and the displayed normalization.
5. By lem-sc-derived-adjunction-from-underived the derived counit on I is the
   localized ordinary counit. Hence the transpose of the map taking 1 to s is
   P[-a]→I→F, with degree-a component f_s.
6. Shift by a, using (K[a])^r=K^(r+a). Components of a degree-zero map do not change,
   so this is the same map as in step 4. Boundaries give homotopies with component
   (-1)^a f_t after shifting. Naturality transports both formulas from I to F.
   Every cohomology class is represented by a map A[-a]→RG(F), because A is free of
   rank one. Thus the quantified formula is χ(x)=x^flat[a] for every class x. -/
theorem supportedHom_adjunction_transpose (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] (a : ℤ) :
    ∃ χ : supportedHomCohomologyFunctor P.Coefficient i a ≅
        supportedHomMorphismFunctor P.Coefficient i a,
      SupportedHomEvaluationNormalization P.Coefficient i a χ ∧
      ∀ (F : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
        (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} P.Coefficient) a).obj
            (ModuleCat.of P.Coefficient P.Coefficient) ⟶
          (supportedSectionsDerived P.Coefficient i).obj F.obj),
        χ.hom.app F (supportedHomClassOfMorphism P.Coefficient i F a f) =
          supportedHomShiftedTranspose P.Coefficient i F a f := by
  refine ⟨supportedHomIso P.Coefficient i a, ?_,
    supportedHomIso_hom_app_supportedHomClassOfMorphism P.Coefficient i a⟩
  intro I _ f hf s hs
  rw [supportedHomCycleClass_eq_supportedHomClassOfMorphism P.Coefficient i I a
    ((supportedCoefficientAdjunction P.Coefficient i).homEquiv _ _ f) (fun j hj => by
      obtain rfl : a + 1 = j := hj
      exact (supportedCoefficientAdjunction P.Coefficient i).homEquiv_comp_eq_zero f _ hf) s hs,
    supportedHomIso_hom_app_supportedHomClassOfMorphism]
  exact Adjunction.mapDerivedCategoryRightDerivedAdjunction_shiftedTranspose
    (supportedCoefficientAdjunction P.Coefficient i)
    (ModuleCat.of P.Coefficient P.Coefficient) I.obj a f hf

end AlgebraicGeometry.ProEtale
