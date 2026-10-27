module

public import Sheaf.RingTheory.CotangentSheafModel
public import Sheaf.RingTheory.CotangentLowerShriek
public import Mathlib.RingTheory.Kaehler.Basic
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.CategoryTheory.DerivedColimitBar
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # The canonical differential sequence on polynomial pairs

Source: Stacks Project, Cotangent Complex, Tag 08QU (lemma-triangle-ses), and
Algebra, Tags 00RV and 00RX
(blueprint: lem-trf-cotangent-differential-presheaf-ses).

The record specifies the canonical arrows by their values on universal differential
generators. It includes their presheaf naturality, actual tensor identifications,
short exactness, and the inclusion/projection formula in every polynomial coordinate system.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings TensorProduct

namespace Algebra.CotangentSheaf

/-- The actual scalar-extended differential module, with the tensor factors reversed.
Source: Stacks 08PU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def tensorTerm {R P T : CommRingCat.{u}} (base : R ⟶ P) (aug : P ⟶ T) :
    ModuleCat.{u} T :=
  (ModuleCat.extendScalars aug.hom).obj (CommRingCat.KaehlerDifferential base)

/-- The pure differential tensor `c ⊗ dx` in the actual coefficient module.
Source: Stacks 08PU and 08QL (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def tensorD {R P T : CommRingCat.{u}} (base : R ⟶ P) (aug : P ⟶ T)
    (c : T) (x : P) : tensorTerm base aug :=
  c ⊗ₜ[P, aug.hom] CommRingCat.KaehlerDifferential.d x

/-- The coefficient presheaf on the full polynomial-presentation site. The isomorphisms
and the formula fix both its values and all restriction maps, exactly as `Coefficients`
does on the coordinate model. Source: Stacks 08PU and 08QL
(blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
structure SiteCoefficients {A T : CommRingCat.{u}} (f : A ⟶ T) where
  functor : (CotangentSites.Site f)ᵒᵖ ⥤ ModuleCat.{u} T
  terms : ∀ U : (CotangentSites.Site f)ᵒᵖ,
    functor.obj U ≅ tensorTerm ((CotangentSites.presentationBase f).app U)
      ((CotangentSites.presentationAugmentation f).app U)
  formula : ∀ {U V : (CotangentSites.Site f)ᵒᵖ} (h : U ⟶ V) (c : T)
    (x : (CotangentSites.presentationRing f).obj U),
    (terms V).hom (functor.map h ((terms U).inv
      (tensorD ((CotangentSites.presentationBase f).app U)
        ((CotangentSites.presentationAugmentation f).app U) c x))) =
    tensorD ((CotangentSites.presentationBase f).app V)
      ((CotangentSites.presentationAugmentation f).app V) c
      ((CotangentSites.presentationRing f).map h x)


private theorem tensor_ext {R P T : CommRingCat.{u}} {base : R ⟶ P} {aug : P ⟶ T}
    {N : ModuleCat.{u} T} {a b : tensorTerm base aug ⟶ N}
    (h : ∀ c x, a (tensorD base aug c x) = b (tensorD base aug c x)) : a = b := by
  apply (ModuleCat.extendRestrictScalarsAdj aug.hom).homEquiv _ _ |>.injective
  apply CommRingCat.KaehlerDifferential.ext
  intro x
  exact h 1 x

private def tensorDesc {R P T : CommRingCat.{u}} (base : R ⟶ P) (aug : P ⟶ T)
    {N : ModuleCat.{u} T} (d : ((ModuleCat.restrictScalars aug.hom).obj N).Derivation base) :
    tensorTerm base aug ⟶ N :=
  (ModuleCat.extendRestrictScalarsAdj aug.hom).homEquiv _ _ |>.symm d.desc

private theorem tensorDesc_D {R P T : CommRingCat.{u}} (base : R ⟶ P) (aug : P ⟶ T)
    {N : ModuleCat.{u} T} (d : ((ModuleCat.restrictScalars aug.hom).obj N).Derivation base)
    (c : T) (x : P) : tensorDesc base aug d (tensorD base aug c x) = c • d.d x := by
  have h := congrArg (fun k ↦ k (CommRingCat.KaehlerDifferential.d x))
    ((ModuleCat.extendRestrictScalarsAdj aug.hom).homEquiv _ _ |>.apply_symm_apply d.desc)
  change tensorDesc base aug d (tensorD base aug 1 x) = _ at h
  rw [ModuleCat.Derivation.desc_d] at h
  calc
    _ = tensorDesc base aug d (c • tensorD base aug 1 x) := by
      congr 1
      change c ⊗ₜ[P, aug.hom] _ = c • ((1 : T) ⊗ₜ[P, aug.hom] _)
      rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    _ = _ := by rw [map_smul, h]

private theorem tensorD_add {R P T : CommRingCat.{u}} (base : R ⟶ P) (aug : P ⟶ T)
    (x y : P) : tensorD base aug 1 (x + y) =
      tensorD base aug 1 x + tensorD base aug 1 y := by
  simp [tensorD, CommRingCat.KaehlerDifferential.d, TensorProduct.tmul_add]

private theorem tensorD_mul {R P T : CommRingCat.{u}} (base : R ⟶ P) (aug : P ⟶ T)
    (x y : P) : tensorD base aug 1 (x * y) =
      aug x • tensorD base aug 1 y + aug y • tensorD base aug 1 x := by
  let := aug.hom.toAlgebra
  let d := CommRingCat.KaehlerDifferential.D base
  change (1 : T) ⊗ₜ[P, aug.hom] d.d (x * y) = _
  rw [d.d_mul, TensorProduct.tmul_add]
  congr 1 <;>
    rw [TensorProduct.tmul_smul]
  all_goals
    change (aug.hom _ * 1) ⊗ₜ[P, aug.hom] _ = _
    rw [mul_one]
    symm
    exact (ModuleCat.ExtendScalars.smul_tmul _ _ _ _).trans (by rw [mul_one])

private theorem tensorD_base {R P T : CommRingCat.{u}} (base : R ⟶ P) (aug : P ⟶ T)
    (r : R) : tensorD base aug 1 (base r) = 0 := by
  simp [tensorD, CommRingCat.KaehlerDifferential.d]

private theorem tensorD_base_any {R P T : CommRingCat.{u}} (base : R ⟶ P)
    (aug : P ⟶ T) (c : T) (r : R) : tensorD base aug c (base r) = 0 := by
  unfold tensorD
  rw [show CommRingCat.KaehlerDifferential.d (base r) = 0 from
    (CommRingCat.KaehlerDifferential.D base).d_map r, TensorProduct.tmul_zero]

attribute [irreducible] tensorDesc

private def tensorMap {R S P Q T : CommRingCat.{u}}
    (base : R ⟶ P) (base' : S ⟶ Q) (aug : P ⟶ T) (aug' : Q ⟶ T)
    (r : R ⟶ S) (h : P ⟶ Q) (hb : base ≫ h = r ≫ base')
    (ha : h ≫ aug' = aug) : tensorTerm base aug ⟶ tensorTerm base' aug' :=
  tensorDesc base aug (ModuleCat.Derivation.mk
    (fun x ↦ tensorD base' aug' 1 (h x))
    (by intro x y; rw [map_add, tensorD_add])
    (by
      intro x y
      rw [map_mul, tensorD_mul]
      change aug' (h x) • tensorD base' aug' 1 (h y) +
          aug' (h y) • tensorD base' aug' 1 (h x) =
        aug x • tensorD base' aug' 1 (h y) + aug y • tensorD base' aug' 1 (h x)
      rw [← CommRingCat.comp_apply, ha, ← CommRingCat.comp_apply, ha])
    (by
      intro x
      have hx := congrArg (fun k ↦ k x) hb
      change h (base x) = base' (r x) at hx
      rw [hx, tensorD_base]))

private theorem tensorMap_D {R S P Q T : CommRingCat.{u}}
    (base : R ⟶ P) (base' : S ⟶ Q) (aug : P ⟶ T) (aug' : Q ⟶ T)
    (r : R ⟶ S) (h : P ⟶ Q) (hb : base ≫ h = r ≫ base')
    (ha : h ≫ aug' = aug) (c : T) (x : P) :
    tensorMap base base' aug aug' r h hb ha (tensorD base aug c x) =
      tensorD base' aug' c (h x) := by
  rw [tensorMap, tensorDesc_D]
  change c • ((1 : T) ⊗ₜ[Q, aug'.hom] _) = c ⊗ₜ[Q, aug'.hom] _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]


private theorem extendScalars_map_tmul {B T : CommRingCat.{u}} (g : B ⟶ T)
    {M N : ModuleCat.{u} B} (l : M ⟶ N) (c : T) (x : M) :
    (ModuleCat.extendScalars g.hom).map l (c ⊗ₜ[B, g.hom] x) =
      c ⊗ₜ[B, g.hom] l x := rfl

attribute [irreducible] tensorMap

private def siteCoefficients {A T : CommRingCat.{u}} (f : A ⟶ T) : SiteCoefficients f where
  functor :=
    { obj := fun U ↦ tensorTerm ((CotangentSites.presentationBase f).app U)
        ((CotangentSites.presentationAugmentation f).app U)
      map := fun h ↦ tensorMap _ _ _ _ (𝟙 A) ((CotangentSites.presentationRing f).map h)
        (by simpa using ((CotangentSites.presentationBase f).naturality h).symm)
        (by simp)
      map_id := by
        intro U
        apply tensor_ext
        intro c x
        simp [tensorMap_D]
      map_comp := by
        intro U V W h k
        apply tensor_ext
        intro c x
        simp [tensorMap_D] }
  terms := fun _ ↦ Iso.refl _
  formula := by
    intro U V h c x
    simpa using tensorMap_D _ _ _ _ _ _ _ _ c x

private theorem siteCoefficients_map_D {A T : CommRingCat.{u}} (f : A ⟶ T)
    {U V : (CotangentSites.Site f)ᵒᵖ} (h : U ⟶ V) (c : T)
    (x : (CotangentSites.presentationRing f).obj U) :
    (siteCoefficients f).functor.map h (tensorD _ _ c x) =
      tensorD _ _ c ((CotangentSites.presentationRing f).map h x) := by
  exact tensorMap_D _ _ _ _ (𝟙 A) _
    (by simpa using ((CotangentSites.presentationBase f).naturality h).symm)
    (by simp) c x


private def tensorIso {R P Q T : CommRingCat.{u}} (base : R ⟶ P) (base' : R ⟶ Q)
    (aug : P ⟶ T) (aug' : Q ⟶ T) (e : P ≅ Q)
    (hb : base ≫ e.hom = base') (ha : e.hom ≫ aug' = aug) :
    tensorTerm base aug ≅ tensorTerm base' aug' where
  hom := tensorMap base base' aug aug' (𝟙 R) e.hom (by simpa using hb) ha
  inv := tensorMap base' base aug' aug (𝟙 R) e.inv
    (by rw [← hb]; simp) (by rw [← ha]; simp)
  hom_inv_id := by
    apply tensor_ext
    intro c x
    simp [tensorMap_D]
  inv_hom_id := by
    apply tensor_ext
    intro c x
    simp [tensorMap_D]



private theorem tensorIso_hom_D {R P Q T : CommRingCat.{u}}
    (base : R ⟶ P) (base' : R ⟶ Q) (aug : P ⟶ T) (aug' : Q ⟶ T) (e : P ≅ Q)
    (hb : base ≫ e.hom = base') (ha : e.hom ≫ aug' = aug) (c : T) (x : P) :
    (tensorIso base base' aug aug' e hb ha).hom (tensorD base aug c x) =
      tensorD base' aug' c (e.hom x) :=
  tensorMap_D _ _ _ _ (𝟙 R) e.hom (by simpa using hb) ha c x

private theorem tensorIso_inv_D {R P Q T : CommRingCat.{u}}
    (base : R ⟶ P) (base' : R ⟶ Q) (aug : P ⟶ T) (aug' : Q ⟶ T) (e : P ≅ Q)
    (hb : base ≫ e.hom = base') (ha : e.hom ≫ aug' = aug) (c : T) (x : Q) :
    (tensorIso base base' aug aug' e hb ha).inv (tensorD base' aug' c x) =
      tensorD base aug c (e.inv x) :=
  tensorMap_D _ _ _ _ (𝟙 R) e.inv (by rw [← hb]; simp) (by rw [← ha]; simp) c x


attribute [irreducible] tensorIso

private def extendTensorIso {P T : CommRingCat.{u}} (a : P ⟶ T) (M : ModuleCat.{u} P) :
    (ModuleCat.extendScalars a.hom).obj M ≅
      (let := a.hom.toAlgebra; ModuleCat.of T (T ⊗[P] M)) := by
  let := a.hom.toAlgebra
  exact Iso.refl _

private theorem extendTensorIso_tmul {P T : CommRingCat.{u}} (a : P ⟶ T)
    (M : ModuleCat.{u} P) (c : T) (x : M) :
    (extendTensorIso a M).hom (c ⊗ₜ[P, a.hom] x) =
      (let := a.hom.toAlgebra; c ⊗ₜ[P] x) := by
  rfl

private def kaehlerChangeAlgebra (R P : CommRingCat.{u})
    (a b : Algebra R P) (h : a = b) :
    (letI := a; ModuleCat.of P (KaehlerDifferential R P)) ≅
      (letI := b; ModuleCat.of P (KaehlerDifferential R P)) := by
  subst b
  exact Iso.refl _

private theorem kaehlerChangeAlgebra_D (R P : CommRingCat.{u})
    (a b : Algebra R P) (h : a = b) (x : P) :
    (kaehlerChangeAlgebra R P a b h).hom
      (letI := a; KaehlerDifferential.D R P x) =
      (letI := b; KaehlerDifferential.D R P x) := by
  subst b
  rfl

private def kaehlerAlgebraIso (R P : CommRingCat.{u}) [Algebra R P]
    (f : R ⟶ P) (hf : f.hom = algebraMap R P) :
    CommRingCat.KaehlerDifferential f ≅ ModuleCat.of P (KaehlerDifferential R P) :=
  kaehlerChangeAlgebra R P f.hom.toAlgebra inferInstance
    ((congrArg RingHom.toAlgebra hf).trans toAlgebra_algebraMap)

private theorem kaehlerAlgebraIso_D (R P : CommRingCat.{u}) [Algebra R P]
    (f : R ⟶ P) (hf : f.hom = algebraMap R P) (x : P) :
    (kaehlerAlgebraIso R P f hf).hom (CommRingCat.KaehlerDifferential.d x) =
      KaehlerDifferential.D R P x :=
  kaehlerChangeAlgebra_D R P _ _ _ x

private def polynomialBasisIso (R T : CommRingCat.{u}) (S : Type u)
    (a : CommRingCat.of (MvPolynomial S R) ⟶ T) :
    tensorTerm (CommRingCat.ofHom MvPolynomial.C) a ≅ ModuleCat.of T (S →₀ T) := by
  let := a.hom.toAlgebra
  exact (ModuleCat.extendScalars a.hom).mapIso
      (kaehlerAlgebraIso R (CommRingCat.of (MvPolynomial S R))
        (CommRingCat.ofHom MvPolynomial.C) (MvPolynomial.C_eq_algebraMap R S)) ≪≫
    extendTensorIso a _ ≪≫
    ((KaehlerDifferential.mvPolynomialBasis R S).baseChange T).repr.toModuleIso

private theorem polynomialBasisIso_D (R T : CommRingCat.{u}) (S : Type u)
    (a : CommRingCat.of (MvPolynomial S R) ⟶ T) (s : S) (c : T) :
    (polynomialBasisIso R T S a).hom
      (tensorD (CommRingCat.ofHom MvPolynomial.C) a c (MvPolynomial.X s)) =
      Finsupp.single s c := by
  let := a.hom.toAlgebra
  change ((KaehlerDifferential.mvPolynomialBasis R S).baseChange T).repr
    ((extendTensorIso a _).hom ((ModuleCat.extendScalars a.hom).map
      (kaehlerAlgebraIso R (CommRingCat.of (MvPolynomial S R))
        (CommRingCat.ofHom MvPolynomial.C) (MvPolynomial.C_eq_algebraMap R S)).hom
      (c ⊗ₜ[_, a.hom] CommRingCat.KaehlerDifferential.d (MvPolynomial.X s)))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, kaehlerAlgebraIso_D, extendTensorIso_tmul]
  classical
  ext i
  simp only [Module.Basis.baseChange_repr_tmul,
    KaehlerDifferential.mvPolynomialBasis_repr_D_X, RingHom.smul_toAlgebra]
  by_cases hi : s = i <;> simp [hi]

private def polynomialTensorIso {R P T : CommRingCat.{u}} (base : R ⟶ P) (aug : P ⟶ T)
    (S : Type u) (e : CommRingCat.of (MvPolynomial S R) ≅ P)
    (hb : CommRingCat.ofHom MvPolynomial.C ≫ e.hom = base) :
    tensorTerm base aug ≅ ModuleCat.of T (S →₀ T) :=
  (tensorIso (CommRingCat.ofHom MvPolynomial.C) base (e.hom ≫ aug) aug e hb rfl).symm ≪≫
    polynomialBasisIso R T S (e.hom ≫ aug)

private theorem polynomialTensorIso_D {R P T : CommRingCat.{u}}
    (base : R ⟶ P) (aug : P ⟶ T) (S : Type u)
    (e : CommRingCat.of (MvPolynomial S R) ≅ P)
    (hb : CommRingCat.ofHom MvPolynomial.C ≫ e.hom = base) (s : S) (c : T) :
    (polynomialTensorIso base aug S e hb).hom
      (tensorD base aug c (e.hom (MvPolynomial.X s))) = Finsupp.single s c := by
  change (polynomialBasisIso R T S (e.hom ≫ aug)).hom
    ((tensorIso _ _ _ _ e hb rfl).inv (tensorD base aug c (e.hom (MvPolynomial.X s)))) = _
  rw [tensorIso_inv_D]
  have he : e.inv (e.hom (MvPolynomial.X s)) = MvPolynomial.X s := by
    exact ConcreteCategory.congr_hom e.hom_inv_id _
  rw [he, polynomialBasisIso_D]


private theorem polynomialTensor_ext {R P T : CommRingCat.{u}} (base : R ⟶ P)
    (aug : P ⟶ T) (S : Type u) (e : CommRingCat.of (MvPolynomial S R) ≅ P)
    (hb : CommRingCat.ofHom MvPolynomial.C ≫ e.hom = base)
    {N : ModuleCat.{u} T} {a b : tensorTerm base aug ⟶ N}
    (h : ∀ s c, a (tensorD base aug c (e.hom (MvPolynomial.X s))) =
      b (tensorD base aug c (e.hom (MvPolynomial.X s)))) : a = b := by
  let k := polynomialTensorIso base aug S e hb
  apply (cancel_epi k.inv).mp
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s c
  have hk : k.inv (Finsupp.single s c) = tensorD base aug c (e.hom (MvPolynomial.X s)) := by
    apply k.toLinearEquiv.injective
    change k.hom (k.inv (Finsupp.single s c)) =
      k.hom (tensorD base aug c (e.hom (MvPolynomial.X s)))
    rw [ModuleCat.hom_inv_apply]
    exact (polynomialTensorIso_D base aug S e hb s c).symm
  change a (k.inv (Finsupp.single s c)) = b (k.inv (Finsupp.single s c))
  rw [hk, h]


attribute [irreducible] polynomialBasisIso polynomialTensorIso

private def tensorBaseChangeIso {P Q B D T : CommRingCat.{u}}
    (h : P ⟶ Q) (k : P ⟶ B) (i : Q ⟶ D) (j : B ⟶ D)
    (sq : CategoryTheory.IsPushout h k i j) (aug : D ⟶ T) :
    tensorTerm j aug ≅ tensorTerm h (i ≫ aug) := by
  let := h.hom.toAlgebra
  let := k.hom.toAlgebra
  let := i.hom.toAlgebra
  let := j.hom.toAlgebra
  let := (h ≫ i).hom.toAlgebra
  have : IsScalarTower P Q D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P B D :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom sq.w)
  have : Algebra.IsPushout P B Q D := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  let := aug.hom.toAlgebra
  let := (i ≫ aug).hom.toAlgebra
  have : IsScalarTower Q D T := IsScalarTower.of_algebraMap_eq' rfl
  refine extendTensorIso aug _ ≪≫ ?_ ≪≫ (extendTensorIso (i ≫ aug) _).symm
  change ModuleCat.of T (T ⊗[D] KaehlerDifferential B D) ≅
    ModuleCat.of T (T ⊗[Q] KaehlerDifferential P Q)
  exact (((KaehlerDifferential.tensorKaehlerEquiv P B Q D).baseChange D T).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange Q D T T
      (KaehlerDifferential P Q)).toModuleIso

private theorem tensorBaseChangeIso_D {P Q B D T : CommRingCat.{u}}
    (h : P ⟶ Q) (k : P ⟶ B) (i : Q ⟶ D) (j : B ⟶ D)
    (sq : CategoryTheory.IsPushout h k i j) (aug : D ⟶ T) (c : T) (q : Q) :
    (tensorBaseChangeIso h k i j sq aug).hom (tensorD j aug c (i q)) =
      tensorD h (i ≫ aug) c q := by
  let := h.hom.toAlgebra
  let := k.hom.toAlgebra
  let := i.hom.toAlgebra
  let := j.hom.toAlgebra
  let := (h ≫ i).hom.toAlgebra
  have : IsScalarTower P Q D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P B D :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom sq.w)
  have : Algebra.IsPushout P B Q D := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  let := aug.hom.toAlgebra
  let := (i ≫ aug).hom.toAlgebra
  have : IsScalarTower Q D T := IsScalarTower.of_algebraMap_eq' rfl
  apply (tensorBaseChangeIso h k i j sq aug).toLinearEquiv.symm.injective
  change (tensorBaseChangeIso h k i j sq aug).inv
    ((tensorBaseChangeIso h k i j sq aug).hom _) = _
  rw [ModuleCat.inv_hom_apply]
  change tensorD j aug c (i q) =
    ((KaehlerDifferential.tensorKaehlerEquiv P B Q D).baseChange D T)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Q D T T (KaehlerDifferential P Q)).symm
        (c ⊗ₜ KaehlerDifferential.D P Q q))
  simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, tensorD,
    CommRingCat.KaehlerDifferential.d, CommRingCat.KaehlerDifferential.D,
    ModuleCat.Derivation.mk, ModuleCat.Derivation.d, RingHom.algebraMap_toAlgebra]


attribute [irreducible] tensorBaseChangeIso

private def tensorBaseChangeNormalized {P Q B D T : CommRingCat.{u}}
    (h : P ⟶ Q) (k : P ⟶ B) (i : Q ⟶ D) (j : B ⟶ D)
    (sq : CategoryTheory.IsPushout h k i j) (j' : B ⟶ D) (hj : j = j')
    (aug : D ⟶ T) (aug' : Q ⟶ T) (ha : i ≫ aug = aug') :
    tensorTerm j' aug ≅ tensorTerm h aug' :=
  eqToIso (by rw [hj]) ≪≫ tensorBaseChangeIso h k i j sq aug ≪≫ eqToIso (by rw [ha])

private theorem tensorBaseChangeNormalized_D {P Q B D T : CommRingCat.{u}}
    (h : P ⟶ Q) (k : P ⟶ B) (i : Q ⟶ D) (j : B ⟶ D)
    (sq : CategoryTheory.IsPushout h k i j) (j' : B ⟶ D) (hj : j = j')
    (aug : D ⟶ T) (aug' : Q ⟶ T) (ha : i ≫ aug = aug') (c : T) (q : Q) :
    (tensorBaseChangeNormalized h k i j sq j' hj aug aug' ha).hom
      (tensorD j' aug c (i q)) = tensorD h aug' c q := by
  subst j'
  subst aug'
  simpa only [tensorBaseChangeNormalized, eqToIso_refl, Iso.trans_hom,
    ModuleCat.comp_apply, Iso.refl_hom, ModuleCat.id_apply] using
      tensorBaseChangeIso_D h k i j sq aug c q


attribute [irreducible] tensorBaseChangeNormalized

private def tensorCancelIso {R P B T : CommRingCat.{u}}
    (base : R ⟶ P) (aug : P ⟶ B) (g : B ⟶ T) :
    (ModuleCat.extendScalars g.hom).obj (tensorTerm base aug) ≅
      tensorTerm base (aug ≫ g) :=
  (ModuleCat.extendScalarsComp aug.hom g.hom).symm.app _

private theorem tensorCancelIso_D {R P B T : CommRingCat.{u}}
    (base : R ⟶ P) (aug : P ⟶ B) (g : B ⟶ T) (c : T) (b : B) (x : P) :
    (tensorCancelIso base aug g).hom (c ⊗ₜ[B, g.hom] tensorD base aug b x) =
      tensorD base (aug ≫ g) (c * g b) x := by
  let M := CommRingCat.KaehlerDifferential base
  have h (w : M) : (tensorCancelIso base aug g).inv
      ((1 : T) ⊗ₜ[P, (aug ≫ g).hom] w) =
      (1 : T) ⊗ₜ[B, g.hom] ((1 : B) ⊗ₜ[P, aug.hom] w) :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul aug.hom g.hom M w
  apply (tensorCancelIso base aug g).toLinearEquiv.symm.injective
  change (tensorCancelIso base aug g).inv ((tensorCancelIso base aug g).hom _) = _
  rw [ModuleCat.inv_hom_apply]
  change c ⊗ₜ[B, g.hom] tensorD base aug b x =
    (tensorCancelIso base aug g).inv (tensorD base (aug ≫ g) (c * g b) x)
  have hc : tensorD base (aug ≫ g) (c * g b) x =
      (c * g b) • tensorD base (aug ≫ g) 1 x := by
    change (c * g b) ⊗ₜ[P, (aug ≫ g).hom] _ =
      (c * g b) • ((1 : T) ⊗ₜ[P, (aug ≫ g).hom] _)
    let := (aug ≫ g).hom.toAlgebra
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c ⊗ₜ[B, g.hom] tensorD base aug b x =
    (c * g b) • (tensorCancelIso base aug g).inv
      ((1 : T) ⊗ₜ[P, (aug ≫ g).hom] CommRingCat.KaehlerDifferential.d x)
  rw [h]
  let := g.hom.toAlgebra
  change c ⊗ₜ[B, g.hom] tensorD base aug b x =
    (c * g b) • ((1 : T) ⊗ₜ[B, g.hom] tensorD base aug 1 x)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change c ⊗ₜ[B] (b ⊗ₜ[P, aug.hom] CommRingCat.KaehlerDifferential.d x) =
    (c * g b) ⊗ₜ[B] ((1 : B) ⊗ₜ[P, aug.hom] CommRingCat.KaehlerDifferential.d x)
  rw [← mul_one b, ← ModuleCat.ExtendScalars.smul_tmul]
  rw [TensorProduct.tmul_smul]
  simp only [mul_one]
  change (g.hom b * c) ⊗ₜ[B] ((1 : B) ⊗ₜ[P, aug.hom]
      CommRingCat.KaehlerDifferential.d x) =
    (c * g.hom b) ⊗ₜ[B] ((1 : B) ⊗ₜ[P, aug.hom]
      CommRingCat.KaehlerDifferential.d x)
  rw [mul_comm (g.hom b) c]


attribute [irreducible] tensorCancelIso

end Algebra.CotangentSheaf

namespace Algebra.CotangentDifferentialSequence

open CotangentSites CotangentSheaf

variable {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)

/-- The base inclusion `A → P`. Source: Stacks 08QU
(blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def pBase (U : (PairSite f g)ᵒᵖ) : A ⟶ (pairP f g).obj U :=
  ((pairDiagram f g).obj U).left.left.hom

/-- The base inclusion `A → Q`. Source: Stacks 08QU
(blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def qBase (U : (PairSite f g)ᵒᵖ) : A ⟶ (pairQ f g).obj U :=
  ((pairDiagram f g).obj U).left.right.hom

/-- The actual value `C ⊗_P Ω[P/A]`, using tensor symmetry from the displayed order.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def leftTerm (U : (PairSite f g)ᵒᵖ) : ModuleCat.{u} C :=
  tensorTerm (pBase f g U) ((pairPB f g).app U ≫ g)

/-- The actual value `C ⊗_Q Ω[Q/A]`.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def middleTerm (U : (PairSite f g)ᵒᵖ) : ModuleCat.{u} C :=
  tensorTerm (qBase f g U) ((pairQC f g).app U)

/-- The actual value `C ⊗_Q Ω[Q/P]`.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def rightTerm (U : (PairSite f g)ᵒᵖ) : ModuleCat.{u} C :=
  tensorTerm ((pairPQ f g).app U) ((pairQC f g).app U)

/-- The generator `c ⊗ d_A p` of the first value.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def leftD (U : (PairSite f g)ᵒᵖ) (c : C) (p : (pairP f g).obj U) : leftTerm f g U :=
  tensorD (pBase f g U) ((pairPB f g).app U ≫ g) c p

/-- The generator `c ⊗ d_A q` of the middle value.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def middleD (U : (PairSite f g)ᵒᵖ) (c : C) (q : (pairQ f g).obj U) :
    middleTerm f g U :=
  tensorD (qBase f g U) ((pairQC f g).app U) c q

/-- The generator `c ⊗ d_P q` of the last value.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def rightD (U : (PairSite f g)ᵒᵖ) (c : C) (q : (pairQ f g).obj U) : rightTerm f g U :=
  tensorD ((pairPQ f g).app U) ((pairQC f g).app U) c q

/-- The first presheaf is the actual scalar extension of the first inverse image.
On the identity-cover topology this is the sheaf change of rings, computed objectwise.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def firstModule (s : Projections f g) (F : SiteCoefficients f) :
    (PairSite f g)ᵒᵖ ⥤ ModuleCat.{u} C :=
  (s.projection 0).op ⋙ F.functor ⋙ ModuleCat.extendScalars g.hom

/-- The second inverse image is precomposition.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def secondModule (s : Projections f g) (F : SiteCoefficients (f ≫ g)) :
    (PairSite f g)ᵒᵖ ⥤ ModuleCat.{u} C :=
  (s.projection 1).op ⋙ F.functor

/-- The third inverse image is precomposition, with the tensor-pushout projection.
Source: Stacks 08QU (blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
def thirdModule (s : Projections f g) (F : SiteCoefficients g) :
    (PairSite f g)ᵒᵖ ⥤ ModuleCat.{u} C :=
  (s.projection 2).op ⋙ F.functor


private theorem pair_base_triangle (U : (PairSite f g)ᵒᵖ) :
    pBase f g U ≫ (pairPQ f g).app U = qBase f g U :=
  Under.w ((pairDiagram f g).obj U).left.hom

private theorem pair_aug_triangle (U : (PairSite f g)ᵒᵖ) :
    (pairPQ f g).app U ≫ (pairQC f g).app U = (pairPB f g).app U ≫ g :=
  congrArg (fun k ↦ k.right) ((pairDiagram f g).obj U).hom.w.symm


private def aValue (U : (PairSite f g)ᵒᵖ) : leftTerm f g U ⟶ middleTerm f g U :=
  tensorMap _ _ _ _ (𝟙 A) ((pairPQ f g).app U)
    (by simpa using pair_base_triangle f g U) (pair_aug_triangle f g U)

private def bValue (U : (PairSite f g)ᵒᵖ) : middleTerm f g U ⟶ rightTerm f g U :=
  tensorMap _ _ _ _ (pBase f g U) (𝟙 _)
    (by simpa using (pair_base_triangle f g U).symm) (by simp)

private theorem aValue_D (U : (PairSite f g)ᵒᵖ) (c : C) (x : (pairP f g).obj U) :
    aValue f g U (leftD f g U c x) = middleD f g U c ((pairPQ f g).app U x) :=
  tensorMap_D _ _ _ _ (𝟙 A) _ (by simpa using pair_base_triangle f g U)
    (pair_aug_triangle f g U) c x

private theorem bValue_D (U : (PairSite f g)ᵒᵖ) (c : C) (x : (pairQ f g).obj U) :
    bValue f g U (middleD f g U c x) = rightD f g U c x :=
  tensorMap_D _ _ _ _ (pBase f g U) (𝟙 _)
    (by simpa using (pair_base_triangle f g U).symm) (by simp) c x

attribute [irreducible] aValue bValue

private def valueOne (s : Projections f g) (U : (PairSite f g)ᵒᵖ) :
    (firstModule f g s (siteCoefficients f)).obj U ≅ leftTerm f g U :=
  (ModuleCat.extendScalars g.hom).mapIso
    (tensorIso _ _ _ _ (s.first.app U) (s.firstBase U)
      (congr_app s.firstAugmentation U)) ≪≫
    tensorCancelIso _ _ g

private def valueTwo (s : Projections f g) (U : (PairSite f g)ᵒᵖ) :
    (secondModule f g s (siteCoefficients (f ≫ g))).obj U ≅ middleTerm f g U :=
  tensorIso _ _ _ _ (s.second.app U) (s.secondBase U)
    (congr_app s.secondAugmentation U)

private def valueThree (s : Projections f g) (U : (PairSite f g)ᵒᵖ) :
    (thirdModule f g s (siteCoefficients g)).obj U ≅ rightTerm f g U := by
  exact tensorBaseChangeNormalized _ _ _ _ (s.tensorSquare U) _
    (congr_app s.tensorBase U) _ _ (congr_app s.tensorAugmentation U)


private theorem valueOne_D (s : Projections f g) (U : (PairSite f g)ᵒᵖ)
    (c : C) (b : B) (p : (presentationRing f).obj ((s.projection 0).op.obj U)) :
    (valueOne f g s U).hom (c ⊗ₜ[B, g.hom]
      tensorD _ _ b p) = leftD f g U (c * g b) (s.first.hom.app U p) := by
  let e : tensorTerm ((presentationBase f).app ((s.projection 0).op.obj U))
      ((presentationAugmentation f).app ((s.projection 0).op.obj U)) ≅
      tensorTerm (pBase f g U) ((pairPB f g).app U) :=
    tensorIso _ _ _ _ (s.first.app U) (s.firstBase U)
      (congr_app s.firstAugmentation U)
  have he := extendScalars_map_tmul g e.hom c (tensorD _ _ b p)
  have hd := tensorIso_hom_D _ _ _ _ (s.first.app U) (s.firstBase U)
    (congr_app s.firstAugmentation U) b p
  change e.hom (tensorD _ _ b p) = tensorD _ _ b (s.first.hom.app U p) at hd
  change (tensorCancelIso _ _ g).hom
    ((ModuleCat.extendScalars g.hom).map e.hom (c ⊗ₜ[B, g.hom] tensorD _ _ b p)) = _
  rw [he]
  exact (congrArg (fun z ↦ (tensorCancelIso (pBase f g U) ((pairPB f g).app U) g).hom
    (c ⊗ₜ[B, g.hom] z)) hd).trans (tensorCancelIso_D _ _ _ c b (s.first.hom.app U p))

private theorem valueTwo_D (s : Projections f g) (U : (PairSite f g)ᵒᵖ)
    (c : C) (q : (presentationRing (f ≫ g)).obj ((s.projection 1).op.obj U)) :
    (valueTwo f g s U).hom (tensorD _ _ c q) =
      middleD f g U c (s.second.hom.app U q) :=
  tensorIso_hom_D _ _ _ _ _ _ _ _ _

private theorem valueThree_D (s : Projections f g) (U : (PairSite f g)ᵒᵖ)
    (c : C) (q : (pairQ f g).obj U) :
    (valueThree f g s U).hom (tensorD _ _ c (s.tensorQ.app U q)) =
      rightD f g U c q := by
  exact tensorBaseChangeNormalized_D _ _ _ _ (s.tensorSquare U) _
    (congr_app s.tensorBase U) _ _ (congr_app s.tensorAugmentation U) c q


attribute [irreducible] valueOne valueTwo valueThree

private theorem valueOne_inv_D (s : Projections f g) (U : (PairSite f g)ᵒᵖ)
    (c : C) (p : (pairP f g).obj U) :
    (valueOne f g s U).inv (leftD f g U c p) =
      c ⊗ₜ[B, g.hom] tensorD _ _ 1 (s.first.inv.app U p) := by
  apply (valueOne f g s U).toLinearEquiv.injective
  change (valueOne f g s U).hom ((valueOne f g s U).inv _) = _
  rw [ModuleCat.hom_inv_apply]
  change leftD f g U c p = (valueOne f g s U).hom _
  rw [valueOne_D]
  simp only [map_one, mul_one]
  congr 1
  exact (ConcreteCategory.congr_hom (s.first.app U).inv_hom_id p).symm

private theorem valueTwo_inv_D (s : Projections f g) (U : (PairSite f g)ᵒᵖ)
    (c : C) (q : (pairQ f g).obj U) :
    (valueTwo f g s U).inv (middleD f g U c q) =
      tensorD _ _ c (s.second.inv.app U q) := by
  apply (valueTwo f g s U).toLinearEquiv.injective
  change (valueTwo f g s U).hom ((valueTwo f g s U).inv _) = _
  rw [ModuleCat.hom_inv_apply]
  change middleD f g U c q = (valueTwo f g s U).hom _
  rw [valueTwo_D]
  congr 1
  exact (ConcreteCategory.congr_hom (s.second.app U).inv_hom_id q).symm

private theorem valueThree_inv_D (s : Projections f g) (U : (PairSite f g)ᵒᵖ)
    (c : C) (q : (pairQ f g).obj U) :
    (valueThree f g s U).inv (rightD f g U c q) =
      tensorD _ _ c (s.tensorQ.app U q) := by
  apply (valueThree f g s U).toLinearEquiv.injective
  change (valueThree f g s U).hom ((valueThree f g s U).inv _) = _
  rw [ModuleCat.hom_inv_apply]
  change rightD f g U c q = (valueThree f g s U).hom _
  rw [valueThree_D]

private theorem first_map_D (s : Projections f g) {U V : (PairSite f g)ᵒᵖ}
    (h : U ⟶ V) (c : C) (p : (pairP f g).obj U) :
    (valueOne f g s V).hom ((firstModule f g s (siteCoefficients f)).map h
      ((valueOne f g s U).inv (leftD f g U c p))) =
      leftD f g V c ((pairP f g).map h p) := by
  rw [valueOne_inv_D]
  change (valueOne f g s V).hom ((ModuleCat.extendScalars g.hom).map _
    (c ⊗ₜ[B, g.hom] tensorD _ _ 1 (s.first.inv.app U p))) = _
  rw [extendScalars_map_tmul]
  erw [siteCoefficients_map_D, valueOne_D]
  simp only [map_one, mul_one]
  congr 1
  have he := congrArg (fun k ↦ k (s.first.inv.app U p)) (s.first.hom.naturality h)
  change (s.first.hom.app V)
    ((presentationRing f).map ((s.projection 0).op.map h) (s.first.inv.app U p)) =
    (pairP f g).map h ((s.first.hom.app U) (s.first.inv.app U p)) at he
  erw [CommRingCat.hom_inv_apply (s.first.app U)] at he
  exact he

private theorem second_map_D (s : Projections f g) {U V : (PairSite f g)ᵒᵖ}
    (h : U ⟶ V) (c : C) (q : (pairQ f g).obj U) :
    (valueTwo f g s V).hom ((secondModule f g s (siteCoefficients (f ≫ g))).map h
      ((valueTwo f g s U).inv (middleD f g U c q))) =
      middleD f g V c ((pairQ f g).map h q) := by
  rw [valueTwo_inv_D]
  change (valueTwo f g s V).hom ((siteCoefficients (f ≫ g)).functor.map
    ((s.projection 1).op.map h) (tensorD _ _ c (s.second.inv.app U q))) = _
  rw [siteCoefficients_map_D, valueTwo_D]
  congr 1
  have he := congrArg (fun k ↦ k (s.second.inv.app U q)) (s.second.hom.naturality h)
  change (s.second.hom.app V)
    ((presentationRing (f ≫ g)).map ((s.projection 1).op.map h) (s.second.inv.app U q)) =
    (pairQ f g).map h ((s.second.hom.app U) (s.second.inv.app U q)) at he
  erw [CommRingCat.hom_inv_apply (s.second.app U)] at he
  exact he

private theorem third_map_D (s : Projections f g) {U V : (PairSite f g)ᵒᵖ}
    (h : U ⟶ V) (c : C) (q : (pairQ f g).obj U) :
    (valueThree f g s V).hom ((thirdModule f g s (siteCoefficients g)).map h
      ((valueThree f g s U).inv (rightD f g U c q))) =
      rightD f g V c ((pairQ f g).map h q) := by
  rw [valueThree_inv_D]
  change (valueThree f g s V).hom ((siteCoefficients g).functor.map
    ((s.projection 2).op.map h) (tensorD _ _ c (s.tensorQ.app U q))) = _
  rw [siteCoefficients_map_D]
  have he := congrArg (fun k ↦ k q) (s.tensorQ.naturality h)
  change (s.tensorQ.app V) ((pairQ f g).map h q) =
    (presentationRing g).map ((s.projection 2).op.map h) (s.tensorQ.app U q) at he
  rw [← he, valueThree_D]


private def aMap (s : Projections f g) :
    firstModule f g s (siteCoefficients f) ⟶
      secondModule f g s (siteCoefficients (f ≫ g)) where
  app U := (valueOne f g s U).hom ≫ aValue f g U ≫ (valueTwo f g s U).inv
  naturality := by
    intro U V h
    apply (cancel_mono (valueTwo f g s V).hom).mp
    apply (cancel_epi (valueOne f g s U).inv).mp
    apply tensor_ext
    intro c p
    simp only [ModuleCat.comp_apply, ModuleCat.hom_inv_apply]
    change (aValue f g V) ((valueOne f g s V).hom
      ((firstModule f g s (siteCoefficients f)).map h
        ((valueOne f g s U).inv (leftD f g U c p)))) = _
    erw [ModuleCat.hom_inv_apply (valueOne f g s U)]
    erw [first_map_D, aValue_D, aValue_D, second_map_D]
    congr 1
    exact congrArg (fun k ↦ k p) ((pairPQ f g).naturality h)

private def bMap (s : Projections f g) :
    secondModule f g s (siteCoefficients (f ≫ g)) ⟶
      thirdModule f g s (siteCoefficients g) where
  app U := (valueTwo f g s U).hom ≫ bValue f g U ≫ (valueThree f g s U).inv
  naturality := by
    intro U V h
    apply (cancel_mono (valueThree f g s V).hom).mp
    apply (cancel_epi (valueTwo f g s U).inv).mp
    apply tensor_ext
    intro c q
    simp only [ModuleCat.comp_apply, ModuleCat.hom_inv_apply]
    change (bValue f g V) ((valueTwo f g s V).hom
      ((secondModule f g s (siteCoefficients (f ≫ g))).map h
        ((valueTwo f g s U).inv (middleD f g U c q)))) = _
    erw [ModuleCat.hom_inv_apply (valueTwo f g s U)]
    erw [second_map_D, bValue_D, bValue_D, third_map_D]

private theorem maps_zero (s : Projections f g) : aMap f g s ≫ bMap f g s = 0 := by
  apply NatTrans.ext
  funext U
  apply (cancel_mono (valueThree f g s U).hom).mp
  apply (cancel_epi (valueOne f g s U).inv).mp
  simp only [NatTrans.comp_app, aMap, bMap, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    NatTrans.app_zero, comp_zero, zero_comp]
  apply tensor_ext
  intro c p
  change bValue f g U (aValue f g U (leftD f g U c p)) = 0
  rw [aValue_D, bValue_D]
  exact tensorD_base_any _ _ c p


attribute [irreducible] aMap bMap

private def towerCoordinates (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U) :
    CommRingCat.of (MvPolynomial (T ⊕ S) A) ≅ (pairQ f g).obj U :=
  ((MvPolynomial.sumRingEquiv A T S).trans
    (MvPolynomial.mapEquiv T eP.commRingCatIsoToRingEquiv)).toCommRingCatIso ≪≫ eQ

private theorem towerCoordinates_base (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U)
    (hP : CommRingCat.ofHom MvPolynomial.C ≫ eP.hom = pBase f g U)
    (hQ : CommRingCat.ofHom MvPolynomial.C ≫ eQ.hom = (pairPQ f g).app U) :
    CommRingCat.ofHom MvPolynomial.C ≫ (towerCoordinates f g U S T eP eQ).hom =
      qBase f g U := by
  rw [← pair_base_triangle f g U, ← hP, ← hQ]
  ext a
  simp [towerCoordinates, MvPolynomial.sumRingEquiv_C, Iso.commRingCatIsoToRingEquiv]

private theorem towerCoordinates_inl (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U)
    (t : T) :
    (towerCoordinates f g U S T eP eQ).hom (MvPolynomial.X (Sum.inl t)) =
      eQ.hom (MvPolynomial.X t) := by
  simp [towerCoordinates, MvPolynomial.sumRingEquiv_X_inl]

private theorem towerCoordinates_inr (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U)
    (hQ : CommRingCat.ofHom MvPolynomial.C ≫ eQ.hom = (pairPQ f g).app U) (s : S) :
    (towerCoordinates f g U S T eP eQ).hom (MvPolynomial.X (Sum.inr s)) =
      (pairPQ f g).app U (eP.hom (MvPolynomial.X s)) := by
  rw [← hQ]
  simp [towerCoordinates, MvPolynomial.sumRingEquiv_X_inr, Iso.commRingCatIsoToRingEquiv]

private def middleCoordinates (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U)
    (hP : CommRingCat.ofHom MvPolynomial.C ≫ eP.hom = pBase f g U)
    (hQ : CommRingCat.ofHom MvPolynomial.C ≫ eQ.hom = (pairPQ f g).app U) :
    middleTerm f g U ≅ ModuleCat.of C ((S →₀ C) × (T →₀ C)) :=
  polynomialTensorIso _ _ (T ⊕ S) (towerCoordinates f g U S T eP eQ)
      (towerCoordinates_base f g U S T eP eQ hP hQ) ≪≫
    ((Finsupp.sumFinsuppLEquivProdFinsupp C).trans
      (LinearEquiv.prodComm C (T →₀ C) (S →₀ C))).toModuleIso

private theorem middleCoordinates_x (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U)
    (hP : CommRingCat.ofHom MvPolynomial.C ≫ eP.hom = pBase f g U)
    (hQ : CommRingCat.ofHom MvPolynomial.C ≫ eQ.hom = (pairPQ f g).app U)
    (s : S) (c : C) :
    (middleCoordinates f g U S T eP eQ hP hQ).hom
      (middleD f g U c ((pairPQ f g).app U (eP.hom (MvPolynomial.X s)))) =
      (Finsupp.single s c, 0) := by
  rw [← towerCoordinates_inr f g U S T eP eQ hQ s]
  change ((Finsupp.sumFinsuppLEquivProdFinsupp C).trans
    (LinearEquiv.prodComm C (T →₀ C) (S →₀ C)))
    ((polynomialTensorIso _ _ _ _ _).hom (tensorD _ _ c _)) = _
  rw [polynomialTensorIso_D]
  ext i <;> simp [Finsupp.sumFinsuppLEquivProdFinsupp]

private theorem middleCoordinates_y (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U)
    (hP : CommRingCat.ofHom MvPolynomial.C ≫ eP.hom = pBase f g U)
    (hQ : CommRingCat.ofHom MvPolynomial.C ≫ eQ.hom = (pairPQ f g).app U)
    (t : T) (c : C) :
    (middleCoordinates f g U S T eP eQ hP hQ).hom
      (middleD f g U c (eQ.hom (MvPolynomial.X t))) = (0, Finsupp.single t c) := by
  rw [← towerCoordinates_inl f g U S T eP eQ t]
  change ((Finsupp.sumFinsuppLEquivProdFinsupp C).trans
    (LinearEquiv.prodComm C (T →₀ C) (S →₀ C)))
    ((polynomialTensorIso _ _ _ _ _).hom (tensorD _ _ c _)) = _
  rw [polynomialTensorIso_D]
  ext i <;> simp [Finsupp.sumFinsuppLEquivProdFinsupp]


attribute [irreducible] middleCoordinates

private theorem coordinate_a (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U)
    (hP : CommRingCat.ofHom MvPolynomial.C ≫ eP.hom = pBase f g U)
    (hQ : CommRingCat.ofHom MvPolynomial.C ≫ eQ.hom = (pairPQ f g).app U)
    (x : leftTerm f g U) :
    (middleCoordinates f g U S T eP eQ hP hQ).hom (aValue f g U x) =
      ((polynomialTensorIso _ _ S eP hP).hom x, 0) := by
  let l := polynomialTensorIso (pBase f g U) ((pairPB f g).app U ≫ g) S eP hP
  let m := middleCoordinates f g U S T eP eQ hP hQ
  have he : aValue f g U ≫ m.hom = l.hom ≫
      ModuleCat.ofHom (LinearMap.inl C (S →₀ C) (T →₀ C)) := by
    apply polynomialTensor_ext _ _ S eP hP
    intro s c
    change m.hom (aValue f g U (leftD f g U c (eP.hom (MvPolynomial.X s)))) = _
    rw [aValue_D, middleCoordinates_x]
    change _ = (l.hom (tensorD _ _ c (eP.hom (MvPolynomial.X s))), 0)
    rw [show l.hom (tensorD _ _ c (eP.hom (MvPolynomial.X s))) = Finsupp.single s c from
      polynomialTensorIso_D _ _ _ _ _ _ _]
  exact congrArg (fun k ↦ k x) he

private theorem coordinate_b (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U)
    (hP : CommRingCat.ofHom MvPolynomial.C ≫ eP.hom = pBase f g U)
    (hQ : CommRingCat.ofHom MvPolynomial.C ≫ eQ.hom = (pairPQ f g).app U)
    (y : middleTerm f g U) :
    (polynomialTensorIso _ _ T eQ hQ).hom (bValue f g U y) =
      ((middleCoordinates f g U S T eP eQ hP hQ).hom y).2 := by
  let m := middleCoordinates f g U S T eP eQ hP hQ
  let r : rightTerm f g U ≅ ModuleCat.of C (T →₀ C) :=
    polynomialTensorIso ((pairPQ f g).app U) ((pairQC f g).app U) T eQ hQ
  have he : bValue f g U ≫ r.hom = m.hom ≫
      ModuleCat.ofHom (LinearMap.snd C (S →₀ C) (T →₀ C)) := by
    apply polynomialTensor_ext _ _ (T ⊕ S) (towerCoordinates f g U S T eP eQ)
      (towerCoordinates_base f g U S T eP eQ hP hQ)
    intro z c
    cases z with
    | inl t =>
      rw [towerCoordinates_inl]
      change r.hom (bValue f g U (middleD f g U c (eQ.hom (MvPolynomial.X t)))) = _
      rw [bValue_D]
      rw [show r.hom (rightD f g U c (eQ.hom (MvPolynomial.X t))) =
        Finsupp.single t c from polynomialTensorIso_D _ _ _ _ _ _ _]
      change _ = (m.hom (middleD f g U c (eQ.hom (MvPolynomial.X t)))).2
      rw [middleCoordinates_y]
    | inr s =>
      rw [towerCoordinates_inr f g U S T eP eQ hQ]
      change r.hom (bValue f g U (middleD f g U c
        ((pairPQ f g).app U (eP.hom (MvPolynomial.X s))))) = _
      rw [bValue_D]
      have hz : rightD f g U c ((pairPQ f g).app U (eP.hom (MvPolynomial.X s))) = 0 :=
        tensorD_base_any _ _ c _
      rw [hz, map_zero]
      change _ = (m.hom (middleD f g U c
        ((pairPQ f g).app U (eP.hom (MvPolynomial.X s))))).2
      rw [middleCoordinates_x]
  exact congrArg (fun k ↦ k y) he

private theorem value_shortExact (U : (PairSite f g)ᵒᵖ) (hz : aValue f g U ≫ bValue f g U = 0) :
    (ShortComplex.mk (aValue f g U) (bValue f g U) hz).ShortExact := by
  have hp : IsPolynomial (pBase f g U) :=
    ((AsSmall.down.obj U.unop).unop).property.1
  have hq : IsPolynomial ((pairPQ f g).app U) :=
    ((AsSmall.down.obj U.unop).unop).property.2
  obtain ⟨S, eP, hP⟩ := hp
  obtain ⟨T, eQ, hQ⟩ := hq
  let l := polynomialTensorIso (pBase f g U) ((pairPB f g).app U ≫ g) S eP hP
  let m := middleCoordinates f g U S T eP eQ hP hQ
  let r : rightTerm f g U ≅ ModuleCat.of C (T →₀ C) :=
    polynomialTensorIso ((pairPQ f g).app U) ((pairQC f g).app U) T eQ hQ
  have ha (x : leftTerm f g U) : m.hom (aValue f g U x) = (l.hom x, 0) :=
    coordinate_a f g U S T eP eQ hP hQ x
  have hb (y : middleTerm f g U) : r.hom (bValue f g U y) = (m.hom y).2 :=
    coordinate_b f g U S T eP eQ hP hQ y
  have hi : Function.Injective (aValue f g U) := by
    intro x y he
    apply l.toLinearEquiv.injective
    have hx := congrArg (fun z ↦ (m.hom z).1) he
    change l.hom x = l.hom y
    simpa only [ha] using hx
  have hs : Function.Surjective (bValue f g U) := by
    intro z
    refine ⟨m.inv (0, r.hom z), ?_⟩
    apply r.toLinearEquiv.injective
    change r.hom (bValue f g U (m.inv (0, r.hom z))) = r.hom z
    rw [hb, ModuleCat.hom_inv_apply]
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 hi)
    ((ModuleCat.epi_iff_surjective _).2 hs)
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro y hy
  refine ⟨l.inv (m.hom y).1, ?_⟩
  apply m.toLinearEquiv.injective
  change m.hom (aValue f g U (l.inv (m.hom y).1)) = m.hom y
  rw [ha, ModuleCat.hom_inv_apply]
  have hzero : (m.hom y).2 = 0 := by rw [← hb, hy, map_zero]
  exact Prod.ext rfl hzero.symm


private theorem presheaf_shortExact (s : Projections f g) :
    (ShortComplex.mk (aMap f g s) (bMap f g s) (maps_zero f g s)).ShortExact := by
  let K := ShortComplex.mk (aMap f g s) (bMap f g s) (maps_zero f g s)
  have hv (U : (PairSite f g)ᵒᵖ) : aValue f g U ≫ bValue f g U = 0 := by
    apply tensor_ext
    intro c p
    change bValue f g U (aValue f g U (leftD f g U c p)) = 0
    rw [aValue_D, bValue_D]
    exact tensorD_base_any _ _ c p
  have hU (U : (PairSite f g)ᵒᵖ) :
      (K.map ((evaluation _ _).obj U)).ShortExact := by
    let e : K.map ((evaluation _ _).obj U) ≅
        ShortComplex.mk (aValue f g U) (bValue f g U) (hv U) :=
      ShortComplex.isoMk (valueOne f g s U) (valueTwo f g s U) (valueThree f g s U)
        (by simp [K, aMap]) (by simp [K, bMap])
    exact ShortComplex.shortExact_of_iso e.symm (value_shortExact f g U (hv U))
  have hmono (U : (PairSite f g)ᵒᵖ) : Mono (K.f.app U) := (hU U).mono_f
  have hepi (U : (PairSite f g)ᵒᵖ) : Epi (K.g.app U) := (hU U).epi_g
  have : Mono K.f := NatTrans.mono_of_mono_app _
  have : Epi K.g := NatTrans.epi_of_epi_app _
  refine ShortComplex.ShortExact.mk' ?_ ‹Mono K.f› ‹Epi K.g›
  apply K.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι' K.f K.zero
  intro W k hk
  let t (U : (PairSite f g)ᵒᵖ) := (hU U).fIsKernel
  let l : W ⟶ K.X₁ :=
    { app U := (t U).lift (KernelFork.ofι (k.app U) (by simpa using congr_app hk U))
      naturality := by
        intro U V h
        apply (cancel_mono (K.f.app V)).mp
        have hl (X : (PairSite f g)ᵒᵖ) :
            (t X).lift (KernelFork.ofι (k.app X) (by simpa using congr_app hk X)) ≫
              K.f.app X = k.app X := Fork.IsLimit.lift_ι (t X)
        rw [Category.assoc, hl]
        rw [Category.assoc, K.f.naturality h, ← Category.assoc, hl]
        exact k.naturality h }
  refine ⟨l, ?_⟩
  apply NatTrans.ext
  funext U
  exact Fork.IsLimit.lift_ι (t U)

set_option backward.isDefEq.respectTransparency true

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- All clauses of the canonical differential presheaf sequence. `a` and `b` are natural
transformations, not independently chosen objectwise maps. All identifications and arrows
are normalized on differential tensors. Coordinate isomorphisms are quantified separately
at each object; no natural coordinate splitting is asserted.
Source: Stacks 08QU, 00RV and 00RX
(blueprint: lem-trf-cotangent-differential-presheaf-ses). -/
structure Sequence where
  sites : Projections f g
  F1 : SiteCoefficients f
  F2 : SiteCoefficients (f ≫ g)
  F3 : SiteCoefficients g
  value1 : ∀ U : (PairSite f g)ᵒᵖ,
    (firstModule f g sites F1).obj U ≅ leftTerm f g U
  value2 : ∀ U : (PairSite f g)ᵒᵖ,
    (secondModule f g sites F2).obj U ≅ middleTerm f g U
  value3 : ∀ U : (PairSite f g)ᵒᵖ,
    (thirdModule f g sites F3).obj U ≅ rightTerm f g U
  first_formula : ∀ (U : (PairSite f g)ᵒᵖ) (c : C) (b : B) (p : (pairP f g).obj U),
    (value1 U).hom (c ⊗ₜ[B, g.hom]
      ((F1.terms ((sites.projection 0).op.obj U)).inv
        (tensorD ((presentationBase f).app ((sites.projection 0).op.obj U))
          ((presentationAugmentation f).app ((sites.projection 0).op.obj U)) b
          (sites.first.inv.app U p)))) = leftD f g U (c * g b) p
  second_formula : ∀ (U : (PairSite f g)ᵒᵖ) (c : C) (q : (pairQ f g).obj U),
    (value2 U).hom ((F2.terms ((sites.projection 1).op.obj U)).inv
      (tensorD ((presentationBase (f ≫ g)).app ((sites.projection 1).op.obj U))
        ((presentationAugmentation (f ≫ g)).app ((sites.projection 1).op.obj U)) c
        (sites.second.inv.app U q))) = middleD f g U c q
  third_formula : ∀ (U : (PairSite f g)ᵒᵖ) (c : C) (q : (pairQ f g).obj U),
    (value3 U).hom ((F3.terms ((sites.projection 2).op.obj U)).inv
      (tensorD ((presentationBase g).app ((sites.projection 2).op.obj U))
        ((presentationAugmentation g).app ((sites.projection 2).op.obj U)) c
        (sites.tensorQ.app U q))) = rightD f g U c q
  a : firstModule f g sites F1 ⟶ secondModule f g sites F2
  b : secondModule f g sites F2 ⟶ thirdModule f g sites F3
  a_formula : ∀ (U : (PairSite f g)ᵒᵖ) (c : C) (p : (pairP f g).obj U),
    (value2 U).hom (a.app U ((value1 U).inv (leftD f g U c p))) =
      middleD f g U c ((pairPQ f g).app U p)
  b_formula : ∀ (U : (PairSite f g)ᵒᵖ) (c : C) (q : (pairQ f g).obj U),
    (value3 U).hom (b.app U ((value2 U).inv (middleD f g U c q))) = rightD f g U c q
  zero : a ≫ b = 0
  shortExact : (ShortComplex.mk a b zero).ShortExact
  coordinate : ∀ (U : (PairSite f g)ᵒᵖ) (S T : Type u)
    (eP : CommRingCat.of (MvPolynomial S A) ≅ (pairP f g).obj U)
    (eQ : CommRingCat.of (MvPolynomial T ((pairP f g).obj U)) ≅ (pairQ f g).obj U),
    CommRingCat.ofHom MvPolynomial.C ≫ eP.hom = pBase f g U →
    CommRingCat.ofHom MvPolynomial.C ≫ eQ.hom = (pairPQ f g).app U →
    ∃ (l : (firstModule f g sites F1).obj U ≅ ModuleCat.of C (S →₀ C))
      (m : (secondModule f g sites F2).obj U ≅ ModuleCat.of C ((S →₀ C) × (T →₀ C)))
      (r : (thirdModule f g sites F3).obj U ≅ ModuleCat.of C (T →₀ C)),
      (∀ (s : S) (c : C),
        l.hom ((value1 U).inv (leftD f g U c (eP.hom (MvPolynomial.X s)))) =
          Finsupp.single s c) ∧
      (∀ (s : S) (c : C),
        m.hom ((value2 U).inv (middleD f g U c
          ((pairPQ f g).app U (eP.hom (MvPolynomial.X s))))) = (Finsupp.single s c, 0)) ∧
      (∀ (t : T) (c : C),
        m.hom ((value2 U).inv (middleD f g U c (eQ.hom (MvPolynomial.X t)))) =
          (0, Finsupp.single t c)) ∧
      (∀ (t : T) (c : C),
        r.hom ((value3 U).inv (rightD f g U c (eQ.hom (MvPolynomial.X t)))) =
          Finsupp.single t c) ∧
      (∀ x : (firstModule f g sites F1).obj U,
        m.hom (a.app U x) = (l.hom x, 0)) ∧
      (∀ y : (secondModule f g sites F2).obj U,
        r.hom (b.app U y) = (m.hom y).2)

/-- The canonical short exact sequence of constant-`C` module presheaves on polynomial pairs,
with its evaluation, base-change, restriction and coordinate formulas.
Source: Stacks 08QU (lemma-triangle-ses), Algebra 00RV and 00RX
(blueprint: lem-trf-cotangent-differential-presheaf-ses).

Proof:
1. Obtain the projection record from lem-trf-cotangent-lower-shriek, using a bar system
   from lem-trf-derived-colimit-bar. Construct the full-site coefficient functors by
   the universal property of differentials. The identity-cover tensor of
   def-pur-sheaf-tensor-product is objectwise. The first value identification sends
   `c ⊗ (b ⊗ dp)` to `c g(b) ⊗ dp`, with inverse `c ⊗ dp ↦ c ⊗ (1 ⊗ dp)`.
2. Apply lem-weil-pbc-kahler-differentials-base-change (00RV) to `P → B`, `P → Q`.
   The pushout is `D = Q ⊗_P B`. After tensoring with C, the resulting isomorphism
   sends `c ⊗ d(q ⊗ 1)` to `c ⊗ d_P q`. For a pair map `(φ,ψ)`, both routes on
   these generators give `c ⊗ d_{P'} ψ(q)`; generators prove naturality.
3. The universal property in def-weil-pbc-kahler-differentials gives `a` and `b`
   from `p ↦ d_A p` and `q ↦ d_P q`. The latter kills P, so their composite is zero.
   Restriction squares commute on generators since ψ restricts to φ, and then on all
   tensors. Thus these are natural transformations, independent of coordinates.
4. Choose any coordinates `P=A[S]`, `Q=P[T]`. Apply
   lem-weil-pbc-polynomial-ring-kahler-basis-any-variables (00RX), followed by scalar
   extension to C. The bases are respectively dx, (dx,dy), dy. The maps on them
   are inclusion and projection, proving the six coordinate formulas and objectwise
   injectivity, exactness and surjectivity. Finsupp permits infinite variable sets.
5. Objectwise monomorphisms and epimorphisms give presheaf monomorphisms and
   epimorphisms. The objectwise kernel lifts are natural by uniqueness after composing
   with the monomorphism. Thus the presheaf short complex is short exact. Identity-cover
   sheaves are presheaves. No flatness of C over Q or natural splitting is used. -/
theorem sequence_nonempty {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Nonempty (Sequence f g) := by
  obtain ⟨bar⟩ := categoryColimitBarSystem_exists.{u + 1}
  obtain ⟨data⟩ := lowerShriekData_nonempty f g bar
  let s := data.sites
  refine ⟨{
    sites := s
    F1 := siteCoefficients f
    F2 := siteCoefficients (f ≫ g)
    F3 := siteCoefficients g
    value1 := valueOne f g s
    value2 := valueTwo f g s
    value3 := valueThree f g s
    first_formula := ?_
    second_formula := ?_
    third_formula := ?_
    a := aMap f g s
    b := bMap f g s
    a_formula := ?_
    b_formula := ?_
    zero := maps_zero f g s
    shortExact := presheaf_shortExact f g s
    coordinate := ?_ }⟩
  · intro U c b p
    change (valueOne f g s U).hom
      (c ⊗ₜ[B, g.hom] tensorD _ _ b (s.first.inv.app U p)) = _
    rw [valueOne_D]
    erw [CommRingCat.hom_inv_apply (s.first.app U)]
  · intro U c q
    change (valueTwo f g s U).hom (tensorD _ _ c (s.second.inv.app U q)) = _
    rw [valueTwo_D]
    erw [CommRingCat.hom_inv_apply (s.second.app U)]
  · intro U c q
    change (valueThree f g s U).hom (tensorD _ _ c (s.tensorQ.app U q)) = _
    exact valueThree_D f g s U c q
  · intro U c p
    simp only [aMap]
    change (valueTwo f g s U).hom
      ((valueTwo f g s U).inv (aValue f g U
        ((valueOne f g s U).hom ((valueOne f g s U).inv (leftD f g U c p))))) = _
    rw [ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply, aValue_D]
  · intro U c q
    simp only [bMap]
    change (valueThree f g s U).hom
      ((valueThree f g s U).inv (bValue f g U
        ((valueTwo f g s U).hom ((valueTwo f g s U).inv (middleD f g U c q))))) = _
    rw [ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply, bValue_D]
  · intro U S T eP eQ hP hQ
    refine ⟨valueOne f g s U ≪≫ polynomialTensorIso _ _ S eP hP,
      valueTwo f g s U ≪≫ middleCoordinates f g U S T eP eQ hP hQ,
      valueThree f g s U ≪≫ polynomialTensorIso _ _ T eQ hQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i c
      change (polynomialTensorIso _ _ S eP hP).hom
        ((valueOne f g s U).hom ((valueOne f g s U).inv
          (leftD f g U c (eP.hom (MvPolynomial.X i))))) = _
      rw [ModuleCat.hom_inv_apply]
      exact polynomialTensorIso_D _ _ _ _ _ _ _
    · intro i c
      change (middleCoordinates f g U S T eP eQ hP hQ).hom
        ((valueTwo f g s U).hom ((valueTwo f g s U).inv
          (middleD f g U c ((pairPQ f g).app U (eP.hom (MvPolynomial.X i)))))) = _
      rw [ModuleCat.hom_inv_apply]
      exact middleCoordinates_x f g U S T eP eQ hP hQ i c
    · intro i c
      change (middleCoordinates f g U S T eP eQ hP hQ).hom
        ((valueTwo f g s U).hom ((valueTwo f g s U).inv
          (middleD f g U c (eQ.hom (MvPolynomial.X i))))) = _
      rw [ModuleCat.hom_inv_apply]
      exact middleCoordinates_y f g U S T eP eQ hP hQ i c
    · intro i c
      change (polynomialTensorIso _ _ T eQ hQ).hom
        ((valueThree f g s U).hom ((valueThree f g s U).inv
          (rightD f g U c (eQ.hom (MvPolynomial.X i))))) = _
      rw [ModuleCat.hom_inv_apply]
      exact polynomialTensorIso_D _ _ _ _ _ _ _
    · intro x
      simp only [aMap]
      change (middleCoordinates f g U S T eP eQ hP hQ).hom
        ((valueTwo f g s U).hom ((valueTwo f g s U).inv
          (aValue f g U ((valueOne f g s U).hom x)))) =
        ((polynomialTensorIso _ _ S eP hP).hom ((valueOne f g s U).hom x), 0)
      rw [ModuleCat.hom_inv_apply]
      exact coordinate_a f g U S T eP eQ hP hQ _
    · intro y
      simp only [bMap]
      change (polynomialTensorIso _ _ T eQ hQ).hom
        ((valueThree f g s U).hom ((valueThree f g s U).inv
          (bValue f g U ((valueTwo f g s U).hom y)))) =
        ((middleCoordinates f g U S T eP eQ hP hQ).hom ((valueTwo f g s U).hom y)).2
      rw [ModuleCat.hom_inv_apply]
      exact coordinate_b f g U S T eP eQ hP hQ _

end Algebra.CotangentDifferentialSequence
