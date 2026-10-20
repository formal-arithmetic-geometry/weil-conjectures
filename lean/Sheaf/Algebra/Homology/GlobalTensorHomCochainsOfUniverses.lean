/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X9
-/
module

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Sheaf.SecSmoothPurity.CochainInverseComparison
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-! # Global tensor–Hom cochains with independent coefficient universes

Source: Stacks Project, Cohomology on Sites, Lemma 0A90 (lemma-compose).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe c v r

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients

namespace CategoryTheory.TensorHomIndependent

/-- A shared constructor keeps the prescribed right adjoints explicit. -/
@[no_expose, instance_reducible]
private noncomputable def closedOf
    {D : Type*} [Category* D] [MonoidalCategory D]
    (rightAdj : D → (D ⥤ D)) (adj : ∀ A : D, tensorLeft A ⊣ rightAdj A) :
    MonoidalClosed D where
  closed A := { rightAdj := rightAdj A, adj := adj A }

end CategoryTheory.TensorHomIndependent

namespace PresheafOfModules.TensorHomIndependent

variable {C : Type c} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max c v r}}

/-- The tensor-hom adjunction for presheaves of modules is natural in the target. -/
private lemma homObjEquiv_comp_homObjMap {M P N N' : PresheafOfModules.{max c v r} (R ⋙ forget₂ _
    _)}
    (φ : M ⊗ P ⟶ N) (g : N ⟶ N') :
    CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r} M P N' (φ ≫ g) =
        CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r} M P N φ ≫ homObjMap (𝟙 M) g := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N')
    fun W ↦ ?_
  rfl

/-- The tensor-hom adjunction for presheaves of modules is natural in the first variable. -/
private lemma homObjEquiv_whiskerRight_comp {M M' P N : PresheafOfModules.{max c v r} (R ⋙ forget₂
    _ _)}
    (f : M' ⟶ M) (φ : M ⊗ P ⟶ N) :
    CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r} M' P N (f ▷ P ≫ φ) =
        CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r} M P N φ ≫ homObjMap f (𝟙 N) := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M') (M₂ := (restrictOver R X.unop).obj N)
    fun W ↦ ?_
  rfl

private lemma homObjEquiv_whiskerLeft_comp {M P P' N : PresheafOfModules.{max c v r} (R ⋙ forget₂
    _ _)}
    (f : P ⟶ P') (φ : M ⊗ P' ⟶ N) :
    CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r} M P N (M ◁ f ≫ φ) = f ≫
        CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r} M P' N φ := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N)
    fun W ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  exact congrArg (fun q : P'.obj (op W.unop.left) ↦
    φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] q)) (naturality_apply f W.unop.hom.op p)

end PresheafOfModules.TensorHomIndependent

attribute [local irreducible] CategoryTheory.IsoTensorHom.homObjEquiv

attribute [local irreducible] SheafOfModules.monoidalCategory

namespace SheafOfModules.TensorHomIndependent

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

-- The sheafification functor from presheaves of modules over `R` to sheaves of modules over `R`.
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{max c v r} (𝟙 (𝓡).obj)

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})] {R : Sheaf J
      CommRingCat.{max c v r}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasWeakSheafify J AddCommGrpCat.{max c v r}]

@[no_expose]
private abbrev Mods (R : Sheaf J CommRingCat.{max c v r}) :=
  SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

attribute [local instance] monoidalCategory symmetricCategory

/-- **The tensor-hom adjunction for sheaves of modules**: morphisms `A ⊗ T ⟶ N` correspond to
morphisms `T ⟶ homObj (R := R) A N`. A morphism `A ⊗ T ⟶ N` is a morphism `a(A ⊗ T) ⟶ N` out of the
sheafification of the presheaf tensor product, i.e. a morphism of presheaves `A ⊗ T ⟶ N`, which
`CategoryTheory.IsoTensorHom.homObjEquiv` turns into a morphism `T ⟶ homObj (R := R) A N`. -/
@[no_expose]
private noncomputable def tensorHomEquiv (A T N : Mods.{c, v, r} R) :
    (A ⊗ T ⟶ N) ≃ (T ⟶ homObj (R := R) A N) where
  toFun φ := ⟨CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r} (R := R.obj) A.val T.val N.val
    ((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 (𝓡).obj)).homEquiv _ N
      ((tensorObjIsoSheafification (R := R) A T).inv ≫ φ))⟩
  invFun ψ := (tensorObjIsoSheafification (R := R) A T).hom ≫
    ((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 (𝓡).obj)).homEquiv _ N).symm
      ((CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r}
        (R := R.obj) A.val T.val N.val).symm ψ.val)
  left_inv φ := by simp
  right_inv ψ := by
    ext1
    dsimp only
    rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private lemma tensorHomEquiv_val (A T N : Mods.{c, v, r} R) (φ : A ⊗ T ⟶ N) :
    (tensorHomEquiv.{c, v, r} (R := R) A T N φ).val =
      CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, r} (R := R.obj) A.val T.val N.val
      ((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 (𝓡).obj)).homEquiv _ N
        ((tensorObjIsoSheafification (R := R) A T).inv ≫ φ)) := rfl

attribute [local irreducible] tensorHomEquiv
-- Naturality uses the adjunction API, without reducing the sheafification construction.
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafification

/-- The tensor-hom adjunction for sheaves of modules is natural in `T`. -/
private lemma tensorHomEquiv_whiskerLeft_comp (A : Mods.{c, v, r} R) {T T' N :
    Mods.{c, v, r} R}
    (f : T ⟶ T') (φ : A ⊗ T' ⟶ N) :
    tensorHomEquiv.{c, v, r} (R := R) A T N (A ◁ f ≫ φ) = f ≫ tensorHomEquiv.{c, v, r} (R := R) A
        T' N φ := by
  have h : (tensorObjIsoSheafification (R := R) A T).inv ≫ A ◁ f =
      (𝓢).map (A.val ◁ f.val) ≫ (tensorObjIsoSheafification (R := R) A T').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom_kfi (R := R),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext1
  rw [comp_val, tensorHomEquiv_val.{c, v, r} (R := R), tensorHomEquiv_val.{c, v, r} (R := R), ←
      Category.assoc, h, Category.assoc,
    Adjunction.homEquiv_naturality_left]
  exact PresheafOfModules.TensorHomIndependent.homObjEquiv_whiskerLeft_comp.{c, v, r}
    (R := R.obj) _ _

/-- The tensor-hom adjunction for sheaves of modules is natural in `N`. -/
private lemma tensorHomEquiv_comp_homObjMap (A : Mods.{c, v, r} R) {T N N' :
    Mods.{c, v, r} R}
    (φ : A ⊗ T ⟶ N) (g : N ⟶ N') :
    tensorHomEquiv.{c, v, r} (R := R) A T N' (φ ≫ g) = tensorHomEquiv.{c, v, r} (R := R) A T N φ ≫
        homObjMap (R := R) (𝟙 A) g := by
  ext1
  rw [comp_val, homObjMap_val, id_val,
    tensorHomEquiv_val.{c, v, r} (R := R), tensorHomEquiv_val.{c, v, r} (R := R),
    ← Category.assoc, Adjunction.homEquiv_naturality_right]
  exact PresheafOfModules.TensorHomIndependent.homObjEquiv_comp_homObjMap.{c, v, r} (R := R.obj) _ _

/-- The tensor-hom adjunction for sheaves of modules is natural in `A`. -/
private lemma tensorHomEquiv_whiskerRight_comp {A A' : Mods.{c, v, r} R} (f : A' ⟶ A)
    {T N : Mods.{c, v, r} R} (φ : A ⊗ T ⟶ N) :
    tensorHomEquiv.{c, v, r} (R := R) A' T N (f ▷ T ≫ φ) = tensorHomEquiv.{c, v, r} (R := R) A T N
        φ ≫ homObjMap (R := R) f (𝟙 N) := by
  have h : (tensorObjIsoSheafification (R := R) A' T).inv ≫ f ▷ T =
      (𝓢).map (f.val ▷ T.val) ≫ (tensorObjIsoSheafification (R := R) A T).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← SheafOfModules.CochainScalarConstruction.whiskerRight_tensorObjIsoSheafification_hom
        (R := R),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext1
  rw [comp_val, homObjMap_val, id_val, tensorHomEquiv_val.{c, v, r} (R := R),
    tensorHomEquiv_val.{c, v, r} (R := R), ← Category.assoc, h, Category.assoc,
    Adjunction.homEquiv_naturality_left]
  exact PresheafOfModules.TensorHomIndependent.homObjEquiv_whiskerRight_comp.{c, v, r}
    (R := R.obj) _ _

variable (R) in
/-- **The tensor-hom adjunction for sheaves of modules**: tensoring with `A` is left adjoint to
the internal hom `homObj A`. -/
@[no_expose]
private noncomputable def tensorHomAdjunction (A : Mods.{c, v, r} R) :
    tensorLeft A ⊣ (homFunctor R).obj (Opposite.op A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv.{c, v, r} (R := R) A
      homEquiv_naturality_left_symm f g := by
        rw [Equiv.symm_apply_eq]
        exact ((congrArg (f ≫ ·) (Equiv.apply_symm_apply (tensorHomEquiv.{c, v, r} (R := R) A _ _)
            g).symm).trans
          (tensorHomEquiv_whiskerLeft_comp.{c, v, r} (R := R) A f _).symm)
      homEquiv_naturality_right f g := tensorHomEquiv_comp_homObjMap.{c, v, r} (R := R) A f g }

/-- **Sheaves of modules form a monoidal closed category**, with internal hom `homObj`:
tensoring with `A` is left adjoint to `homObj A` (`SheafOfModules.tensorHomAdjunction.{c, v, r}`).
-/
@[no_expose]
private noncomputable abbrev monoidalClosed : MonoidalClosed (Mods.{c, v, r} R) :=
  CategoryTheory.TensorHomIndependent.closedOf
    (fun A ↦ (homFunctor R).obj (op A)) (tensorHomAdjunction.{c, v, r} R)

private lemma uncurry_eq_tensorHomEquiv_symm {A T N : Mods.{c, v, r} R}
    (g : T ⟶ homObj (R := R) A N) :
    letI := monoidalClosed.{c, v, r} (R := R)
    MonoidalClosed.uncurry g = (tensorHomEquiv.{c, v, r} (R := R) A T N).symm g := by
  let := monoidalClosed.{c, v, r} (R := R)
  change ((tensorHomAdjunction.{c, v, r} R A).homEquiv _ _).symm g = _
  simp only [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private lemma ihom_ev_app (A N : Mods.{c, v, r} R) :
    letI := monoidalClosed.{c, v, r} (R := R)
    (ihom.ev A).app N = (tensorHomEquiv.{c, v, r} (R := R) A ((ihom A).obj N) N).symm
      (𝟙 _) := by
  let := monoidalClosed.{c, v, r} (R := R)
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_eq_tensorHomEquiv_symm.{c, v, r} (R := R)]

private lemma ihom_map {A N N' : Mods.{c, v, r} R} (f : N ⟶ N') :
    letI := monoidalClosed.{c, v, r} (R := R)
    (ihom A).map f = homObjMap (R := R) (𝟙 A) f := by
  rfl

/-- The contravariant internal Hom map is the usual sheaf Hom map. -/
private lemma pre_app {A A' : Mods.{c, v, r} R} (f : A' ⟶ A) (N : Mods.{c, v, r} R) :
    letI := monoidalClosed.{c, v, r} (R := R)
    (MonoidalClosed.pre f).app N = homObjMap (R := R) f (𝟙 N) := by
  let := monoidalClosed.{c, v, r} (R := R)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre, uncurry_eq_tensorHomEquiv_symm.{c, v, r} (R := R),
    Equiv.eq_symm_apply, tensorHomEquiv_whiskerRight_comp.{c, v, r} (R := R),
    ihom_ev_app.{c, v, r} (R := R), Equiv.apply_symm_apply, Category.id_comp]

end SheafOfModules.TensorHomIndependent

set_option backward.isDefEq.respectTransparency true
open CategoryTheory.Limits CochainComplex MonoidalClosed

namespace CategoryTheory.SignedTensorHom

variable {D : Type*} [Category* D] [Preadditive D] [MonoidalCategory D]
  [MonoidalClosed D] [MonoidalPreadditive D] [HasCountableProducts D]
  (H L M : CochainComplex D ℤ)
  (π : ∀ (n p q : ℤ) (_ : p + n = q), H.X n ⟶ (ihom (L.X p)).obj (M.X q))
  (hlim : ∀ n, IsLimit (Fan.mk (H.X n) (fun p : ℤ ↦ π n p (p + n) rfl)))

@[no_expose]
private noncomputable def toX (n : ℤ) : H.X n ⟶ (internalHomObj L M).X n :=
  Pi.lift fun T : HomComplex.Triplet n ↦ (T.p * n).negOnePow • π n T.p T.q T.hpq

@[no_expose]
private noncomputable def fromX (n : ℤ) : (internalHomObj L M).X n ⟶ H.X n :=
  (hlim n).lift
    (Fan.mk _ fun p : ℤ ↦ (p * n).negOnePow • internalHomπ L M n p (p + n) rfl)

@[reassoc]
private lemma toX_π (n p q : ℤ) (h : p + n = q) :
    toX H L M π n ≫ internalHomπ L M n p q h = (p * n).negOnePow • π n p q h :=
  Pi.lift_π _ _

@[reassoc]
private lemma fromX_π (n p q : ℤ) (h : p + n = q) :
    fromX H L M π hlim n ≫ π n p q h =
      (p * n).negOnePow • internalHomπ L M n p q h := by
  subst h
  exact (hlim n).fac _ ⟨p⟩

-- Use the projection equations when comparing maps between the product objects.
attribute [local irreducible] toX fromX

@[no_expose]
private noncomputable def degreeIso (n : ℤ) : H.X n ≅ (internalHomObj L M).X n where
  hom := toX H L M π n
  inv := fromX H L M π hlim n
  hom_inv_id := (hlim n).hom_ext fun ⟨p⟩ ↦ by
    change (_ ≫ _) ≫ π n p (p + n) rfl = 𝟙 _ ≫ π n p (p + n) rfl
    rw [Category.assoc, fromX_π, Linear.comp_units_smul, toX_π,
      smul_smul, Int.units_mul_self, one_smul, Category.id_comp]
  inv_hom_id := internalHomObj_hom_ext fun p q h ↦ by
    rw [Category.assoc, toX_π, Linear.comp_units_smul, fromX_π,
      smul_smul, Int.units_mul_self, one_smul, Category.id_comp]

variable (hd : ∀ (n p q : ℤ) (h : p + (n + 1) = q) (h₁ : p + 1 + n = q),
  H.d n (n + 1) ≫ π (n + 1) p q h =
    π n p (p + n) rfl ≫ (ihom (L.X p)).map (M.d (p + n) q) -
      n.negOnePow • (π n (p + 1) q h₁ ≫ (pre (L.d p (p + 1))).app (M.X q)))

omit [MonoidalPreadditive D] [HasCountableProducts D] in
include hd in
private lemma d_smul (n p q : ℤ) (h : p + (n + 1) = q) (h₁ : p + 1 + n = q) :
    H.d n (n + 1) ≫ ((p * (n + 1)).negOnePow • π (n + 1) p q h) =
      ((p * (n + 1)).negOnePow : ℤ) •
        (π n p (p + n) rfl ≫ (ihom (L.X p)).map (M.d (p + n) q) -
          (n.negOnePow : ℤ) •
            (π n (p + 1) q h₁ ≫ (pre (L.d p (p + 1))).app (M.X q))) := by
  rw [Units.smul_def, Preadditive.comp_zsmul, hd n p q h h₁, Units.smul_def]

include hd in
private lemma comm (n m : ℤ) (hnm : n + 1 = m) :
    toX H L M π n ≫ (internalHomObj L M).d n m = H.d n m ≫ toX H L M π m := by
  subst hnm
  refine internalHomObj_hom_ext fun p q h ↦ ?_
  have h₁ : p + 1 + n = q := by omega
  rw [Category.assoc, Category.assoc,
    internalHomObj_d_π L M n (n + 1) p q h (p + n) (p + 1) rfl h₁,
    toX_π, d_smul H L M π hd n p q h h₁]
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.comp_sub,
    toX_π_assoc, Preadditive.zsmul_comp]
  rw [show p * (n + 1) = p * n + p by ring, show (p + 1) * n = p * n + n by ring,
    Int.negOnePow_add, Int.negOnePow_add]
  simp only [Units.val_mul, smul_sub, smul_smul, mul_comm, mul_left_comm]

/-- Product components with the ordinary Hom differential give the internal Hom complex
by multiplying the component `(p,p+n)` by `(-1)^(pn)`. -/
@[no_expose]
private noncomputable def comparisonIso : H ≅ internalHomObj L M :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso H L M π hlim)
    (fun n m hnm ↦ comm H L M π hd n m hnm)

end CategoryTheory.SignedTensorHom

namespace CategoryTheory.TensorHomIndependent

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  {R : Sheaf J CommRingCat.{max c v r}}

set_option hygiene false in
local notation "𝒜" => SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

variable [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜]

@[no_expose]
private noncomputable abbrev closedFromAdjunction
    (adj : ∀ A : 𝒜, tensorLeft A ⊣ (SheafOfModules.homFunctor R).obj (op A)) :
    MonoidalClosed 𝒜 :=
  closedOf (fun A ↦ (SheafOfModules.homFunctor R).obj (op A)) adj

variable (adj : ∀ A : 𝒜, tensorLeft A ⊣ (SheafOfModules.homFunctor R).obj (op A))

omit [MonoidalPreadditive 𝒜] in
private lemma ihom_map {A N N' : 𝒜} (f : N ⟶ N') :
    letI := closedFromAdjunction.{c, v, r} (R := R) adj
    (ihom A).map f = SheafOfModules.homObjMap (R := R) (𝟙 A) f := by
  rfl

variable (hpre : ∀ {A A' : 𝒜} (f : A' ⟶ A) (N : 𝒜),
  -- Inline the closed structure to match the component formulas without expanding the adjunction.
  letI := closedFromAdjunction.{c, v, r} (R := R) adj
  (pre f).app N = SheafOfModules.homObjMap (R := R) f (𝟙 N))

variable (L M : CochainComplex 𝒜 ℤ)

/-- The sheaf Hom projection with the categorical internal Hom as its codomain. -/
@[no_expose]
private noncomputable def homComplexIhomπ (n p q : ℤ) (h : p + n = q) :
    letI := closedFromAdjunction.{c, v, r} (R := R) adj
    (homComplex.{c, v, max c v r, max c v r} (R := R) L M).X n ⟶
      (ihom (L.X p)).obj (M.X q) :=
  homComplexπ.{c, v, max c v r, max c v r} (R := R) L M n p q h

set_option linter.style.haveILetI false in
omit [MonoidalPreadditive 𝒜] in
include hpre in
private lemma homComplex_d_ihomπ (n m p q q' p' : ℤ) (hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q) :
    letI := closedFromAdjunction.{c, v, r} (R := R) adj
    (homComplex.{c, v, max c v r, max c v r} (R := R) L M).d n m ≫
        homComplexIhomπ.{c, v, r} (R := R) (adj := adj) L M m p q hpq =
      homComplexIhomπ.{c, v, r} (R := R) (adj := adj) L M n p q' hq' ≫
        (ihom (L.X p)).map (M.d q' q) -
        n.negOnePow • (homComplexIhomπ.{c, v, r} (R := R) (adj := adj) L M n p' q hp' ≫
          (pre (L.d p p')).app (M.X q)) := by
  -- Inline the closed structure to match the component formulas without expanding the adjunction.
  letI := closedFromAdjunction.{c, v, r} (R := R) adj
  change _ = _
  have hpre' : (pre (L.d p p')).app (M.X q) =
      SheafOfModules.homObjMap (R := R) (L.d p p') (𝟙 (M.X q)) :=
    hpre (L.d p p') (M.X q)
  simp only [homComplexIhomπ, ihom_map.{c, v, r} (R := R) (adj := adj), hpre']
  exact homComplex_d_π.{c, v, max c v r, max c v r} (R := R) L M
      n m p q q' p' hnm hpq hq' hp'

/-- The sheaf Hom product cone with categorical internal Hom factors. -/
@[no_expose]
private noncomputable def homComplexIhomIsLimit (n : ℤ) :
    letI := closedFromAdjunction.{c, v, r} (R := R) adj
    IsLimit (Fan.mk ((homComplex.{c, v, max c v r, max c v r} (R := R) L M).X n)
      (fun p : ℤ ↦ homComplexIhomπ.{c, v, r} (R := R) (adj := adj) L M n p (p + n) rfl)) := by
  -- Inline the closed structure to match the component formulas without expanding the adjunction.
  letI := closedFromAdjunction.{c, v, r} (R := R) adj
  change IsLimit _
  exact homComplexIsLimit.{c, v, max c v r, max c v r} (R := R) L M n

-- Keep the tensor adjunction behind the component API during the comparison.
attribute [local irreducible] homComplexIhomπ

set_option linter.style.haveILetI false in
include hpre in
/-- Identify the actual sheaf Hom complex using its product-component API. -/
private theorem homComplexIsoInternalHomObj :
    letI := closedFromAdjunction.{c, v, r} (R := R) adj
    Nonempty (homComplex.{c, v, max c v r, max c v r} (R := R) L M ≅ internalHomObj L M) := by
  -- Inline the closed structure to match the component formulas without expanding the adjunction.
  letI := closedFromAdjunction.{c, v, r} (R := R) adj
  change Nonempty (_ ≅ _)
  refine ⟨SignedTensorHom.comparisonIso
    (homComplex.{c, v, max c v r, max c v r} (R := R) L M) L M
    (homComplexIhomπ.{c, v, r} (R := R) (adj := adj) L M) ?_ ?_⟩
  · intro n
    exact homComplexIhomIsLimit.{c, v, r} (R := R) (adj := adj) L M n
  · intro n p q h h₁
    exact homComplex_d_ihomπ.{c, v, r} (R := R) (adj := adj) (hpre := hpre)
      L M n (n + 1) p q (p + n) (p + 1) rfl h rfl h₁

end CategoryTheory.TensorHomIndependent

namespace CategoryTheory.TensorHomIndependent

@[no_expose]
private noncomputable def cochainsPostIso
    {D : Type*} [Category* D] [Preadditive D]
    (K : CochainComplex D ℤ) {L M : CochainComplex D ℤ} (e : L ≅ M) (n : ℤ) :
    HomComplex.Cochain K L n ≃+ HomComplex.Cochain K M n where
  toFun a := a.comp (HomComplex.Cochain.ofHom e.hom) (add_zero n)
  invFun a := a.comp (HomComplex.Cochain.ofHom e.inv) (add_zero n)
  left_inv a := by
    ext p q hpq
    simp [HomComplex.Cochain.comp_zero_cochain_v]
  right_inv a := by
    ext p q hpq
    simp [HomComplex.Cochain.comp_zero_cochain_v]
  map_add' a b := by ext; simp [HomComplex.Cochain.comp_zero_cochain_v]

@[no_expose]
private noncomputable def cochainsPreIso
    {D : Type*} [Category* D] [Preadditive D]
    {K L : CochainComplex D ℤ} (e : K ≅ L) (M : CochainComplex D ℤ) (n : ℤ) :
    HomComplex.Cochain L M n ≃+ HomComplex.Cochain K M n where
  toFun a := (HomComplex.Cochain.ofHom e.hom).comp a (zero_add n)
  invFun a := (HomComplex.Cochain.ofHom e.inv).comp a (zero_add n)
  left_inv a := by
    ext p q hpq
    simp [HomComplex.Cochain.zero_cochain_comp_v, ← Category.assoc]
  right_inv a := by
    ext p q hpq
    simp [HomComplex.Cochain.zero_cochain_comp_v, ← Category.assoc]
  map_add' a b := by ext; simp [HomComplex.Cochain.zero_cochain_comp_v]

/-- A chain comparison with the categorical internal Hom induces the ordinary
cochain tensor–Hom equivalence and its differential compatibility. -/
private theorem cochainsTensorHomOfIso
    {D : Type*} [Category* D] [Abelian D] [HasColimitsOfSize.{0, 0} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [BraidedCategory D] [HasCountableProducts D]
    (K L I H : CochainComplex D ℤ) (d : H ≅ internalHomObj L I) :
    ∃ e : ∀ n : ℤ, HomComplex.Cochain K H n ≃+ HomComplex.Cochain (K ⊗ L) I n,
      ∀ (n m : ℤ) (a), e m (HomComplex.δ n m a) = HomComplex.δ n m (e n a) := by
  let e (n : ℤ) := (cochainsPostIso K d n).trans
    ((InternalHom.cochainEquiv L I K n).symm.trans
      (cochainsPreIso (β_ K L) I n))
  refine ⟨e, ?_⟩
  intro n m a
  dsimp only [e, AddEquiv.trans_apply, cochainsPreIso, cochainsPostIso,
    InternalHom.cochainEquiv_symm_apply]
  change (HomComplex.Cochain.ofHom (β_ K L).hom).comp
      (InternalHom.uncurryCochain
        ((HomComplex.δ n m a).comp (HomComplex.Cochain.ofHom d.hom) (add_zero m)))
      (zero_add m) =
    HomComplex.δ n m ((HomComplex.Cochain.ofHom (β_ K L).hom).comp
      (InternalHom.uncurryCochain
        (a.comp (HomComplex.Cochain.ofHom d.hom) (add_zero n))) (zero_add n))
  rw [← HomComplex.δ_comp_ofHom, InternalHom.uncurryCochain_δ,
    HomComplex.δ_ofHom_comp]

end CategoryTheory.TensorHomIndependent

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- Currying identifies all global cochains into a sheaf Hom complex with cochains
out of the total tensor complex, and respects their differentials.
Source: Stacks Project, Cohomology on Sites, Lemma 0A90 (lemma-compose).
(blueprint: lem-sfb-global-tensor-hom-cochains-universes).

Proof: project a degree-n cochain to its degree-p outer and degree-q inner
components. The sheaf tensor–Hom adjunction transposes this component to a map
K^p tensor L^q to I^(p+q+n). The coproduct universal property of the total tensor
assembles these maps, and restriction to its summands followed by currying is
inverse. All operations are additive. On a (p,q) summand the Hom differential
is d_I f minus (-1)^n f d_K minus (-1)^(n+p) f d_L. This is exactly the Hom
differential for the total tensor, whose differential is d_K tensor 1 plus
(-1)^p times 1 tensor d_L. This verifies the displayed compatibility, including
for negative degrees. Empty products and zero complexes obey the same universal
properties. The argument uses no equality between site and coefficient universes. -/
theorem global_tensorHom_cochainsOfUniverses
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (K L I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    let T := CochainComplex.mapBifunctor K L (curriedTensor _)
    ∃ e : ∀ n : ℤ, CochainComplex.HomComplex.Cochain K (homComplex (R := R) L I) n ≃+
        CochainComplex.HomComplex.Cochain T I n,
      ∀ (n m : ℤ) (_hnm : n + 1 = m) (a),
        e m (CochainComplex.HomComplex.δ n m a) =
          CochainComplex.HomComplex.δ n m (e n a) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  -- These literal instances keep the canonical tensor-Hom naturality family directly applicable.
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  letI := TensorHomIndependent.closedFromAdjunction.{c, v, r} (R := R)
    (SheafOfModules.TensorHomIndependent.tensorHomAdjunction.{c, v, r} R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  let A := SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let : HasColimitsOfSize.{0, 0} A :=
    hasColimitsOfSizeShrink.{0, 0, max c v r, max c v r} A
  obtain ⟨d⟩ := TensorHomIndependent.homComplexIsoInternalHomObj.{c, v, r} (R := R)
    (adj := SheafOfModules.TensorHomIndependent.tensorHomAdjunction.{c, v, r} R)
    (hpre := @SheafOfModules.TensorHomIndependent.pre_app.{c, v, r} C _ J _ R _ _) L I
  obtain ⟨e, he⟩ := TensorHomIndependent.cochainsTensorHomOfIso
    K L I (homComplex (R := R) L I) d
  exact ⟨e, fun n m _ a ↦ he n m a⟩

end CategoryTheory
