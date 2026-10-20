/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Algebra.Homology.HomComplex

/-!
# Signed double internal Hom and mapping cones

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08JC;
derived.tex, Definition 014E (blueprint: lem-sf-double-hom-cone-comparison).
The component equations below are equations of module sheaves, hence include every
local section and all restriction maps. Mathlib orders the cone summands as A[1], B.
-/

@[expose] public section

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SignedDoubleHomCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}

/-- The module category used in the signed comparison; this is just the recorded
ringed-site module category, in a universe containing the small site.
Source: Stacks 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{max u v w, r, v, u}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- Integer cochain complexes in the recorded module category.
Source: Stacks 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
abbrev Complex (R : Sheaf J CommRingCat.{r}) := CochainComplex (Modules.{u, v, w, r} R) ℤ

/-- Binary biproducts computed from the existing sectionwise products. This supplies
cones without any sheafification or injectivity assumption.
Source: Stacks 014E (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable instance moduleBinaryBiproducts : HasBinaryBiproducts (Modules.{u, v, w, r} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Internal Hom into the fixed complex, using the recorded Hom bifunctor.
Source: Stacks 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable abbrev dual (I : Complex.{u, v, w, r} R) :
    (Complex.{u, v, w, r} R)ᵒᵖ ⥤ Complex.{u, v, w, r} R :=
  (homComplexFunctor (R := R)).flip.obj I

/-- Twice applying the same contravariant internal Hom.
Source: Stacks 08JC (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable abbrev doubleDual (I : Complex.{u, v, w, r} R) :
    Complex.{u, v, w, r} R ⥤ Complex.{u, v, w, r} R :=
  (dual I).rightOp ⋙ dual I

/-- The specified product projection of the existing Hom complex, with an explicit
index equality for reindexing.
Source: Stacks 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable def proj (K I : Complex.{u, v, w, r} R) (n a b : ℤ) (h : a + n = b) :
    (homComplex K I).X n ⟶ SheafOfModules.homObj (K.X a) (I.X b) :=
  Classical.choose (homComplex_projections_exists (R := R)) K I n a b h

/-- The existing product universal property, with the same projections as `proj`.
Source: Stacks 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable def productLimit (K I : Complex.{u, v, w, r} R) (n : ℤ) :
    IsLimit (Fan.mk ((homComplex K I).X n) (fun a : ℤ ↦ proj K I n a (a + n) rfl)) :=
  Classical.choice
    ((Classical.choose_spec (homComplex_projections_exists (R := R))).1 K I n)

/-- The unsigned graded inclusion X^q into T(Cone u)^q, extending maps by zero
on the A[1] summand. Its data come from the product universal property.
Source: Stacks 014E and 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable def inB (I : Complex.{u, v, w, r} R)
    {A B : Complex.{u, v, w, r} R} (f : A ⟶ B) (q : ℤ) :
    (homComplex B I).X q ⟶ (homComplex (CochainComplex.mappingCone f) I).X q :=
  Fan.IsLimit.lift (productLimit _ I q) (fun a : ℤ ↦
    proj B I q a (a + q) rfl ≫
      SheafOfModules.homObjMap (HomologicalComplex.homotopyCofiber.sndX f a) (𝟙 _))

/-- The unsigned graded inclusion Y^r into T(Cone u)^(r+1), extending maps by
zero on the B summand.
Source: Stacks 014E and 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable def inA (I : Complex.{u, v, w, r} R)
    {A B : Complex.{u, v, w, r} R} (f : A ⟶ B) (t : ℤ) :
    (homComplex A I).X t ⟶ (homComplex (CochainComplex.mappingCone f) I).X (t + 1) :=
  Fan.IsLimit.lift (productLimit _ I (t + 1)) (fun a : ℤ ↦
    proj A I t (a + 1) (a + (t + 1)) (by omega) ≫
      SheafOfModules.homObjMap
        (HomologicalComplex.homotopyCofiber.fstX f a (a + 1) rfl) (𝟙 _))

/-- Reindex T(K)^t into T(K[1])^(t+1) without multiplying by a sign.
Source: Stacks 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable def reindexOne (K I : Complex.{u, v, w, r} R) (t : ℤ) :
    (homComplex K I).X t ⟶ (homComplex (K⟦(1 : ℤ)⟧) I).X (t + 1) :=
  Fan.IsLimit.lift (productLimit _ I (t + 1)) (fun a : ℤ ↦
    proj K I t (a + 1) (a + (t + 1)) (by omega) ≫
      SheafOfModules.homObjMap (K.shiftFunctorObjXIso 1 a (a + 1) rfl).hom (𝟙 _))

/-- The cone map induced by a commutative square, with no homotopy correction.
Source: Stacks 014E (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable abbrev coneMap {a b : Arrow (Complex.{u, v, w, r} R)} (h : a ⟶ b) :=
  CochainComplex.mappingCone.map a.hom b.hom h.left h.right h.w.symm

/-- Signed shift and cone comparisons for double internal Hom into an arbitrary I.
Source: Stacks 014E and 0A8X; explicit calculation filling the omission in 08JC
(blueprint: lem-sf-double-hom-cone-comparison).

Proof: (1) Write eps(t)=(-1)^t. Reindexing a degree q map from K[m] gives degree
q-m from K. Multiplication by eps(mq) intertwines the two differentials: both
sides are eps(mq+m)d_I f - eps(mq+q)f d_K. The same sign gives the inverse;
precomposition proves naturality. (2) Define chi as minus s at (T(K),-1)
after T(s at (K,1)) inverse. On y of degree t its sign is
-eps(p)eps(t+1)=eps(p+t). (3) Restricting maps from the binary cone summands
gives T(E)^q=X^q plus Y^(q-1); its differential is
(d_X x, d_Y y + eps(q+1)T(u)x). (4) Applying Hom again gives
alpha'_q=d_I alpha_q-eps(p)alpha_(q+1)d_X+eps(p+q)beta_q T(u),
and beta'_t=d_I beta_t-eps(p)beta_(t+1)d_Y. (5) Set gamma_t=eps(p+t)beta_t.
Then the differential is (d alpha+T²(u)gamma,-d gamma), the cone differential.
The same sign constructs the inverse. (6) For a square, cone maps act diagonally
on X and Y, and these actions commute with eps(p+t), proving naturality.
(7) T²(i) sends alpha to (alpha,0). T²(-pi) evaluates to -beta, and chi
turns this into -gamma, which is -pi after theta. These are equations of
restricted module maps, so they hold as sheaf maps. Only binary sums, products,
reindexing and signs are used; there is no boundedness, flatness or K-injectivity.
-/
theorem comparison (I : Complex.{u, v, w, r} R) :
    ∃ s : ∀ (K : Complex.{u, v, w, r} R) (m : ℤ),
      homComplex (K⟦m⟧) I ≅ (homComplex K I)⟦-m⟧,
    ∃ chi : ∀ K : Complex.{u, v, w, r} R,
      (doubleDual I).obj (K⟦(1 : ℤ)⟧) ≅ ((doubleDual I).obj K)⟦(1 : ℤ)⟧,
    ∃ theta : ∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B),
      (doubleDual I).obj (CochainComplex.mappingCone f) ≅
        CochainComplex.mappingCone ((doubleDual I).map f),
    (∀ (K : Complex.{u, v, w, r} R) (m q a : ℤ),
      (s K m).hom.f q ≫
          ((homComplex K I).shiftFunctorObjXIso (-m) q (q - m) (by omega)).hom ≫
          proj K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • (proj (K⟦m⟧) I q a (a + q) rfl ≫
          SheafOfModules.homObjMap (K.shiftFunctorObjXIso m a (a + m) rfl).inv (𝟙 _))) ∧
    (∀ {K L : Complex.{u, v, w, r} R} (f : K ⟶ L) (m : ℤ),
      (dual I).map (f⟦m⟧').op ≫ (s K m).hom =
        (s L m).hom ≫ ((dual I).map f.op)⟦-m⟧') ∧
    (∀ K : Complex.{u, v, w, r} R,
      (chi K).hom = -((dual I).map (s K 1).inv.op ≫ (s (homComplex K I) (-1)).hom)) ∧
    (∀ (K : Complex.{u, v, w, r} R) (p t : ℤ),
      (chi K).hom.f p ≫
          (((doubleDual I).obj K).shiftFunctorObjXIso 1 p (p + 1) rfl).hom ≫
          proj (homComplex K I) I (p + 1) t (t + (p + 1)) rfl =
        (p + t).negOnePow •
          (proj (homComplex (K⟦(1 : ℤ)⟧) I) I p (t + 1) (t + (p + 1)) (by omega) ≫
            SheafOfModules.homObjMap (reindexOne K I t) (𝟙 _))) ∧
    (∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B) (p q : ℤ),
      (theta f).hom.f p ≫
          HomologicalComplex.homotopyCofiber.sndX ((doubleDual I).map f) p ≫
          proj (homComplex B I) I p q (q + p) rfl =
        proj (homComplex (CochainComplex.mappingCone f) I) I p q (q + p) rfl ≫
          SheafOfModules.homObjMap (inB I f q) (𝟙 _)) ∧
    (∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B) (p t : ℤ),
      (theta f).hom.f p ≫
          HomologicalComplex.homotopyCofiber.fstX ((doubleDual I).map f) p (p + 1) rfl ≫
          proj (homComplex A I) I (p + 1) t (t + (p + 1)) rfl =
        (p + t).negOnePow •
          (proj (homComplex (CochainComplex.mappingCone f) I) I p (t + 1)
            (t + (p + 1)) (by omega) ≫ SheafOfModules.homObjMap (inA I f t) (𝟙 _))) ∧
    (∀ {a b : Arrow (Complex.{u, v, w, r} R)} (h : a ⟶ b),
      (doubleDual I).map (coneMap h) ≫ (theta b.hom).hom =
        (theta a.hom).hom ≫ coneMap ((doubleDual I).mapArrow.map h)) ∧
    (∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B),
      (doubleDual I).map (CochainComplex.mappingCone.inr f) ≫ (theta f).hom =
        CochainComplex.mappingCone.inr ((doubleDual I).map f)) ∧
    (∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B),
      (doubleDual I).map (CochainComplex.mappingCone.triangle f).mor₃ ≫ (chi A).hom =
        (theta f).hom ≫ (CochainComplex.mappingCone.triangle ((doubleDual I).map f)).mor₃) := by
  sorry

end CategoryTheory.SignedDoubleHomCone
