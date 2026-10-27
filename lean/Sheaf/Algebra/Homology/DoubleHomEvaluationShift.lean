/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Signed integer shifts of double-Hom evaluation

Source: Stacks Project, more-algebra.tex, Tags 0A60 and 0A61 and section-sign-rules.
The all-integer shift calculation is the explicit expansion in the DAG proof.
(blueprint: lem-trf-double-hom-evaluation-shift)

The existential maps below are characterized on every homogeneous product coordinate
and every pure tensor. All auxiliary definitions use the existing Hom and total tensor;
no new model of complexes or internal Hom is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.DoubleHomEvaluationShift

variable {R : Type u} [CommRing R]

/-- The one-object-site presentation of integer complexes of ordinary modules.
Source: Stacks 0A60 (blueprint: lem-trf-double-hom-evaluation-shift). -/
abbrev Complex (R : Type u) [CommRing R] := CochainComplex (RingSiteModules R) ℤ

/-- Specialize the recorded product Hom, with its standard Hom differential.
Source: Stacks 0A60, section-sign-rules
(blueprint: lem-trf-double-hom-evaluation-shift). -/
abbrev hom (U V : Complex R) : Complex R :=
  homComplex (R := CochainComplex.onePointRingSheaf R) U V

/-- The recorded componentwise contravariant/covariant action of Hom.
Source: Stacks 0A60 (blueprint: lem-trf-double-hom-evaluation-shift). -/
def homMap {U U' V V' : Complex R} (f : U' ⟶ U) (g : V ⟶ V') :
    hom U V ⟶ hom U' V' :=
  ((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).map f.op).app V ≫
    ((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).obj (op U')).map g

/-- The induced covariant/contravariant/covariant action on double Hom.
Source: Stacks 0A60 (blueprint: lem-trf-double-hom-evaluation-shift). -/
def doubleMap {P P' J J' I I' : Complex R}
    (p : P ⟶ P') (j : J' ⟶ J) (i : I ⟶ I') :
    hom (hom P J) I ⟶ hom (hom P' J') I' := homMap (homMap p j) i

/-- Direct-sum total tensor in the existing sheaf-module monoidal structure.
Source: Stacks 0A60, section-sign-rules
(blueprint: lem-trf-double-hom-evaluation-shift). -/
def tensor (U V : Complex R) : Complex R := by
  letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf R)
  exact CochainComplex.mapBifunctor U V (curriedTensor (RingSiteModules R))

/-- The existing tensor bifunctor applied to chain maps.
Source: Stacks 0A60 (blueprint: lem-trf-double-hom-evaluation-shift). -/
def tensorMap {U U' V V' : Complex R} (f : U ⟶ U') (g : V ⟶ V') :
    tensor U V ⟶ tensor U' V' := by
  letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf R)
  exact HomologicalComplex.mapBifunctorMap f g (curriedTensor (RingSiteModules R)) (.up ℤ)

/-- The canonical second-variable tensor shift, whose summand sign is `(-1)^(ma)`.
Source: Stacks, section-sign-rules; Mathlib `mapBifunctorShift₂Iso`.
(blueprint: lem-trf-double-hom-evaluation-shift). -/
def tensorShift (U V : Complex R) (m : ℤ) : tensor U (V⟦m⟧) ≅ (tensor U V)⟦m⟧ := by
  letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf R)
  exact CochainComplex.mapBifunctorShift₂Iso U V (curriedTensor (RingSiteModules R)) m

/-- A homogeneous pure tensor, using the existing sheafification unit and total inclusion.
Source: Stacks 0A60 and 03EK (blueprint: lem-trf-double-hom-evaluation-shift). -/
def pure (U V : Complex R) (a b n : ℤ) (hab : a + b = n)
    (W : (Discrete PUnit.{u + 1})ᵒᵖ) (x : (U.X a).val.obj W) (y : (V.X b).val.obj W) :
    ((tensor U V).X n).val.obj W := by
  letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf R)
  exact (CochainComplex.ιMapBifunctor U V (curriedTensor (RingSiteModules R))
    a b n hab).val.app W
      ((homTensorCurrySectionMap (CochainComplex.onePointRingSheaf R)
        (U.X a) (V.X b)).app W (x ⊗ₜ[(CochainComplex.onePointRingSheaf R).obj.obj W] y))

/-- Evaluate a coordinate of the recorded product Hom, allowing an explicit index equality.
Source: Stacks 0A60 and 0A8X (blueprint: lem-trf-double-hom-evaluation-shift). -/
def value (U V : Complex R) (n a b : ℤ) (hab : a + n = b)
    (W : (Discrete PUnit.{u + 1})ᵒᵖ) (f : ((hom U V).X n).val.obj W)
    (x : (U.X a).val.obj W) : (V.X b).val.obj W :=
  (((homComplexπ (R := CochainComplex.onePointRingSheaf R) U V n a b hab).val.app W f).app
    (op (Over.mk (𝟙 W.unop)))) x

/-- Unsigned source reindexing from degree `c` to degree `c+m`. This is a graded map,
not a chain map; its signed version is characterized in the theorem below.
Source: Stacks, section-sign-rules (blueprint: lem-trf-double-hom-evaluation-shift). -/
def reindex (U V : Complex R) (m c : ℤ) : (hom U V).X c ⟶ (hom (U⟦m⟧) V).X (c + m) :=
  Fan.IsLimit.lift (homComplexIsLimit (R := CochainComplex.onePointRingSheaf R)
    (U⟦m⟧) V (c + m)) (fun a : ℤ ↦
      homComplexπ U V c (a + m) (a + (c + m)) (by omega) ≫
        SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf R)
          (U.shiftFunctorObjXIso m a (a + m) rfl).hom (𝟙 _))

/-- Signed integer-shift compatibility of double-Hom evaluation for arbitrary complexes.
Source: Stacks Project, more-algebra.tex, Tags 0A60 and 0A61, section-sign-rules;
the all-integer signed reindexing calculation is expanded in the node's proof.
(blueprint: lem-trf-double-hom-evaluation-shift).

Proof:
1. For degrees a,b,c define E(h tensor x)(f)=(-1)^(bc) h(f(x)). This is balanced
and linear and extends over the direct-sum tensor. Hom elements are arbitrary product
families, so no boundedness or finite support in the Hom variables is required.
2. Expand the Hom and tensor differentials. Both sides of the chain condition have
terms (-1)^(bc)d_I h(f(x)), -(-1)^(a+bc)h(d_J f(x)), and
(-1)^(a+bc+c)h(f(d_P x)). Hence E is a chain map, also for shifted P.
3. Reindex a degree-q map from U[m] to V and multiply by (-1)^(mq).
Both differentials become (-1)^(mq+m)d_V f - (-1)^(mq+q)f d_U.
The inverse has the same sign. Degree-zero composition proves naturality.
4. Tensor shift multiplies h tensor x by (-1)^(ma). Its inverse has the same
sign, and the two differential coefficients are (-1)^(ma+m) and
(-1)^(ma+a+m). Composition with degree-zero maps proves naturality.
5. Compose inverse Hom(s,I), the outer source shift for -m, and (-1)^m.
For g of degree n and f of degree c the sign is
(-1)^(m(c+m)-mn+m)=(-1)^(m(n+c)), since m(m+1) and 2mn are even.
These natural chain isomorphisms give chi with the stated component formula.
6. If x has original degree b, its shifted degree is b-m. The two sides of the
square have exponents (b-m)(c+m)+m(a+b-m+c) and bc+ma. Their difference is
2m(b-m), which is even for every integer m. Product extensionality and generation
by homogeneous tensors give equality of chain maps. No flatness, injectivity or
boundedness has been used. -/
theorem signed_evaluation_shift :
    ∃ (s : ∀ (U V : Complex R) (m : ℤ), hom (U⟦m⟧) V ≅ (hom U V)⟦-m⟧)
      (E : ∀ P J I : Complex R, tensor (hom J I) P ⟶ hom (hom P J) I)
      (χ : ∀ (P J I : Complex R) (m : ℤ),
        hom (hom (P⟦m⟧) J) I ≅ (hom (hom P J) I)⟦m⟧),
      (∀ (U V : Complex R) (m q a : ℤ),
        (s U V m).hom.f q ≫
            ((hom U V).shiftFunctorObjXIso (-m) q (q - m) (by omega)).hom ≫
            homComplexπ U V (q - m) (a + m) (a + q) (by omega) =
          (m * q).negOnePow • (homComplexπ (U⟦m⟧) V q a (a + q) rfl ≫
            SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf R)
              (U.shiftFunctorObjXIso m a (a + m) rfl).inv
              (𝟙 _))) ∧
      (∀ (U U' V V' : Complex R) (f : U' ⟶ U) (g : V ⟶ V') (m : ℤ),
        homMap (f⟦m⟧') g ≫ (s U' V' m).hom =
          (s U V m).hom ≫ (homMap f g)⟦-m⟧') ∧
      (∀ (P J I : Complex R) (a b c : ℤ) (W : (Discrete PUnit.{u + 1})ᵒᵖ)
        (h : ((hom J I).X a).val.obj W) (x : (P.X b).val.obj W)
        (f : ((hom P J).X c).val.obj W),
        value (hom P J) I (a + b) c (a + b + c) (by omega) W
            ((E P J I).f (a + b) |>.val.app W
              (pure (hom J I) P a b (a + b) rfl W h x)) f =
          (b * c).negOnePow • value J I a (b + c) (a + b + c) (by omega) W h
            (value P J c b (b + c) rfl W f x)) ∧
      (∀ (P J I : Complex R) (m : ℤ),
        (χ P J I m).hom = m.negOnePow •
          (homMap (s P J m).inv (𝟙 I) ≫ (s (hom P J) I (-m)).hom ≫
            eqToHom (congrArg (fun t : ℤ ↦ (hom (hom P J) I)⟦t⟧) (neg_neg m)))) ∧
      (∀ (P J I : Complex R) (m n c : ℤ),
        (χ P J I m).hom.f n ≫
            ((hom (hom P J) I).shiftFunctorObjXIso m n (n + m) rfl).hom ≫
            homComplexπ (hom P J) I (n + m) c (c + (n + m)) rfl =
          (m * (n + c)).negOnePow •
            (homComplexπ (hom (P⟦m⟧) J) I n (c + m) (c + (n + m)) (by omega) ≫
              SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf R)
                (reindex P J m c) (𝟙 _))) ∧
      (∀ (P J I : Complex R) (m a b : ℤ) (W : (Discrete PUnit.{u + 1})ᵒᵖ)
        (h : ((hom J I).X a).val.obj W) (x : ((P⟦m⟧).X b).val.obj W),
        (((tensor (hom J I) P).shiftFunctorObjXIso m (a + b) (a + b + m)
            rfl).hom.val.app W)
            ((tensorShift (hom J I) P m).hom.f (a + b) |>.val.app W
              (pure (hom J I) (P⟦m⟧) a b (a + b) rfl W h x)) =
          (m * a).negOnePow • pure (hom J I) P a (b + m) (a + b + m) (by omega) W h
            ((P.shiftFunctorObjXIso m b (b + m) rfl).hom.val.app W x)) ∧
      (∀ (P P' J J' I I' : Complex R) (p : P ⟶ P') (j : J' ⟶ J) (i : I ⟶ I')
        (m : ℤ),
        doubleMap (p⟦m⟧') j i ≫ (χ P' J' I' m).hom =
          (χ P J I m).hom ≫ (doubleMap p j i)⟦m⟧') ∧
      (∀ (P P' J J' I I' : Complex R) (p : P ⟶ P') (j : J' ⟶ J) (i : I ⟶ I')
        (m : ℤ),
        tensorMap (homMap j i) (p⟦m⟧') ≫ (tensorShift (hom J' I') P' m).hom =
          (tensorShift (hom J I) P m).hom ≫ (tensorMap (homMap j i) p)⟦m⟧') ∧
      (∀ (P J I : Complex R) (m : ℤ),
        E (P⟦m⟧) J I ≫ (χ P J I m).hom =
          (tensorShift (hom J I) P m).hom ≫ (E P J I)⟦m⟧') := by
  sorry

end CategoryTheory.DoubleHomEvaluationShift
