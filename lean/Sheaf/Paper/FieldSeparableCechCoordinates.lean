/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.ContinuousRingUniverseRealization
public import Mathlib.FieldTheory.Galois.Profinite
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Data.Matrix.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

import Sheaf.FieldTheory.AlgebraicSeparableSmooth
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition
import Sheaf.Paper.CondensedPointCoefficients
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition

/-! # Separable-closure Cech coordinates

Source: Bhatt--Scholze, Sections 4.2 and 7.3, and Hemo--Richarz--Scholbach,
Example 3.1; the ten-step field coordinate calculation in the DAG.
(blueprint: lem-sfb-field-separable-cech-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj Simplicial

namespace AlgebraicGeometry.ProEtale
namespace FieldSeparableCech

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The separable-closure morphism is weakly etale.
Source: Bhatt--Scholze, Example 4.1.4; DAG proof step 1.
(blueprint: lem-sfb-field-separable-cech-coordinates).
Proof: finite subsets of Ω lie in finite Galois subextensions. Their finite etale
algebras form a filtered system with union Ω. Thus the extension is ind-etale,
hence weakly etale, by lem-kun-algebraic-separable-smooth and
lem-weil-pbc-ind-etale-stability. -/
theorem weaklyEtale : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  sorry

/-- The actual closure object in the small site, with its proved structural property.
Source: Bhatt--Scholze, Example 4.1.4, DAG proof step 1.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def closureObject : (Spec (.of k)).ProEt :=
  @Scheme.ProEt.mk _ _ (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (weaklyEtale k Ω)

/-- The closure map as an arrow of the small site, with final target.
Source: the field Cech construction, DAG proof steps 1--3.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def closureArrow : Arrow (Spec (.of k)).ProEt :=
  { left := closureObject k Ω
    right := Scheme.ProEt.mk (𝟙 (Spec (.of k)))
    hom := MorphismProperty.Over.homMk (closureObject k Ω).hom (Category.comp_id _) }

/-- The (q+1)-fold fibre product, formed inside the small pro-etale site.
Source: the field Cech construction, DAG proof steps 2--3.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
abbrev object (q : ℕ) : (Spec (.of k)).ProEt :=
  (closureArrow k Ω).cechNerve.obj (op ⦋q⦌)

/-- The profinite power of the Krull Galois group, including its singleton zeroth power.
Source: Stacks Tag 0BU2; DAG proof step 3.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def power (q : ℕ) : Profinite.{u} := Profinite.of (Fin q → (Ω ≃ₐ[k] Ω))

/-- Ordered cumulative products of the successive Galois increments.
Source: the pure-tensor formula in DAG proof steps 2 and 4.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def cumulative {q : ℕ} (g : Fin q → (Ω ≃ₐ[k] Ω)) (j : ℕ) : Ω ≃ₐ[k] Ω :=
  ((List.ofFn g).take j).prod

/-- The Ω-point of Ω[S] associated to g, using evaluation of locally constant integers.
Source: the inverse-limit coordinates in DAG proof step 3.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def testPoint (q : ℕ) (g : power k Ω q) :
    Spec (.of Ω) ⟶ ((profiniteToProEtOf (Spec (.of Ω))).obj (power k Ω q)).left :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom
      ((Int.castRingHom Ω).comp (LocallyConstant.evalRingHom g))))
    (𝟙 _) (specULiftZIsTerminal.hom_ext _ _)

/-- The actual ring of sections of the pulled-back condensed coefficient ring.
Source: HRS Example 3.1; DAG proof step 5.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
abbrev sections (A : Type u) [NormedField A] (q : ℕ) : CommRingCat.{u + 1} :=
  (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology (Spec (.of k)))
    (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of k)))).obj.obj
      (op (object k Ω q))

/-- The canonical vertex characterization of the incremental coordinate isomorphisms.
Source: the pure-tensor formula in DAG proof steps 2--4.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def AreCoordinates
    (e : ∀ q : ℕ, (object k Ω q).left ≅
      ((profiniteToProEtOf (Spec (.of Ω))).obj (power k Ω q)).left) : Prop :=
  (∀ q : ℕ, (e q).inv ≫
      (WidePullback.π (fun _ : Fin (q + 1) ↦ (closureArrow k Ω).hom) 0).left =
    ((profiniteToProEtOf (Spec (.of Ω))).obj (power k Ω q)).hom) ∧
  ∀ (q : ℕ) (g : power k Ω q) (j : Fin (q + 1)),
    testPoint k Ω q g ≫ (e q).inv ≫
        (WidePullback.π (fun _ : Fin (q + 1) ↦ (closureArrow k Ω).hom) j).left =
      Spec.map (CommRingCat.ofHom (cumulative k Ω g j.val).toRingHom)

/-- The singleton closure map covers, and its nerve has the incremental Galois coordinates.
The vertex equations specify the convention on every geometric Ω-point and every degree.
Source: Bhatt--Scholze, Section 4.2; Stacks Tag 0BU2; DAG proof steps 1--4.
(blueprint: lem-sfb-field-separable-cech-coordinates).
Proof: the extension is faithfully flat and ind-etale, hence its affine singleton
is a pro-etale cover. At a finite Galois stage E the tensor decomposition sends
(a₀,...,a_q) to a₀ g₁(a₁) (g₁g₂)(a₂)...(g₁...g_q)(a_q).
Tensor products commute with the filtered union of finite Galois E. Taking Spec
and using the Krull limit gives Ω[G^q]; the finite Galois quotients are cofinal
among finite continuous quotients. The displayed formula identifies all vertex
projections. Deleting a vertex combines adjacent increments, deleting vertex zero
moves the base by g₁, and repeating a vertex inserts 1. Thus a descent map from
vertex 1 to vertex 0 satisfies c(g)c(h)=c(gh). -/
theorem coordinates :
    Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ∈
      Scheme.proetalePrecoverage (Spec (.of k)) ∧
    ∃ e : ∀ q : ℕ, (object k Ω q).left ≅
        ((profiniteToProEtOf (Spec (.of Ω))).obj (power k Ω q)).left,
      AreCoordinates k Ω e := by
  sorry

/-- The coefficient morphism is the inverse image of the recorded postcomposition map.
Source: HRS Example 3.1; DAG proof step 9.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
abbrev coefficientMap (X : Scheme.{u}) {A B : Type u} [NormedField A] [NormedField B]
    (φ : A →+* B) (hφ : Continuous φ) :
    condensedRingObj (Profinite.continuousCoefficientRingObj A) X ⟶
      condensedRingObj (Profinite.continuousCoefficientRingObj B) X :=
  (upperStarFromPoint X).map (Profinite.continuousMapRingObjMapOfUniverse φ hφ)

/-- The actual coefficient map preserves the transported ring structures.
Source: HRS Example 3.1; DAG proof step 9.
(blueprint: lem-sfb-field-separable-cech-coordinates).
Proof: postcomposition preserves addition, multiplication and unit on each profinite
set by def-sfb-continuous-map-condensed-ring-map. The strong monoidal inverse image
preserves these equations by sk-def-sfb-pulled-back-coefficients. -/
@[instance] theorem coefficientMap_isMonHom (X : Scheme.{u}) {A B : Type u}
    [NormedField A] [NormedField B] (φ : A →+* B) (hφ : Continuous φ) :
    IsMonHom (coefficientMap X φ hφ) := by
  sorry

/-- The increment transformation induced by a simplex map. The initial vertex can move;
its coefficient action is trivial. Adjacent products have the order g h.
Source: DAG proof step 4.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def reindex {n m : ℕ} (α : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (g : power k Ω m) : power k Ω n :=
  fun j ↦ (cumulative k Ω g (α.toOrderHom j.castSucc).val)⁻¹ *
    cumulative k Ω g (α.toOrderHom j.succ).val

/-- The group nerve face and degeneracy formulas, including the base move at vertex zero.
Every simplex map is included, so repeating a vertex inserts 1 and deleting an interior
vertex multiplies adjacent increments in the order g h.
Source: DAG proof step 4; Bhatt--Scholze Section 7.4 conventions.
(blueprint: lem-sfb-field-separable-cech-coordinates).
Proof: substitute the cumulative-product vertex formula from steps 2--3. The new base
is the old cumulative product at α(0); dividing each selected consecutive cumulative
product on the left by its predecessor gives reindex. Equality holds on Ω-points,
which determine maps from the reduced locally constant Ω-algebra. The three edges
of a two-simplex have labels g,h,gh, giving c(gh)=c(g)c(h). -/
theorem face_coordinates
    (e : ∀ q : ℕ, (object k Ω q).left ≅
      ((profiniteToProEtOf (Spec (.of Ω))).obj (power k Ω q)).left)
    (he : AreCoordinates k Ω e) (n m : ℕ)
    (α : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (g : power k Ω m) :
    testPoint k Ω m g ≫ (e m).inv ≫ ((closureArrow k Ω).cechNerve.map α.op).left =
      Spec.map (CommRingCat.ofHom (cumulative k Ω g (α.toOrderHom 0).val).toRingHom) ≫
        testPoint k Ω n (reindex k Ω α g) ≫ (e n).inv := by
  sorry

/-- Canonical Cech section rings, natural in every simplex map and continuous field map.
Source: Bhatt--Scholze Lemma 4.2.12; HRS Example 3.1; DAG proof steps 5 and 9.
(blueprint: lem-sfb-field-separable-cech-coordinates).
Proof: the finite Galois tensor formula identifies W_q with Spec LC(G^q,Ω).
Its underlying space is G^q by lem-weil-pbc-locally-constant-prime-spectrum.
Ultrametric balls make A totally disconnected without completeness. Apply
lem-weil-pbc-condensed-field-continuous-realization on Spec k, with its adjoint
test-object normalization, to identify the actual pulled-back ring with C(|-|,A).
Naturality makes every face and degeneracy act by precomposition with the
increment map. Moving the geometric vertex acts trivially on its one-point space.
The adjoint normalization also makes the coefficient map postcomposition by φ,
by def-sfb-continuous-map-condensed-ring-map. For q=0 this gives C(*,A)=A. -/
theorem section_coordinates
    (e : ∀ q : ℕ, (object k Ω q).left ≅
      ((profiniteToProEtOf (Spec (.of Ω))).obj (power k Ω q)).left)
    (he : AreCoordinates k Ω e) :
    ∃ c : ∀ (A : Type u) [NormedField A], IsNonarchimedean (norm : A → ℝ) →
        ∀ q : ℕ, sections k Ω A q ≃+* C(power k Ω q, A),
      (∀ (A : Type u) [NormedField A] (hA : IsNonarchimedean (norm : A → ℝ))
        (q : ℕ) (f : sections k Ω A q) (g : power k Ω q),
        c A hA q f g =
          ((ContinuousRingUniverse.comparison (Spec (.of k)) A).hom.app
            (op (object k Ω q)) f).down
              ((testPoint k Ω q g ≫ (e q).inv).base (IsLocalRing.closedPoint Ω))) ∧
      (∀ (A : Type u) [NormedField A] (hA : IsNonarchimedean (norm : A → ℝ))
        (n m : ℕ) (α : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
        (f : sections k Ω A n) (g : power k Ω m),
        c A hA m
          ((condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of k))).obj.map
            ((closureArrow k Ω).cechNerve.map α.op).op f) g =
          c A hA n f (reindex k Ω α g)) ∧
      (∀ (A B : Type u) [NormedField A] [NormedField B]
        (hA : IsNonarchimedean (norm : A → ℝ)) (hB : IsNonarchimedean (norm : B → ℝ))
        (φ : A →+* B) (hφ : Continuous φ) (q : ℕ) (f : sections k Ω A q)
        (g : power k Ω q),
        c B hB q ((coefficientMap (Spec (.of k)) φ hφ).hom.app (op (object k Ω q)) f) g =
          φ (c A hA q f g)) := by
  sorry

/-- A regular-module endomorphism is multiplication by the constant a on every object.
This uses the actual adjoint realization of the pulled-back coefficient ring.
Source: HRS Example 3.1; DAG proof step 8.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def IsConstantEntry (A : Type u) [NormedField A]
    (f : Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj A)
      (Spec (.of Ω))) ⟶ Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj A)
      (Spec (.of Ω)))) (a : A) : Prop :=
  ∀ (U : (Spec (.of Ω)).ProEt)
    (x : (condensedRingObj (Profinite.continuousCoefficientRingObj A)
      (Spec (.of Ω))).obj.obj (op U)),
    ((ContinuousRingUniverse.comparison (Spec (.of Ω)) A).hom.app (op U)
      (f.hom.hom.app (op U) x)).down =
      ContinuousMap.const U.left a *
        ((ContinuousRingUniverse.comparison (Spec (.of Ω)) A).hom.app (op U) x).down

/-- Constant matrix entries characterize the finite-free module morphism.
Source: HRS Example 3.1; DAG proof step 8.
(blueprint: lem-sfb-field-separable-cech-coordinates). -/
def HasMatrix (A : Type u) [NormedField A] {m n : ℕ}
    (f : Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj A)
      (Spec (.of Ω))) n ⟶ Mod.finiteFree
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of Ω))) m)
    (T : Matrix (Fin m) (Fin n) A) : Prop :=
  ∀ (i : Fin m) (j : Fin n), IsConstantEntry Ω A
    (biproduct.ι (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of Ω)))) j ≫
      f ≫ biproduct.π (fun _ : Fin m ↦ Mod.regular
        (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of Ω)))) i) (T i j)

/-- Lisse modules over the separably closed point are finite free; all morphisms are
constant matrices, including zero ranks. Ordinary internal extension is entrywise.
Source: Bhatt--Scholze Section 7.3; HRS Example 3.1; DAG proof steps 6--10.
(blueprint: lem-sfb-field-separable-cech-coordinates).
Proof: Spec Ω is w-contractible: its unique local ring is strictly henselian and
its component space is a singleton. By det-pe-wcb-clopen-partition a trivializing
cover has a member with a section. Restrict the slice trivialization along this
section, using def-pur-localized-ringed-site and the section-module equivalence;
this gives global finite freeness. A module map is determined by its standard
basis sections. Point evaluation gives Γ(Ω,R_A)=A, so these are precisely constant
matrices. Finite sums are also products; empty rows or columns give the unique
zero morphism. For φ:A→B the balancing coequalizer gives B⊗_A A≅B by b⊗a↦bφ(a)
and b↦b⊗1. Apply this on all finite summands. The normalization on the scalar
unit is the coefficient map on each basis inclusion. Thus a matrix extends
entrywise by φ. No completion, coefficient algebraic closure, or tensor-of-sections
formula is used. -/
theorem module_coordinates [IsSepClosed Ω] :
    (∀ (A : Type u) [NormedField A] (_hA : IsNonarchimedean (norm : A → ℝ))
      (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of Ω)))),
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj A) M →
        Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj A)
          (Spec (.of Ω))) M) ∧
    (∀ (A : Type u) [NormedField A] (_hA : IsNonarchimedean (norm : A → ℝ)) (m n : ℕ),
      ∃ E : (Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj A)
          (Spec (.of Ω))) n ⟶ Mod.finiteFree
          (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of Ω))) m)
          ≃+ Matrix (Fin m) (Fin n) A,
        ∀ f, HasMatrix Ω A f (E f)) ∧
    (∀ (A B : Type u) [NormedField A] [NormedField B]
      (_hA : IsNonarchimedean (norm : A → ℝ)) (_hB : IsNonarchimedean (norm : B → ℝ))
      (φ : A →+* B) (hφ : Continuous φ),
      ∃ e : ∀ n : ℕ,
        (Mod.extendScalars (coefficientMap (Spec (.of Ω)) φ hφ)).obj
          (Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj A)
            (Spec (.of Ω))) n) ≅
          Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj B)
            (Spec (.of Ω))) n,
        (∀ (n : ℕ) (j : Fin n),
          (biproduct.ι (fun _ : Fin n ↦ Mod.regular
            (condensedRingObj (Profinite.continuousCoefficientRingObj A)
              (Spec (.of Ω)))) j).hom ≫
              Mod.extendUnitHom (coefficientMap (Spec (.of Ω)) φ hφ)
                (Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj A)
                  (Spec (.of Ω))) n) ≫ (e n).hom.hom =
            coefficientMap (Spec (.of Ω)) φ hφ ≫
              (biproduct.ι (fun _ : Fin n ↦ Mod.regular
                (condensedRingObj (Profinite.continuousCoefficientRingObj B)
                  (Spec (.of Ω)))) j).hom) ∧
        ∀ (m n : ℕ)
          (f : Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj A)
            (Spec (.of Ω))) n ⟶ Mod.finiteFree
            (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of Ω))) m)
          (T : Matrix (Fin m) (Fin n) A),
          HasMatrix Ω A f T →
            HasMatrix Ω B ((e n).inv ≫
              (Mod.extendScalars (coefficientMap (Spec (.of Ω)) φ hφ)).map f ≫ (e m).hom)
              (T.map φ)) := by
  sorry

end FieldSeparableCech
end AlgebraicGeometry.ProEtale
