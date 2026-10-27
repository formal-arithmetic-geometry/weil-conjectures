/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Algebra.DirectSum.Module
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
import Sheaf.Paper.AffineProjectiveComplexDerivedHom
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Finite flat models for relative derived Hom

Source: Stacks Project, More on Algebra, Tag 0E1U, with Tags 0DHV, 0653 and 0A66.
(blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model).
The model category has actual derived morphisms. Thus natural isomorphisms on it
express naturality in derived morphisms, including changes of representatives.
Scalar extension uses the left-tensor convention of `ModuleCat.extendScalars`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings

namespace CochainComplex

/-- The choices allowed in the finite-flat Hom model, with no chosen bases.
Flatness is measured after restriction to R; finite presentation is over S.
Source: Stacks 0E1U (blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
structure RelativeFiniteFlatHomModel (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] where
  P : CochainComplex (ModuleCat.{u} S) ℤ
  F : CochainComplex (ModuleCat.{u} S) ℤ
  upper : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)
  free : ∀ i : ℤ, Module.Free S (P.X i) ∧ Module.Finite S (P.X i)
  bounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i)
  flat : ∀ i : ℤ, Module.Flat R
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (F.X i))
  fp : ∀ i : ℤ, Module.FinitePresentation S (F.X i)

/-- A model is viewed as its pair of derived objects, contravariantly in the source.
Source: Stacks 0E1U (blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
def relativeFiniteFlatHomPair (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] (M : RelativeFiniteFlatHomModel R S) :
    (DerivedCategory (ModuleCat.{u} S))ᵒᵖ × DerivedCategory (ModuleCat.{u} S) :=
  (op (DerivedCategory.Q.obj M.P), DerivedCategory.Q.obj M.F)

/-- Models with all derived morphisms of their source and target, rather than just
chain maps. Source: Stacks 0E1U, naturality of RHom
(blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
abbrev RelativeFiniteFlatHomModels (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] :=
  InducedCategory
    ((DerivedCategory (ModuleCat.{u} S))ᵒᵖ × DerivedCategory (ModuleCat.{u} S))
    (relativeFiniteFlatHomPair R S)

/-- The ordinary termwise tensor over S. For S'=S tensor_R T it is canonically the
termwise tensor over R, by (s tensor t) tensor x ↦ t tensor sx.
Source: Stacks 0661 and 0E1U
(blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
abbrev relativeHomExtend {S B : Type u} [CommRing S] [CommRing B] (φ : S →+* B) :=
  (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)

/-- The derived Hom functor on models after scalar extension. This definition uses
exactly the recorded derived extension and internal Hom, with their existing actions
on arbitrary derived morphisms. Source: Stacks 0E1U
(blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
def relativeHomDerivedFunctor (R S B : Type u)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] (φ : S →+* B) :
    RelativeFiniteFlatHomModels R S ⥤ DerivedCategory (ModuleCat.{u} B) :=
  inducedFunctor (relativeFiniteFlatHomPair R S) ⋙
    ((ModuleCat.ordinaryDerivedExtendScalars φ).op.prod
      (ModuleCat.ordinaryDerivedExtendScalars φ)) ⋙ ordinaryModuleDerivedInternalHom B

/-- The unextended derived Hom functor on the same model category.
Source: Stacks 0E1U (blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
def relativeHomDerivedFunctorOriginal (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] :
    RelativeFiniteFlatHomModels R S ⥤ DerivedCategory (ModuleCat.{u} S) :=
  inducedFunctor (relativeFiniteFlatHomPair R S) ⋙ ordinaryModuleDerivedInternalHom S

/-- The coefficient algebra S_T and its S-algebra map, in the source's order.
Source: Stacks 0E1U (blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
abbrev relativeHomCoefficientMap (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    S →+* S ⊗[R] T :=
  (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom

/-- Coherent families of the chain isomorphisms appearing in the relative Hom model.
This is only the type of the comparison data; its existence and normalizations are
asserted in the theorem below. Source: Stacks 0E1U
(blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
abbrev RelativeHomScalarComparisons (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] :=
  ∀ (T : Type u) [CommRing T] [Algebra R T] (M : RelativeFiniteFlatHomModels R S),
    (relativeHomExtend (relativeHomCoefficientMap R S T)).obj
        (moduleHomComplex M.P M.F) ≅
      moduleHomComplex
        ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.P)
        ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.F)

/-- The derived-to-ordinary counit of the already recorded universal pair.
Source: Stacks 0661 (blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model). -/
abbrev relativeHomScalarCounit {S B : Type u} [CommRing S] [CommRing B]
    (φ : S →+* B) (G : CochainComplex (ModuleCat.{u} S) ℤ) :=
  (ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app G

/-- Finite flat Hom models, their normalized scalar comparisons, and derived naturality.
Source: Stacks 0E1U(a),(b), finite-presentation clause; 0DHV, 0653, 0661 and 0A66.
(blueprint: lem-sfb-relative-rhom-finite-flat-base-change-model).

Proof:
1. Choose bounded-above finite-free P,Q by pseudo-coherence. Flatness of S/R
makes Q termwise R-flat, hence K-flat by lem-pc-module-bounded-flat-kflat.
The lower Tor bound makes Q tensor N exact in degree a-1 for every N.
By lem-pc-module-flat-opcycles-tor-criterion the cokernel of d^(a-1) is
R-flat. Good truncation there gives bounded F representing L. Its new term
has the finite presentation Q^(a-1) -> Q^a -> F^a -> 0.
2. For every allowed P,F, only v-n <= i <= min(u,w-n) contribute to Hom^n.
Thus the product Hom is the stated finite direct sum, vanishing for n<v-u.
Each summand is a finite power of F^(i+n), hence R-flat and finitely presented.
The signed differential is the existing moduleHomComplex differential.
3. Apply lem-sc-affine-projective-complex-derived-hom on the singleton site,
using lem-weil-pbc-singleton-site-module-comparison, or equivalently the
normalized ordinary-module lem-pod-projective-hom-evaluation-model.
4. P,F are R-K-flat. The augmentation calculation of
lem-sfb-flat-algebra-derived-module-tensor-exchange and
lem-pc-mixed-tensor-kflat-quasi-iso shows that the canonical scalar counits
for P,F are invertible for any T. No flatness of T is used.
5. Apply lem-trf-half-bounded-hom-scalar-isomorphism to S -> S tensor_R T.
Balancing gives the displayed formula. Applying Q and step 3 gives the
required derived isomorphism with ordinary termwise tensor on the left.
6. Degree-zero cycles are chain maps and boundaries are homotopies.
lem-pc-ring-derived-map-representative identifies these classes with derived
maps. The normalized formula sends h tensor 1 to the extended chain map;
naturality of the counit identifies this with derived scalar extension.
7. For a derived target map choose a finite-free source resolution and lower
truncate it below the support bounds of both targets. The maps descend to
that good truncation, giving a roof of bounded R-flat finitely presented
models. Its left arrow remains a quasi-isomorphism after tensoring, by
lem-pc-mixed-tensor-kflat-quasi-iso. Source maps have chain representatives.
The termwise formula commutes with composition and homotopy, so it descends
to all derived morphisms and is independent of model choices.
8. After extension F remains T-flat and finitely presented, P remains finite
free, and S_T remains flat and finitely presented over T. The same construction
therefore repeats. On pure tensors both direct and iterated comparisons
multiply the coefficients in the same order. The associator equation below
expresses this equality; identity extension is fixed by the same formula.
Zero rings, zero complexes and nonflat T are included throughout. -/
theorem relativeRhom_finiteFlat_baseChange_model
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (hflat : RingHom.Flat (algebraMap R S)) [Algebra.FinitePresentation R S]
    (K L : DerivedCategory (ModuleCat.{u} S))
    (hK : DerivedCategory.IsPseudoCoherent K)
    (hL : DerivedCategory.IsPseudoCoherent L)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ ∀ (N : ModuleCat.{u} R) (i : ℤ),
      i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((ModuleCat.restrictScalars (algebraMap R S)).mapDerivedCategory.obj L) ⊗
            DerivedCategory.Q.obj ((singleFunctor _ 0).obj N)))) :
    (∃ M : RelativeFiniteFlatHomModel R S,
      Nonempty (DerivedCategory.Q.obj M.P ≅ K) ∧
      Nonempty (DerivedCategory.Q.obj M.F ≅ L)) ∧
    (∀ M : RelativeFiniteFlatHomModels R S,
      (∃ a : ℤ, ∀ n : ℤ, n < a → IsZero ((moduleHomComplex M.P M.F).X n)) ∧
      (∀ n : ℤ, Module.Flat R
        ((ModuleCat.restrictScalars (algebraMap R S)).obj
          ((moduleHomComplex M.P M.F).X n)) ∧
        Module.FinitePresentation S ((moduleHomComplex M.P M.F).X n)) ∧
      (∀ n : ℤ, ∃ σ : (moduleHomComplex M.P M.F).X n ≃ₗ[S]
          DirectSum ℤ (fun i : ℤ ↦ M.P.X i →ₗ[S] M.F.X (i + n)),
        ∀ (h : (moduleHomComplex M.P M.F).X n) (i : ℤ),
          (σ h) i = (h.v i (i + n) rfl).hom)) ∧
    ∃ (H : RelativeFiniteFlatHomModels R S ⥤ DerivedCategory (ModuleCat.{u} S))
      (eH : ∀ M, H.obj M ≅ DerivedCategory.Q.obj (moduleHomComplex M.P M.F))
      (α : H ≅ relativeHomDerivedFunctorOriginal R S)
      (HT : ∀ (T : Type u) [CommRing T] [Algebra R T],
        RelativeFiniteFlatHomModels R S ⥤ DerivedCategory (ModuleCat.{u} (S ⊗[R] T)))
      (eT : ∀ (T : Type u) [CommRing T] [Algebra R T] (M : RelativeFiniteFlatHomModels R S),
        (HT T).obj M ≅ DerivedCategory.Q.obj
          ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj
            (moduleHomComplex M.P M.F)))
      (β : ∀ (T : Type u) [CommRing T] [Algebra R T],
        HT T ≅ relativeHomDerivedFunctor R S (S ⊗[R] T)
          (relativeHomCoefficientMap R S T))
      (χ : RelativeHomScalarComparisons R S)
      (ev : ∀ (A : Type u) [CommRing A]
        (P F : CochainComplex (ModuleCat.{u} A) ℤ), P ⊗ moduleHomComplex P F ⟶ F),
      (∀ (A : Type u) [CommRing A] (P F : CochainComplex (ModuleCat.{u} A) ℤ)
        (p n : ℤ) (x : P.X p) (h : (moduleHomComplex P F).X n),
        (ev A P F).f (p + n)
            (HomologicalComplex.ιTensorObj P (moduleHomComplex P F) p n (p + n) rfl
              (x ⊗ₜ[A] h)) =
          (p * n).negOnePow • (h.v p (p + n) rfl x)) ∧
      (∀ M : RelativeFiniteFlatHomModels R S,
        Functor.LaxMonoidal.μ DerivedCategory.Q M.P (moduleHomComplex M.P M.F) ≫
            DerivedCategory.Q.map (ev S M.P M.F) =
          DerivedCategory.Q.obj M.P ◁ ((eH M).inv ≫ α.hom.app M) ≫
            (ihom.ev (DerivedCategory.Q.obj M.P)).app (DerivedCategory.Q.obj M.F)) ∧
      (∀ (T : Type u) [CommRing T] [Algebra R T] (M : RelativeFiniteFlatHomModels R S),
        IsIso (relativeHomScalarCounit (relativeHomCoefficientMap R S T) M.P) ∧
        IsIso (relativeHomScalarCounit (relativeHomCoefficientMap R S T) M.F)) ∧
      (∀ (T : Type u) [CommRing T] [Algebra R T] (M : RelativeFiniteFlatHomModels R S) (n p q : ℤ)
        (hpq : p + n = q) (h : (moduleHomComplex M.P M.F).X n)
        (c d : S ⊗[R] T) (x : M.P.X p),
        (((χ T M).hom.f n (c ⊗ₜ[S,relativeHomCoefficientMap R S T] h)).v p q hpq)
            (d ⊗ₜ[S,relativeHomCoefficientMap R S T] x) =
          (c * d) ⊗ₜ[S,relativeHomCoefficientMap R S T] (h.v p q hpq x)) ∧
      (∀ (M M' : RelativeFiniteFlatHomModels R S) (a : M'.P ⟶ M.P)
        (b : M.F ⟶ M'.F),
        ∃ f : moduleHomComplex M.P M.F ⟶ moduleHomComplex M'.P M'.F,
          (∀ (n p q : ℤ) (hpq : p + n = q) (h : (moduleHomComplex M.P M.F).X n),
            (f.f n h).v p q hpq = a.f p ≫ h.v p q hpq ≫ b.f q) ∧
          H.map (InducedCategory.homMk
              ((DerivedCategory.Q.map a).op, DerivedCategory.Q.map b)) ≫ (eH M').hom =
            (eH M).hom ≫ DerivedCategory.Q.map f ∧
          ∀ (T : Type u) [CommRing T] [Algebra R T],
            (HT T).map (InducedCategory.homMk
                ((DerivedCategory.Q.map a).op, DerivedCategory.Q.map b)) ≫ (eT T M').hom =
              (eT T M).hom ≫ DerivedCategory.Q.map
                ((relativeHomExtend (relativeHomCoefficientMap R S T)).map f)) ∧
      (∀ (T : Type u) [CommRing T] [Algebra R T]
        (M : RelativeFiniteFlatHomModels R S) (n : ℤ)
        (h : (moduleHomComplex M.P M.F).X n),
        (χ T M).hom.f n
            ((1 : S ⊗[R] T) ⊗ₜ[S,relativeHomCoefficientMap R S T] h) =
          h.map (ModuleCat.extendScalars (relativeHomCoefficientMap R S T))) ∧
      (∀ (T : Type u) [CommRing T] [Algebra R T],
        ∃ ω :
          ((ModuleCat.restrictScalars (algebraMap R S) ⋙
            ModuleCat.extendScalars (algebraMap R T)).mapHomologicalComplex (.up ℤ)) ≅
          relativeHomExtend (relativeHomCoefficientMap R S T) ⋙
            Functor.mapHomologicalComplex
              (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom) (.up ℤ),
          ∀ (G : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) (t : T) (x : G.X i),
            (ω.hom.app G).f i (t ⊗ₜ[R,algebraMap R T] x) =
              ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T) t)
                ⊗ₜ[S,relativeHomCoefficientMap R S T] x) ∧
      (∀ M : RelativeFiniteFlatHomModels R S, ∃ θ : (moduleHomComplex M.P M.F).homology 0 ≃+
          (DerivedCategory.Q.obj M.P ⟶ DerivedCategory.Q.obj M.F),
        (∀ (f : M.P ⟶ M.F) (z : (moduleHomComplex M.P M.F).cycles 0),
          (moduleHomComplex M.P M.F).iCycles 0 z = HomComplex.Cochain.ofHom f →
          θ ((moduleHomComplex M.P M.F).homologyπ 0 z) = DerivedCategory.Q.map f) ∧
        ∀ (T : Type u) [CommRing T] [Algebra R T] (f : M.P ⟶ M.F),
          (ModuleCat.ordinaryDerivedExtendScalars (relativeHomCoefficientMap R S T)).map
              (DerivedCategory.Q.map f) ≫
              relativeHomScalarCounit (relativeHomCoefficientMap R S T) M.F =
            relativeHomScalarCounit (relativeHomCoefficientMap R S T) M.P ≫
              DerivedCategory.Q.map
                ((relativeHomExtend (relativeHomCoefficientMap R S T)).map f)) ∧
      (∀ (T : Type u) [CommRing T] [Algebra R T] (M : RelativeFiniteFlatHomModels R S),
        ∃ γ : DerivedCategory.Q.obj
            (moduleHomComplex
              ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.P)
              ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.F)) ≅
            (relativeHomDerivedFunctor R S (S ⊗[R] T)
              (relativeHomCoefficientMap R S T)).obj M,
          (eT T M).hom ≫ DerivedCategory.Q.map (χ T M).hom ≫ γ.hom =
            (β T).hom.app M ∧
          (relativeHomScalarCounit (relativeHomCoefficientMap R S T) M.P ▷
              DerivedCategory.Q.obj
                (moduleHomComplex
                  ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.P)
                  ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.F))) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q
              ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.P)
              (moduleHomComplex
                ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.P)
                ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.F)) ≫
            DerivedCategory.Q.map (ev (S ⊗[R] T)
              ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.P)
              ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.F)) =
          (ModuleCat.ordinaryDerivedExtendScalars
            (relativeHomCoefficientMap R S T)).obj (DerivedCategory.Q.obj M.P) ◁ γ.hom ≫
            (ihom.ev ((ModuleCat.ordinaryDerivedExtendScalars
              (relativeHomCoefficientMap R S T)).obj (DerivedCategory.Q.obj M.P))).app
                ((ModuleCat.ordinaryDerivedExtendScalars
                  (relativeHomCoefficientMap R S T)).obj (DerivedCategory.Q.obj M.F)) ≫
              relativeHomScalarCounit (relativeHomCoefficientMap R S T) M.F) ∧
      (∀ (T U : Type u) [CommRing T] [CommRing U] [Algebra R T] [Algebra R U]
        (v : T →ₐ[R] U) (M : RelativeFiniteFlatHomModels R S),
        ∃ τ : relativeHomExtend (relativeHomCoefficientMap R S U) ≅
            relativeHomExtend (relativeHomCoefficientMap R S T) ⋙
              relativeHomExtend (Algebra.TensorProduct.map (AlgHom.id R S) v).toRingHom,
          (∀ (G : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) (x : G.X i),
            (τ.hom.app G).f i
                ((1 : S ⊗[R] U) ⊗ₜ[S,relativeHomCoefficientMap R S U] x) =
              (1 : S ⊗[R] U) ⊗ₜ[S ⊗[R] T,
                (Algebra.TensorProduct.map (AlgHom.id R S) v).toRingHom]
                ((1 : S ⊗[R] T) ⊗ₜ[S,relativeHomCoefficientMap R S T] x)) ∧
          ∃ ξ :
            (relativeHomExtend
              (Algebra.TensorProduct.map (AlgHom.id R S) v).toRingHom).obj
                (moduleHomComplex
                  ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.P)
                  ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.F)) ≅
              moduleHomComplex
                ((relativeHomExtend (relativeHomCoefficientMap R S U)).obj M.P)
                ((relativeHomExtend (relativeHomCoefficientMap R S U)).obj M.F),
            (∀ (n p q : ℤ) (hpq : p + n = q)
              (z : (moduleHomComplex
                ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.P)
                ((relativeHomExtend (relativeHomCoefficientMap R S T)).obj M.F)).X n)
              (c : S ⊗[R] U),
              (ξ.hom.f n
                (c ⊗ₜ[S ⊗[R] T,
                  (Algebra.TensorProduct.map (AlgHom.id R S) v).toRingHom] z)).v p q hpq =
                (τ.hom.app M.P).f p ≫
                  (c • ((ModuleCat.extendScalars
                    (Algebra.TensorProduct.map (AlgHom.id R S) v).toRingHom).map
                      (z.v p q hpq))) ≫ (τ.inv.app M.F).f q) ∧
            (relativeHomExtend
              (Algebra.TensorProduct.map (AlgHom.id R S) v).toRingHom).map
                (χ T M).hom ≫ ξ.hom =
              (τ.inv.app (moduleHomComplex M.P M.F)) ≫ (χ U M).hom) := by
  sorry

end CochainComplex
