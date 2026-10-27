/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Sheaf.Algebra.Homology.OneKFlatChainTranspose
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.HomComplexMappingCone
import Sheaf.Algebra.Homology.RingedHomCompositionModel
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-! # Projective representatives of canonical biduality

Source: Stacks Project, more-algebra.tex Tag 0A66; sites-cohomology.tex Tag 0A97;
sites.tex Tag 00X9 (blueprint: lem-trf-projective-bidual-representative-comparison).
The punctual-site transport includes the actual Hom projections, augmentation maps,
evaluations and Koszul transpose. All derived localizations have coefficient universe u.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CochainComplex
open scoped TensorProduct

namespace CategoryTheory.ProjectiveBidualRepresentative

variable (B : Type u) [CommRing B]

/-- Termwise evaluation, using the existing punctual-site functor.
Source: Stacks 00X9 (blueprint: lem-trf-projective-bidual-representative-comparison). -/
abbrev evaluation := (singletonEvaluation B).mapHomologicalComplex (.up ℤ)

/-- The existing constant inverse is additive, component by component.
Source: Stacks 00X9 (blueprint: lem-trf-projective-bidual-representative-comparison). -/
instance constantAdditive : (singletonConstantModuleSheaf B).Additive where
  map_add := rfl

/-- Termwise constant inverse, using the existing punctual-site construction.
Source: Stacks 00X9 (blueprint: lem-trf-projective-bidual-representative-comparison). -/
abbrev constant := (singletonConstantModuleSheaf B).mapHomologicalComplex (.up ℤ)

/-- Grothendieck abelianness in the coefficient universe, from the recorded site theorem.
Source: Stacks 079P (blueprint: lem-trf-projective-bidual-representative-comparison). -/
instance sheafGrothendieck : IsGrothendieckAbelian.{u} (singletonModuleCategory B) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{0, 0, u}
    singletonTopology (singletonRingSheaf B)).1

/-- The Koszul braiding descended from cochain complexes, with no arbitrary braiding binder.
Source: Stacks 0FPT (blueprint: lem-trf-projective-bidual-representative-comparison). -/
@[instance_reducible]
def koszulBraiding : BraidedCategory (DerivedCategory (ModuleCat.{u} B)) :=
  DerivedMonoidal.braidedCategory' DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} B) (.up ℤ))

attribute [local instance] koszulBraiding

/-- The coefficient complex B[0].
Source: Stacks 0A66 (blueprint: lem-trf-projective-bidual-representative-comparison). -/
abbrev coefficient :=
  (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)

/-- Product total sheaf Hom, retaining the recorded construction and differential.
Source: Stacks 0A8X (blueprint: lem-trf-projective-bidual-representative-comparison). -/
abbrev sheafHom (E F : CochainComplex (singletonModuleCategory B) ℤ) :=
  homComplex.{0, 0, u, u} (R := singletonRingSheaf B) E F

/-- The fixed sheaf K-injective resolution, transported by the actual constant/evaluation pair.
Source: Stacks 079P (blueprint: lem-trf-projective-bidual-representative-comparison). -/
abbrev resolution := constant B ⋙
  WeilConjectures.coefficientHomResolution.{u, 0, 0}
    singletonTopology (singletonRingSheaf B) ⋙ evaluation B

/-- The transported augmentation, without changing the fixed resolution map.
Source: Stacks 079P (blueprint: lem-trf-projective-bidual-representative-comparison). -/
def augmentation (S : CochainComplex (ModuleCat.{u} B) ℤ) : S ⟶ (resolution B).obj S :=
  (evaluation B).map ((ringedSiteHomAugmentation.{0, 0, u}
    singletonTopology (singletonRingSheaf B)).app ((constant B).obj S))

/-- The Hom comparison is the transpose of localized signed ordinary evaluation.
The augmentation square in the theorem below identifies it with the fixed resolution comparison.
Source: Stacks 0A66, 0A97
(blueprint: lem-trf-projective-bidual-representative-comparison). -/
def comparison
    (ev : ∀ (P N : CochainComplex (ModuleCat.{u} B) ℤ),
      P ⊗ moduleHomComplex P N ⟶ N)
    (P N : CochainComplex (ModuleCat.{u} B) ℤ) :
    DerivedCategory.Q.obj (moduleHomComplex P N) ⟶
      (ihom (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N) :=
  MonoidalClosed.curry
    (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N) ≫
      DerivedCategory.Q.map (ev P N))

/-- The canonical coefficient bidual map of the recorded ordinary derived Hom.
Its braiding is the actual descended Koszul braiding specified above.
Source: Stacks 0A97 (blueprint: lem-trf-projective-bidual-representative-comparison). -/
def bidual (V : DerivedCategory (ModuleCat.{u} B)) :=
  MonoidalClosed.toIhomIhom (DerivedCategory.Q.obj (coefficient B)) V

/-- Exact, localized Hom and duality transport from the punctual site.
All comparisons are required to commute with the recorded ordinary-to-derived comparison;
the evaluated Hom isomorphism is specified on every product coordinate.
Source: Stacks 00X9, 0A66, 0A97
(blueprint: lem-trf-projective-bidual-representative-comparison). -/
def Transport
    (ev : ∀ (P N : CochainComplex (ModuleCat.{u} B) ℤ),
      P ⊗ moduleHomComplex P N ⟶ N) : Prop :=
  (∃ e : singletonModuleCategory B ≌ ModuleCat.{u} B,
    e.functor = singletonEvaluation B ∧ e.inverse = singletonConstantModuleSheaf B ∧
      ∀ T : ShortComplex (singletonModuleCategory B), T.ShortExact →
        (T.map e.functor).ShortExact) ∧
  (∀ E : CochainComplex (singletonModuleCategory B) ℤ,
    E.IsKInjective ↔ CochainComplex.IsKInjective ((evaluation B).obj E)) ∧
  (∀ E : CochainComplex (ModuleCat.{u} B) ℤ,
    E.IsKInjective ↔ CochainComplex.IsKInjective ((constant B).obj E)) ∧
  (∀ E : CochainComplex (singletonModuleCategory B) ℤ,
    QuasiIso ((evaluation B).map
      ((ringedSiteHomAugmentation.{0, 0, u} singletonTopology (singletonRingSheaf B)).app E)) ∧
    CochainComplex.IsKInjective ((evaluation B).obj
      ((WeilConjectures.coefficientHomResolution.{u, 0, 0}
        singletonTopology (singletonRingSheaf B)).obj E))) ∧
  ∃ d : DerivedCategory.{u} (singletonModuleCategory B) ≌
      DerivedCategory.{u} (ModuleCat.{u} B),
    ∃ k : DerivedCategory.Q ⋙ d.functor ≅ evaluation B ⋙ DerivedCategory.Q,
      ∃ χ : ∀ (E F : CochainComplex (singletonModuleCategory B) ℤ),
          (evaluation B).obj (sheafHom B E F) ≅
            moduleHomComplex ((evaluation B).obj E) ((evaluation B).obj F),
        (∀ (E F : CochainComplex (singletonModuleCategory B) ℤ)
          (n p q : ℤ) (h : p + n = q)
          (z : ((evaluation B).obj (sheafHom B E F)).X n)
          (x : ((evaluation B).obj E).X p),
          (((χ E F).hom.f n z).v p q h) x =
            (((WeilConjectures.coefficientHomComponent.{u, 0, 0}
              singletonTopology (singletonRingSheaf B) E F n p q h).val.app
                (op (⟨PUnit.unit⟩ : singletonSite)) z).app
                  (op (Over.mk (𝟙 (⟨PUnit.unit⟩ : singletonSite))))).hom x) ∧
        ∃ ρ : ∀ V W : DerivedCategory.{u} (singletonModuleCategory B),
            d.functor.obj ((derivedInternalHomOfUniverses.{0, 0, u, u}
              singletonTopology (singletonRingSheaf B)).obj (op V, W)) ≅
                (ihom (d.functor.obj V)).obj (d.functor.obj W),
          (∀ (V V' W W' : DerivedCategory.{u} (singletonModuleCategory B))
            (f : V' ⟶ V) (g : W ⟶ W'),
            d.functor.map ((derivedInternalHomOfUniverses.{0, 0, u, u}
              singletonTopology (singletonRingSheaf B)).map (f.op, g)) ≫ (ρ V' W').hom =
              (ρ V W).hom ≫ (MonoidalClosed.pre (d.functor.map f)).app (d.functor.obj W) ≫
                (ihom (d.functor.obj V')).map (d.functor.map g)) ∧
          (∀ E F : CochainComplex (singletonModuleCategory B) ℤ,
            d.functor.map (ringedSiteOrdinaryHomComparison.{0, 0, u, u}
              singletonTopology (singletonRingSheaf B) E F) ≫
                (ρ (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F)).hom ≫
                (MonoidalClosed.pre (k.app E).inv).app
                  (d.functor.obj (DerivedCategory.Q.obj F)) ≫
                (ihom (DerivedCategory.Q.obj ((evaluation B).obj E))).map (k.app F).hom =
              (k.app (sheafHom B E F)).hom ≫ DerivedCategory.Q.map (χ E F).hom ≫
                comparison B ev ((evaluation B).obj E) ((evaluation B).obj F)) ∧
          ∃ M : RingedSiteDualityModel.{0, 0, u, u}
              singletonTopology (singletonRingSheaf B),
            ∃ τ : ∀ V W : DerivedCategory.{u} (singletonModuleCategory B),
                d.functor.obj (M.closed.tensor.obj (V, W)) ≅
                  d.functor.obj V ⊗ d.functor.obj W,
              (∀ (V V' W W' : DerivedCategory.{u} (singletonModuleCategory B))
                (f : V ⟶ V') (g : W ⟶ W'),
                d.functor.map (M.closed.tensor.map (f, g)) ≫ (τ V' W').hom =
                  (τ V W).hom ≫ (d.functor.map f ⊗ₘ d.functor.map g)) ∧
              (∀ V W : DerivedCategory.{u} (singletonModuleCategory B),
                d.functor.map (M.closed.evaluation V W) =
                  (τ _ V).hom ≫ ((ρ V W).hom ▷ d.functor.obj V) ≫
                    (β_ _ (d.functor.obj V)).hom ≫
                      (ihom.ev (d.functor.obj V)).app (d.functor.obj W)) ∧
              (∀ V W : DerivedCategory.{u} (singletonModuleCategory B),
                d.functor.map (M.symmetric.braiding V W).hom ≫ (τ W V).hom =
                  (τ V W).hom ≫ (β_ (d.functor.obj V) (d.functor.obj W)).hom) ∧
              (∀ (A V W : DerivedCategory.{u} (singletonModuleCategory B))
                (f : M.closed.tensor.obj (A, V) ⟶ W),
                d.functor.map (M.closed.transpose A V W f) ≫ (ρ V W).hom =
                  MonoidalClosed.curry
                    ((β_ (d.functor.obj V) (d.functor.obj A)).hom ≫
                      (τ A V).inv ≫ d.functor.map f)) ∧
              (∀ V W : DerivedCategory.{u} (singletonModuleCategory B),
                d.functor.map (ringedSiteBidual M.closed M.symmetric W V) ≫
                  (ρ ((derivedInternalHomOfUniverses.{0, 0, u, u}
                    singletonTopology (singletonRingSheaf B)).obj (op V, W)) W).hom ≫
                  (MonoidalClosed.pre (ρ V W).inv).app (d.functor.obj W) =
                MonoidalClosed.toIhomIhom (d.functor.obj W) (d.functor.obj V))

/-- The exact statement, with every representative map pinned by its homogeneous formula.
The Hom differential is the imported product Hom differential. The comparison is defined
above by actual localized evaluation and is required to satisfy the fixed augmentation square.
Source: Stacks 0A66, 0A97, 00X9
(blueprint: lem-trf-projective-bidual-representative-comparison). -/
def Statement : Prop :=
  ∃ H : ∀ {P P' N N' : CochainComplex (ModuleCat.{u} B) ℤ},
      (P' ⟶ P) → (N ⟶ N') → (moduleHomComplex P N ⟶ moduleHomComplex P' N'),
    ∃ ev : ∀ (P N : CochainComplex (ModuleCat.{u} B) ℤ),
        P ⊗ moduleHomComplex P N ⟶ N,
      (∀ (P P' N N' : CochainComplex (ModuleCat.{u} B) ℤ)
        (a : P' ⟶ P) (b : N ⟶ N') (n p q : ℤ) (h : p + n = q)
        (z : (moduleHomComplex P N).X n),
        ((H a b).f n z).v p q h = a.f p ≫ z.v p q h ≫ b.f q) ∧
      (∀ (P N : CochainComplex (ModuleCat.{u} B) ℤ) (p q : ℤ)
        (x : P.X p) (z : (moduleHomComplex P N).X q),
        (ev P N).f (p + q)
          (HomologicalComplex.ιTensorObj P (moduleHomComplex P N) p q (p + q) rfl
            (x ⊗ₜ[B] z)) = (p * q).negOnePow • (z.v p (p + q) rfl) x) ∧
      Transport B ev ∧
      (∀ S : CochainComplex (ModuleCat.{u} B) ℤ,
        QuasiIso (augmentation B S) ∧ CochainComplex.IsKInjective ((resolution B).obj S)) ∧
      (∀ S : CochainComplex (ModuleCat.{u} B) ℤ,
        IsIso (comparison B ev S ((resolution B).obj (coefficient B))) ∧
        comparison B ev S (coefficient B) ≫
            (ihom (DerivedCategory.Q.obj S)).map
              (DerivedCategory.Q.map (augmentation B (coefficient B))) =
          DerivedCategory.Q.map (H (𝟙 S) (augmentation B (coefficient B))) ≫
            comparison B ev S ((resolution B).obj (coefficient B))) ∧
      (∀ (S S' : CochainComplex (ModuleCat.{u} B) ℤ) (f : S ⟶ S'),
        DerivedCategory.Q.map (H f (𝟙 (coefficient B))) ≫
            comparison B ev S (coefficient B) =
          comparison B ev S' (coefficient B) ≫
            (MonoidalClosed.pre (DerivedCategory.Q.map f)).app
              (DerivedCategory.Q.obj (coefficient B))) ∧
      ∃ δ : ∀ T : CochainComplex (ModuleCat.{u} B) ℤ,
          T ⟶ moduleHomComplex (moduleHomComplex T (coefficient B)) (coefficient B),
        (∀ (T : CochainComplex (ModuleCat.{u} B) ℤ) (p q : ℤ)
          (x : T.X p) (φ : (moduleHomComplex T (coefficient B)).X q),
          (((δ T).f p x).v q (q + p) rfl) φ =
            (p * q).negOnePow • (φ.v p (q + p) (add_comm p q)) x) ∧
        (∀ (T : CochainComplex (ModuleCat.{u} B) ℤ) (p q : ℤ)
          (_h : q + p ≠ 0) (x : T.X p),
          ((δ T).f p x).v q (q + p) rfl = 0) ∧
        (∀ T : CochainComplex (ModuleCat.{u} B) ℤ,
          (∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (T.X i)) →
          (∀ i : ℤ, Module.Projective B (T.X i)) →
          (∃ n : ℤ, ∀ i : ℤ, n < i →
            IsZero ((moduleHomComplex T (coefficient B)).X i)) →
          (∀ i : ℤ, Module.Projective B ((moduleHomComplex T (coefficient B)).X i)) →
          QuasiIso (H (𝟙 T) (augmentation B (coefficient B))) ∧
          QuasiIso (H (𝟙 (moduleHomComplex T (coefficient B)))
            (augmentation B (coefficient B))) ∧
          IsIso (comparison B ev T (coefficient B)) ∧
          IsIso (comparison B ev (moduleHomComplex T (coefficient B)) (coefficient B)) ∧
          bidual B (DerivedCategory.Q.obj T) ≫
              (MonoidalClosed.pre (comparison B ev T (coefficient B))).app
                (DerivedCategory.Q.obj (coefficient B)) =
            DerivedCategory.Q.map (δ T) ≫
              comparison B ev (moduleHomComplex T (coefficient B)) (coefficient B)) ∧
        (∀ (V W : DerivedCategory.{u} (ModuleCat.{u} B)) (e : V ⟶ W),
          e ≫ bidual B W = bidual B V ≫
            (MonoidalClosed.pre
              ((MonoidalClosed.pre e).app (DerivedCategory.Q.obj (coefficient B)))).app
                (DerivedCategory.Q.obj (coefficient B)))

/-- Canonical biduality on bounded-above projective representatives.
Source: Stacks Project, more-algebra.tex Tag 0A66 (lemma-RHom-out-of-projective),
sites-cohomology.tex Tag 0A97 (lemma-internal-hom-evaluate), sites.tex Tag 00X9.
(blueprint: lem-trf-projective-bidual-representative-comparison).

Proof:
1. Evaluate sheaves on the punctual site and use the constant inverse. Both functors
are exact, hence induce localization-compatible ordinary derived equivalences in u.
2. The slice site is again punctual. The sheaf-Hom projections are the module linear
maps, so products, their differential, precomposition and postcomposition agree.
Chain maps and null-homotopies transport componentwise; this preserves and reflects
K-injectivity. Keep the actual image of the fixed augmentation.
3. Compute derived Hom using these transported K-injective targets. Their comparison
with the imported ordinary derived closed Hom is pinned by localized signed evaluation.
Thus the Hom comparison square commutes. The tensor adjunction transports evaluation
and its Koszul transpose, giving the last three clauses of Transport.
4. Bounded-above projective S is K-projective. The cone of the fixed augmentation is
acyclic, its Hom out of S is acyclic, and Hom commutes with that cone. Therefore the
actual Hom augmentation is a quasi-isomorphism, for both T and its ordinary dual D.
5. The fixed-resolution comparison is the localized Hom augmentation followed by the
inverse resolution factorization. The augmentation square displayed in Statement is
this equality after composing with the invertible derived augmentation. Precomposition
commutes with postcomposition by the augmentation, proving comparison naturality.
6. Apply the signed representative normalization of lem-sfb-ringed-site-duality-maps
on the punctual site and transport it through the comparisons of steps 2 and 3.
It identifies delta with x ↦ (phi ↦ (-1)^(|x||phi|) phi(x)); nonzero output degrees
vanish since B[0] is zero there. It gives precisely the displayed comparison equation.
Naturality of the coefficient transpose applies to every derived morphism. No step
uses finite generation or asserts that the bidual map is invertible. -/
theorem projective_bidual_representative_comparison : Statement B := by
  sorry

end CategoryTheory.ProjectiveBidualRepresentative
