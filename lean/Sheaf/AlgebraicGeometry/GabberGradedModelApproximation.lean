module

public import Sheaf.AlgebraicGeometry.HigherGradedSheaf
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.Ideal

/-! # Gabber approximation preserves higher graded algebras

Source: ILO, Travaux de Gabber, Expose III, Definition 4.2 and Theorem 5.1,
pp.39--42 (blueprint: lem-per-gabber-graded-model-approximation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
namespace GabberGradedModel

/-- The canonical base-ring action on global sections of an S-scheme.
Source: ILO III section 2 (blueprint: lem-per-gabber-graded-model-approximation). -/
def sections {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- The later model is the specified model's base change along the inclusion.
Source: ILO III section 2 and Theorem 5.1
(blueprint: lem-per-gabber-graded-model-approximation). -/
def later {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {E : Type u} [Preorder E] (D : E → Subalgebra A B)
    (hD : Monotone D) (i j : E) (hij : i ≤ j)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of (D i))) : Scheme.{u} :=
  pullback f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hD hij)).toRingHom))

/-- The algebraic approximation obtained from the later model by the map u.
Source: ILO III section 2 and Theorem 5.1
(blueprint: lem-per-gabber-graded-model-approximation). -/
def approximation {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {E : Type u} [Preorder E] (D : E → Subalgebra A B)
    (hD : Monotone D) (i j : E) (hij : i ≤ j)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of (D i))) (v : D j →ₐ[A] A) : Scheme.{u} :=
  pullback (pullback.snd f₀ (Spec.map
    (CommRingCat.ofHom (Subalgebra.inclusion (hD hij)).toRingHom)))
    (Spec.map (CommRingCat.ofHom v.toRingHom))

/-- The structural morphism of the approximation to Spec A.
Source: ILO III section 2 (blueprint: lem-per-gabber-graded-model-approximation). -/
def approximationToBase {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {E : Type u} [Preorder E] (D : E → Subalgebra A B)
    (hD : Monotone D) (i j : E) (hij : i ≤ j)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of (D i))) (v : D j →ₐ[A] A) :
    approximation D hD i j hij f₀ v ⟶ Spec (.of A) :=
  pullback.snd _ (Spec.map (CommRingCat.ofHom v.toRingHom))

/-- The approximation's canonical projection to the original fixed model.
Source: ILO III section 2 (blueprint: lem-per-gabber-graded-model-approximation). -/
def approximationToModel {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {E : Type u} [Preorder E] (D : E → Subalgebra A B)
    (hD : Monotone D) (i j : E) (hij : i ≤ j)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of (D i))) (v : D j →ₐ[A] A) :
    approximation D hD i j hij f₀ v ⟶ X₀ :=
  pullback.fst _ (Spec.map (CommRingCat.ofHom v.toRingHom)) ≫ pullback.fst f₀ _

end GabberGradedModel

/-- Sufficiently close algebraic models have a unique extension of their canonical
thickening isomorphism to the higher graded algebra. `φ` is normalized by its
maps to the original model and to Spec A; these equations specify the canonical
base-change isomorphism, rather than allowing an arbitrary thickening isomorphism.
The pushforward form of the isomorphism is equivalent, by the inverse-image
adjunction for the homeomorphism φ, to the source's inverse-image form.

Source: ILO, Travaux de Gabber, Expose III, Definition 4.2 and Theorem 5.1,
pp.39--42 (blueprint: lem-per-gabber-graded-model-approximation).

Proof:
1. Completion modulo m^k is A/m^k by lem-weil-pbc-local-completion-quotient
   applied to the quotient; its nilpotent maximal ideal makes its completion itself.
   The kernels between these quotients identify all homogeneous pieces of G_a(A)
   and G_a(Ahat). Congruence and the pullback universal property give φ.
2. Choose a finite affine cover of the fixed finite-type model. Noetherianity and
   finite type imply finite presentation, by lem-weil-pbc-finite-type-algebra-noetherian
   and lem-weil-pbc-finite-type-noetherian-finite-presentation. Choose polynomial
   relation rows on these charts.
3. Over Ahat[t], the syzygy kernels are finite by
   lem-trf-noetherian-submodule-finitely-presented and completion Noetherianity
   lem-weil-pbc-adic-completion-noetherian. Choose finite relation matrices.
4. Enlarge the index to contain their finitely many coefficients. Injectivity of
   the subalgebras into Ahat makes PR=0 hold at every later stage and after u.
   Exactness at an intermediate stage is not asserted.
5. Apply lem-weil-pbc-artin-rees to the two image modules on each completed chart.
   Enlarge their finitely many bounds to c>=1 and take n0>=c, independently of u.
6. For N>=n0+1 apply lem-per-higher-graded-cokernel-perturbation with n=N-1.
   Congruence gives differences in m^N and PR=0 persists. This gives the higher
   graded algebra comparison of width N-c with the prescribed degree-zero map.
7. Completion modulo each power identifies the algebraic chart quotients with
   their completed counterparts. Kernels between successive quotients identify
   all graded pieces. By lem-weil-pbc-localization-quotient-commute and
   lem-weil-pbc-localization-module-exact these formulas respect restrictions.
8. G_a(T) is generated over G_a(A) by degree zero: for q>0 write elements of
   m^q O_T as sums of base elements times local sections; for -a<q<=0 use the
   base class of 1 in degree q, and for q<=-a the piece is zero. This proves
   uniqueness on all open restrictions.
9. The local comparisons agree on overlaps by step 8 and glue, as do their inverses.
   The common bounds work uniformly. For the empty model take i1=i0 and n0=c=1.
-/
theorem gabber_graded_model_approximation
    (A : Type u) [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    (hExcellent : IsExcellent A)
    (E : Type u) [Preorder E] [IsDirected E (· ≤ ·)]
    (D : E → Subalgebra A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hD : Monotone D) (hFinite : ∀ i : E, (D i).FG)
    (hUnion : ∀ b : AdicCompletion (IsLocalRing.maximalIdeal A) A, ∃ i : E, b ∈ D i)
    (i₀ : E) (X₀ X : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of (D i₀)))
    [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (f : X ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (model : X ≅ pullback f₀ (Spec.map (CommRingCat.ofHom (D i₀).val.toRingHom)))
    (hModel : model.hom ≫ pullback.snd f₀ _ = f) :
    ∃ (i₁ : E) (hi₀ : i₀ ≤ i₁) (n₀ c : ℕ), 1 ≤ c ∧ c ≤ n₀ ∧
      ∀ (i : E) (hi : i₁ ≤ i) (N : ℕ), n₀ + 1 ≤ N →
        ∀ v : D i →ₐ[A] A,
          (∀ b : D i, algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (v b) -
            (b : AdicCompletion (IsLocalRing.maximalIdeal A) A) ∈
              ((IsLocalRing.maximalIdeal A) ^ N).map
                (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) →
          ∃ φ : (Scheme.IdealSheafData.ofIdealTop
              ((IsLocalRing.maximalIdeal A).map
                (GabberGradedModel.sections (f ≫ Spec.map (CommRingCat.ofHom
                  (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))))) ^
                (N - c)).subscheme ≅
            (Scheme.IdealSheafData.ofIdealTop
              ((IsLocalRing.maximalIdeal A).map
                (GabberGradedModel.sections (GabberGradedModel.approximationToBase
                  D hD i₀ i (le_trans hi₀ hi) f₀ v))) ^ (N - c)).subscheme,
            (φ.hom ≫ (Scheme.IdealSheafData.ofIdealTop
                ((IsLocalRing.maximalIdeal A).map
                  (GabberGradedModel.sections (GabberGradedModel.approximationToBase
                    D hD i₀ i (le_trans hi₀ hi) f₀ v))) ^ (N - c)).subschemeι ≫
                GabberGradedModel.approximationToModel
                  D hD i₀ i (le_trans hi₀ hi) f₀ v =
              (Scheme.IdealSheafData.ofIdealTop
                ((IsLocalRing.maximalIdeal A).map
                  (GabberGradedModel.sections (f ≫ Spec.map (CommRingCat.ofHom
                    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))))) ^
                      (N - c)).subschemeι ≫ model.hom ≫ pullback.fst f₀ _) ∧
            (φ.hom ≫ (Scheme.IdealSheafData.ofIdealTop
                ((IsLocalRing.maximalIdeal A).map
                  (GabberGradedModel.sections (GabberGradedModel.approximationToBase
                    D hD i₀ i (le_trans hi₀ hi) f₀ v))) ^ (N - c)).subschemeι ≫
                GabberGradedModel.approximationToBase
                  D hD i₀ i (le_trans hi₀ hi) f₀ v =
              (Scheme.IdealSheafData.ofIdealTop
                ((IsLocalRing.maximalIdeal A).map
                  (GabberGradedModel.sections (f ≫ Spec.map (CommRingCat.ofHom
                    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))))) ^
                      (N - c)).subschemeι ≫ f ≫ Spec.map (CommRingCat.ofHom
                (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) ∧
            ∃! e : HigherGraded.sheaf (IsLocalRing.maximalIdeal A)
                (GabberGradedModel.approximation D hD i₀ i (le_trans hi₀ hi) f₀ v)
                (GabberGradedModel.sections (GabberGradedModel.approximationToBase
                  D hD i₀ i (le_trans hi₀ hi) f₀ v)) (N - c) ≅
              (TopCat.Sheaf.pushforward CommRingCat φ.hom.base).obj
                (HigherGraded.sheaf (IsLocalRing.maximalIdeal A) X
                  (GabberGradedModel.sections (f ≫ Spec.map (CommRingCat.ofHom
                    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))) (N - c)),
              HigherGraded.IsExtension _ _ _ _ (N - c) φ e := by
  sorry

end AlgebraicGeometry
