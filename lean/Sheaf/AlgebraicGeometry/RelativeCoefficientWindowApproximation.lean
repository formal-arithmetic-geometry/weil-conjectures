module

public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finite-window coefficient approximation

Source: the agent-formulated two-open prerequisite for the unnumbered Kiehl assertion
following Stacks Project, perfect.tex, Tag 0CSD. This is not a theorem stated by that tag;
the primary Kiehl descente source is WANTED.
(blueprint: def-sfb-relative-coefficient-window-approximation).

The helpers expand the proposition and its prescribed scalar-action normalization.
The coefficient maps are arbitrary; no flatness is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace AlgebraicGeometry

noncomputable section

/-- The projection between the actual coefficient base changes of the same scheme.
Source: the two-open prerequisite after Stacks 0CSD
(blueprint: def-sfb-relative-coefficient-window-approximation). -/
def coefficientWindowProjection {B A E : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec B) (b : B ⟶ A) (d : B ⟶ E) (e : E ⟶ A) (h : d ≫ e = b) :
    pullback f (Spec.map b) ⟶ pullback f (Spec.map d) :=
  pullback.map f (Spec.map b) f (Spec.map d) (𝟙 X) (Spec.map e) (𝟙 (Spec B))
    (Category.comp_id f |>.trans (Category.id_comp f).symm)
    ((Category.comp_id _).trans
      ((congrArg Spec.map h).symm.trans (Spec.map_comp d e)))

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The coefficient object is the associated module A in degree zero, with E acting
through the specified map. Source: the two-open prerequisite after Stacks 0CSD
(blueprint: def-sfb-relative-coefficient-window-approximation). -/
def coefficientWindowModule {E A : CommRingCat.{u}} (e : E ⟶ A) :
    schemeDerivedCategory (Spec E) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (tilde ((ModuleCat.restrictScalars e.hom).obj (ModuleCat.of A A)))

/-- Multiplication A tensor_E A to A, associated to Spec A. It is the counit of
extension/restriction of scalars, so sends a tensor b to ab.
Source: the given A-structure in the two-open prerequisite after Stacks 0CSD
(blueprint: def-sfb-relative-coefficient-window-approximation). -/
def coefficientWindowMultiplication {E A : CommRingCat.{u}} (e : E ⟶ A) :
    (Scheme.Modules.pullback (Spec.map e)).obj
      (tilde ((ModuleCat.restrictScalars e.hom).obj (ModuleCat.of A A))) ⟶
        SheafOfModules.unit (Spec A).ringCatSheaf :=
  (Scheme.Modules.tildePullbackIso e).hom.app _ ≫
    tilde.map ((ModuleCat.extendRestrictScalarsAdj e.hom).counit.app (ModuleCat.of A A)) ≫
      (tildeSelf (R := A)).hom

/-- The scalar-action map on the source of the coefficient projection, built from
the pinned composition of pullbacks across the square, their single-module
comparison, and multiplication.
Source: the transpose specified in the two-open prerequisite after Stacks 0CSD
(blueprint: def-sfb-relative-coefficient-window-approximation). -/
def coefficientWindowScalar {E A : CommRingCat.{u}} {Z T : Scheme.{u}}
    (q : T ⟶ Spec E) (r : Z ⟶ Spec A) (π : Z ⟶ T) (e : E ⟶ A)
    (h : π ≫ q = r ≫ Spec.map e) :
    (derivedPullback π).obj ((derivedPullback q).obj (coefficientWindowModule e)) ⟶
      𝟙_ (schemeDerivedCategory Z) :=
  (canonicalDerivedPullbackComposition π q).hom.app (coefficientWindowModule e) ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj (coefficientWindowModule e)) h) ≫
    (canonicalDerivedPullbackComposition r (Spec.map e)).inv.app (coefficientWindowModule e) ≫
    (derivedPullback r).map
      (Scheme.Modules.canonicalSinglePullbackMap (Spec.map e) _ ≫
        (DerivedCategory.singleFunctor _ 0).map (coefficientWindowMultiplication e)) ≫
    Scheme.Modules.canonicalSinglePullbackMap r (SheafOfModules.unit (Spec A).ringCatSheaf) ≫
    (DerivedCategory.singleFunctor _ 0).map
      (SheafOfModules.pullbackObjUnitToUnit r.toRingCatSheafHom)

/-- The normalized coefficient morphism is the adjoint transpose of scalar
multiplication tensored with the transpose of gamma. The tensor comparison is the
existing uniquely characterized K-flat comparison, not an arbitrary monoidal map.
Source: the displayed theta in the two-open prerequisite after Stacks 0CSD
(blueprint: def-sfb-relative-coefficient-window-approximation). -/
def coefficientWindowTheta {E A : CommRingCat.{u}} {Z T : Scheme.{u}}
    (q : T ⟶ Spec E) (r : Z ⟶ Spec A) (π : Z ⟶ T) (e : E ⟶ A)
    (h : π ≫ q = r ≫ Spec.map e) (F : schemeDerivedCategory T)
    (K : schemeDerivedCategory Z) (γ : F ⟶ (schemeDerivedDirectImage π).obj K) :
    (derivedPullback q).obj (coefficientWindowModule e) ⊗ F ⟶
      (schemeDerivedDirectImage π).obj K :=
  (canonicalSchemeDerivedAdjunction π).homEquiv _ _
    ((Classical.choose (exists_canonicalPullbackTensorComparison π)) _ _ ≫
      (coefficientWindowScalar q r π e h ⊗ₘ
        ((canonicalSchemeDerivedAdjunction π).homEquiv F K).symm γ) ≫ (λ_ K).hom)

/-- The proposition P(W), expressed for its structure morphism f. Every finite type
coefficient stage D and compatible D to A, every relatively pseudo-coherent QCoh K,
and every integer a admit a finite type refinement E and a bounded coherent F.
The cone of the prescribed theta is QCoh and vanishes in all degrees at least a.
Source: the definition of P in the two-open prerequisite after Stacks 0CSD
(blueprint: def-sfb-relative-coefficient-window-approximation). -/
def HasRelativeCoefficientWindowApproximation {B A : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec B) [LocallyOfFiniteType f] (b : B ⟶ A) : Prop :=
  ∀ (D : CommRingCat.{u}) (d : B ⟶ D), d.hom.FiniteType →
    ∀ (t : D ⟶ A), d ≫ t = b →
    ∀ K : schemeDerivedCategory (pullback f (Spec.map b)),
      schemeDerivedQCohProperty _ K →
      Scheme.IsPseudoCoherentRelativeTo (pullback.snd f (Spec.map b)) K →
      ∀ a : ℤ, ∃ (E : CommRingCat.{u}) (s : D ⟶ E), s.hom.FiniteType ∧
        ∃ (e : E ⟶ A) (h : (d ≫ s) ≫ e = b), s ≫ e = t ∧
          ∃ F : schemeDerivedCategory (pullback f (Spec.map (d ≫ s))),
            (∃ l v : ℤ, ∀ i : ℤ, i < l ∨ v < i →
              IsZero ((DerivedCategory.homologyFunctor _ i).obj F)) ∧
            (∀ i : ℤ, RingedSpace.IsCoherent _
              ((DerivedCategory.homologyFunctor _ i).obj F)) ∧
            ∃ γ : F ⟶ (schemeDerivedDirectImage
              (coefficientWindowProjection f b (d ≫ s) e h)).obj K,
              ∃ (C : schemeDerivedCategory (pullback f (Spec.map (d ≫ s))))
                (j : (schemeDerivedDirectImage
                  (coefficientWindowProjection f b (d ≫ s) e h)).obj K ⟶ C)
                (δ : C ⟶ ((derivedPullback (pullback.snd f (Spec.map (d ≫ s)))).obj
                  (coefficientWindowModule e) ⊗ F)⟦(1 : ℤ)⟧),
                Triangle.mk
                  (coefficientWindowTheta (pullback.snd f (Spec.map (d ≫ s)))
                    (pullback.snd f (Spec.map b))
                    (coefficientWindowProjection f b (d ≫ s) e h) e
                    (pullback.lift_snd _ _ _) F K γ) j δ ∈
                    distTriang (schemeDerivedCategory (pullback f (Spec.map (d ≫ s)))) ∧
                schemeDerivedQCohProperty _ C ∧
                ∀ i : ℤ, a ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj C)

end

end AlgebraicGeometry
