/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.TraceFormula.SpaceLineModuleProjInput

/-! # Relative section algebras and their canonical evaluation maps

Source: Stacks Project, Morphisms, Tag 01VJ(5); Constructions, Tag 01O9(2),(3)
(blueprint: def-sfb-relative-section-algebra-canonical-map).

These are the existing section-normalized definitions, extracted from the relative
ampleness theorem module. No existence or ampleness theorem is assumed here.
`GeneratesEverywhere` is the full positive-degree generation condition for this evaluation,
expressed by the rank-one stalk criterion when the module is invertible.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical graded section algebra, in the existing quasi-coherent affine-basis
presentation used by relative Proj. Its degree-n sections are exactly sections of L^n
on the inverse-image open, not a chosen unrelated algebra. These identifications determine
it up to the unique graded algebra isomorphism preserving sections.
Source: Stacks, Morphisms, Tag 01VJ(5)
(blueprint: def-sfb-relative-section-algebra-canonical-map). -/
structure RelativeSectionAlgebra {X T : Scheme.{u}} (f : X ⟶ T) (L : X.Modules) where
  data : T.GradedAlgebraData
  sectionEquiv (V : T.affineOpens) (n : ℕ) :
    data.grading V n ≃+ Γ(L.tensorPow n, f ⁻¹ᵁ V.1)
  smul (V : T.affineOpens) (n : ℕ) (r : Γ(T, V.1)) (a : data.grading V n) :
    sectionEquiv V n (r • a) = f.app V.1 r • sectionEquiv V n a
  one (V : T.affineOpens) :
    sectionEquiv V 0 ⟨1, SetLike.one_mem_graded (data.grading V)⟩ =
      unitSectionsEquiv (f ⁻¹ᵁ V.1) 1
  mul (V : T.affineOpens) (m n : ℕ) (a : data.grading V m) (b : data.grading V n) :
    sectionEquiv V (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V.1)
        (tmulSection (sectionEquiv V m a) (sectionEquiv V n b))
  restriction {V W : T.affineOpens} (h : V ≤ W) (n : ℕ) (a : data.grading W n) :
    sectionEquiv V n ⟨data.res h a, (data.res h).map_mem a.property⟩ =
      (L.tensorPow n).val.map (homOfLE (f.preimage_mono h)).op (sectionEquiv W n a)

/-- Evaluation of a homogeneous section on a trivializing scheme chart. The section map
is literally `1 ⊗ s`, followed by the existing tensor-power pullback comparison.
Source: Stacks, Morphisms, Tag 01VJ(5), adjunction map; Constructions, Tag 01O9
(blueprint: def-sfb-relative-section-algebra-canonical-map). -/
noncomputable def RelativeSectionAlgebra.evaluate {X T : Scheme.{u}} {f : X ⟶ T}
    {L : X.Modules} (A : RelativeSectionAlgebra f L) {W : Scheme.{u}} (j : W ⟶ X)
    (V : T.affineOpens) (h : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (f ⁻¹ᵁ V.1))
    (n : ℕ) (a : A.data.grading V n) :
    Γ(((tensorPullback j).obj L).tensorPow n, ⊤) :=
  (boundaryPullbackPowIso j L n).hom.app ⊤
    (((tensorPullback j).obj (L.tensorPow n)).val.map (homOfLE h).op
      (((tensorPullbackSectionAdjunction j).unit.app (L.tensorPow n)).app (f ⁻¹ᵁ V.1)
        (A.sectionEquiv V n a)))

/-- The assertion U(evaluation) = X: a positive-degree homogeneous section generates the
rank-one stalk at every point. Sections may be taken on any affine base neighbourhood.
Source: Stacks, Constructions, Tag 01O9, generation locus; Morphisms, Tag 01VJ(5)
(blueprint: def-sfb-relative-section-algebra-canonical-map). -/
def RelativeSectionAlgebra.GeneratesEverywhere {X T : Scheme.{u}} {f : X ⟶ T}
    {L : X.Modules} (A : RelativeSectionAlgebra f L) : Prop :=
  ∀ x : X, ∃ (V : T.affineOpens) (hx : x ∈ f ⁻¹ᵁ V.1) (n : ℕ), 0 < n ∧
    ∃ a : A.data.grading V n,
      (TopCat.Presheaf.germ (L.tensorPow n).val.presheaf (f ⁻¹ᵁ V.1) x hx)
          (A.sectionEquiv V n a) ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk (L.tensorPow n).val.presheaf x))

/-- The scheme specialization of the canonical chart formula in the recorded
`GradedLineMap.IsCanonicalMap`, for the evaluation map of the section algebra.
All trivializing open scheme charts are tested. The ring map is fixed on every
homogeneous section, including degree zero; the irrelevant-ideal condition is precisely
the hypothesis for the existing `Proj.fromOfGlobalSections` construction.
Source: Stacks, Constructions, Tag 01O9(2),(3); Morphisms, Tag 01VJ(5)
(blueprint: def-sfb-relative-section-algebra-canonical-map). -/
def RelativeSectionAlgebra.IsCanonicalMap {X T : Scheme.{u}} {f : X ⟶ T}
    {L : X.Modules} (A : RelativeSectionAlgebra f L) (r : X ⟶ A.data.relProj) : Prop :=
  r ≫ A.data.relProjHom = f ∧
    ∀ (W : Scheme.{u}) (j : W ⟶ X), IsOpenImmersion j →
      ∀ (V : T.affineOpens) (h : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (f ⁻¹ᵁ V.1))
        (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
        (α : A.data.obj V →+* Γ(W, ⊤)),
        (∀ (n : ℕ) (a : A.data.grading V n), α a =
          (unitSectionsEquiv ⊤).symm
            ((AlgebraicSpace.trivializedPower e n).hom.app ⊤ (A.evaluate j V h n a))) →
        ∀ hα : Ideal.map α (HomogeneousIdeal.irrelevant (A.data.grading V)).toIdeal = ⊤,
          j ≫ r = Proj.fromOfGlobalSections (A.data.grading V) α hα ≫ A.data.relProjι V

end AlgebraicGeometry.Scheme.Modules
