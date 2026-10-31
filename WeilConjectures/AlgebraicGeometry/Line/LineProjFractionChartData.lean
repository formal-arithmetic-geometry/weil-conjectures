/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProjAlgebra.RelativeProjAffineRestriction
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Homogeneous-fraction charts for a graded map into a line module

Source: Stacks Project, Constructions, Tags 01NK and 01O9, local construction and
affine-base gluing (blueprint: lem-trf-line-proj-affine-chart-atlas).

The input maps are maps of the actual tensor-pullback homogeneous sheaves. The unit
and multiplication equations on pulled-back sections express the graded algebra law.
The chart opens are specified by their stalkwise free-generator condition. Fractions
are specified without division: the scalar times the denominator section is the numerator.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The image of a homogeneous section under the given tensor-pullback map.
Source: Stacks, Tag 01O9 (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjImage {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.Opens) (n : ℕ) (a : Γ(A.piece n, V)) : Γ(L.tensorPow n, f ⁻¹ᵁ V) :=
  (ψ n).app (f ⁻¹ᵁ V) (tensorPullbackSection f (A.piece n) V a)

/-- The inclusion of a homogeneous section into the actual affine section ring.
Source: Stacks, Tags 01NK and 01O9 (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjElement {T : Scheme.{u}} (A : RelativeProjAlgebra T)
    (V : T.affineOpens) (n : ℕ) (a : Γ(A.piece n, V.1)) : A.grade V n :=
  ⟨(Sigma.ι A.piece n ≫ A.decomposition.hom).app V.1 a, ⟨a, rfl⟩⟩

/-- Tensor powers of a local frame, including the degree-zero unit section.
Source: Stacks, Tag 01NK (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjFramePower {W : Scheme.{u}} (L : W.Modules) (U : W.Opens)
    (e : Γ(L, U)) : (n : ℕ) → Γ(L.tensorPow n, U)
  | 0 => unitSectionsEquiv U 1
  | n + 1 => tmulSection e (lineProjFramePower L U e n)

/-- The m-th power of a degree-d section, transported to degree m*d.
Source: Stacks, Tag 01NK (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjPower {W : Scheme.{u}} (L : W.Modules) (U : W.Opens)
    (d : ℕ) (s : Γ(L.tensorPow d, U)) (m : ℕ) : Γ(L.tensorPow (m • d), U) :=
  (eqToHom (congrArg L.tensorPow (Nat.mul_comm d m))).app U
    ((L.tensorPowMulIso d m).inv.app U
      (lineProjFramePower (L.tensorPow d) U s m))

/-- The chart open is the existing generating locus on the inverse-image open scheme,
viewed as an open of W. The intersection makes its ambient inclusion explicit.
Source: Stacks, Tags 01CY and 01O9 (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjGeneratorOpen {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1)) : W.Opens :=
  (f ⁻¹ᵁ V.1) ⊓ (f ⁻¹ᵁ V.1).ι ''ᵁ
    generatingLocus
      (((L.tensorPow d).restrictAppIso (f ⁻¹ᵁ V.1).ι ⊤).inv
        ((L.tensorPow d).presheaf.map (eqToHom (f ⁻¹ᵁ V.1).ι_image_top).op
          (lineProjImage f A L ψ V.1 d a)))

/-- The ring map of a morphism to an affine spectrum, expressed on ambient open sections.
Source: Stacks, Tag 01I1 (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjScalar {W : Scheme.{u}} (U : W.Opens) {R : CommRingCat.{u}}
    (q : U.toScheme ⟶ Spec R) : R ⟶ Γ(W, U) :=
  (Scheme.ΓSpecIso R).inv ≫ q.appTop ≫ U.topIso.hom

/-- The homogeneous-fraction formula on any source open. The denominator power is an
actual tensor power, and the numerator is the image of the specified homogeneous section.
Source: Stacks, Tags 01NK and 01O9 (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
def LineProjFractionFormula {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (U : W.Opens) (hU : U ≤ f ⁻¹ᵁ V.1)
    (q : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grade V)
      (lineProjElement A V d a).val))) : Prop :=
  ∀ (m : ℕ) (b : Γ(A.piece (m • d), V.1)),
    (lineProjScalar U q
      (HomogeneousLocalization.Away.mk (A.grade V) (lineProjElement A V d a).property
        m (lineProjElement A V (m • d) b).val
          (lineProjElement A V (m • d) b).property)) •
      lineProjPower L U d
        ((L.tensorPow d).presheaf.map (homOfLE hU).op
          (lineProjImage f A L ψ V.1 d a)) m =
      (L.tensorPow (m • d)).presheaf.map (homOfLE hU).op
        (lineProjImage f A L ψ V.1 (m • d) b)

/-- A morphism from the free-generator open to its affine homogeneous-localization chart.
Source: Stacks, Tags 01NK and 01O9 (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable abbrev LineProjChart {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1)) :=
  (lineProjGeneratorOpen f A L ψ V d a).toScheme ⟶
    Spec (.of (HomogeneousLocalization.Away (A.grade V) (lineProjElement A V d a).val))

/-- Composition with the standard affine chart of Proj over V.
Source: Stacks, Tags 01NK and 01O9 (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjChartToLocal {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1))
    (q : LineProjChart f A L ψ V d a) :
    (lineProjGeneratorOpen f A L ψ V d a).toScheme ⟶ Proj (A.grade V) :=
  q ≫ Proj.awayι (A.grade V) (lineProjElement A V d a).val
    (lineProjElement A V d a).property hd

/-- The chart map viewed in the canonical relative Proj of the given algebra sheaf.
Source: Stacks, Tag 01O9 (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjChartToRelative {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1))
    (q : LineProjChart f A L ψ V d a) :
    (lineProjGeneratorOpen f A L ψ V d a).toScheme ⟶ A.affineData.relProj :=
  lineProjChartToLocal f A L ψ V d hd a q ≫ A.affineData.relProjι V

/-- In every trivializing affine open, the generator open is D(alpha_a) and the ring
map sends b/a^m to alpha_b/alpha_a^m. Writing this after multiplication by alpha_a^m
also covers the empty open. Quantification over all frames expresses frame independence.
Source: Stacks, Tag 01NK (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
def LineProjTrivializationFormula {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (q : LineProjChart f A L ψ V d a) : Prop :=
  ∀ (B : W.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (e : Γ(L, B.1)), IsFreeGenerator e → ∀ αa : Γ(W, B.1),
    (L.tensorPow d).presheaf.map (homOfLE hB).op (lineProjImage f A L ψ V.1 d a) =
      αa • lineProjFramePower L B.1 e d →
    lineProjGeneratorOpen f A L ψ V d a ⊓ B.1 = W.basicOpen αa ∧
      ∀ (m : ℕ) (b : Γ(A.piece (m • d), V.1)) (αb : Γ(W, B.1)),
        (L.tensorPow (m • d)).presheaf.map (homOfLE hB).op
            (lineProjImage f A L ψ V.1 (m • d) b) =
          αb • lineProjFramePower L B.1 e (m • d) →
        W.presheaf.map (homOfLE inf_le_left).op
            (lineProjScalar (lineProjGeneratorOpen f A L ψ V d a) q
              (HomogeneousLocalization.Away.mk (A.grade V)
                (lineProjElement A V d a).property m
                (lineProjElement A V (m • d) b).val
                (lineProjElement A V (m • d) b).property)) *
          (W.presheaf.map (homOfLE
              (inf_le_right : lineProjGeneratorOpen f A L ψ V d a ⊓ B.1 ≤ B.1)).op αa) ^ m =
          W.presheaf.map (homOfLE
            (inf_le_right : lineProjGeneratorOpen f A L ψ V d a ⊓ B.1 ≤ B.1)).op αb

/-- Restriction of a homogeneous section to an affine base refinement.
Source: Stacks, Tag 01O9(3) (blueprint: lem-trf-line-proj-affine-chart-atlas). -/
noncomputable def lineProjRestrict {T : Scheme.{u}} (A : RelativeProjAlgebra T)
    {V C : T.affineOpens} (hCV : C ≤ V) (d : ℕ) (a : Γ(A.piece d, V.1)) :
    Γ(A.piece d, C.1) :=
  (A.piece d).presheaf.map (homOfLE (X := T.Opens) hCV).op a

/-- Compatibility with every affine base refinement, using the canonical restriction
map of relative-Proj affine charts. Source: Stacks, Tag 01O9(3)
(blueprint: lem-trf-line-proj-affine-chart-atlas). -/
def LineProjBaseRefinement {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (q : ∀ (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)),
      LineProjChart f A L ψ V d a) : Prop :=
  ∀ (V C : T.affineOpens) (hCV : C ≤ V) (d : ℕ) (hd : 0 < d)
    (a : Γ(A.piece d, V.1)),
    lineProjGeneratorOpen f A L ψ C d (lineProjRestrict A hCV d a) =
      lineProjGeneratorOpen f A L ψ V d a ⊓ (f ⁻¹ᵁ C.1) ∧
    ∀ h : lineProjGeneratorOpen f A L ψ C d (lineProjRestrict A hCV d a) ≤
          lineProjGeneratorOpen f A L ψ V d a,
      W.homOfLE h ≫ lineProjChartToLocal f A L ψ V d hd a (q V d hd a) =
        lineProjChartToLocal f A L ψ C d hd
            (lineProjRestrict A hCV d a) (q C d hd (lineProjRestrict A hCV d a)) ≫
          (A.gradeIso C).inv ≫ A.localTransition hCV ≫ (A.gradeIso V).hom

end AlgebraicGeometry.Scheme.Modules
