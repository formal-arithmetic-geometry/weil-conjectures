/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.SixFunctors.OpenExternalTensorNormalization
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Algebra.Homology.BifunctorShift

/-! # Whole-system open external tensor coherence

Source: Stacks Project, Tag 0GL1, `lemma-j-shriek-and-tensor`, and the
open-factor reduction in the blueprint proof of `lem-sf-kunneth-coherence`.
(blueprint: lem-sf-semilinear-open-external-coherence).

The existing varying-ring operations act on ordinary unbounded derived categories
of modules on the vertical sequence site. Tensor presentations below are fixed by
ordinary section formulas and K-flat totalization, including the Koszul symmetry.
The existing coefficient-independent product diagrams are reused.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
open AlgebraicGeometry.ProEtale.VaryingRing
open AlgebraicGeometry.ProEtale.OpenExternalTensor (Diagram Triple)

namespace AlgebraicGeometry.ProEtale.SemilinearOpenExternal

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The existing ring object of whole systems, without evaluation or scalar restriction.
Source: Zheng Construction 4.1; Stacks 0GL1 on the diagram site
(blueprint: lem-sf-semilinear-open-external-coherence). -/
abbrev systemCoefficients (X : Scheme.{u}) :=
  systemRing (ProEt.topology X) (coefficients C X) (coefficientTransition C τ X)

/-- A simultaneous presentation of the specified tensor operations. The ordinary
comparison is fixed on pure sections by the actual inverse-image unit, and the
recorded model fixes its totalization and localization. Symmetry and associators
have their recorded signed K-flat models. These are conclusions, not additional
hypotheses on the coefficient tower or on derived objects.
Source: Stacks 0GL1, 06YS, 08J9; Zheng 4.1 and 4.10
(blueprint: lem-sf-semilinear-open-external-coherence). -/
structure TensorData where
  systems : ∀ X : Scheme.{u}, Data.{u + 1, u, u + 1} (ProEt.topology X)
    (coefficients C X) (coefficientTransition C τ X)
  symmetry : ∀ X : Scheme.{u},
    @SymmetricCategory (Derived C τ X) _ (systems X).closed.monoidal
  coherence : ∀ X : Scheme.{u},
    RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
      (coefficientSequenceTopology (ProEt.topology X)) (systemCoefficients C τ X)
      (systems X).closed (systems X).tensorModels (symmetry X)
  mu : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (systems Y).closed.tensor ⋙ G C τ f ≅
      (G C τ f).prod (G C τ f) ⋙ (systems X).closed.tensor
  model : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    TensorComparisonModel.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X))
      (systemCoefficients C τ Y) (systemCoefficients C τ X) (pull C τ f)
      (systems Y).closed (systems X).closed
      (systems Y).tensorModels (systems X).tensorModels (mu f)
  ordinary_sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Modules C τ Y)
      (V : (ℕ × Y.ProEt)ᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
    (((moduleAdj C τ f).homEquiv _ _ ((model f).ordinary M N).hom).val.app V)
      (tensorSection.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (systemCoefficients C τ Y) M N V x y) =
    tensorSection.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology X))
      (systemCoefficients C τ X) ((pull C τ f).obj M) ((pull C τ f).obj N)
      ((VaryingRing.baseChange f).op.obj V)
      (((moduleAdj C τ f).unit.app M).val.app V x)
      (((moduleAdj C τ f).unit.app N).val.app V y)

variable {C τ} (o : TensorData C τ)

/-- Tensor on whole systems from the dependency's closed structure.
Source: Stacks 06YS (blueprint: lem-sf-semilinear-open-external-coherence). -/
abbrev TensorData.tensor (X : Scheme.{u}) (M N : Derived C τ X) :=
  (o.systems X).closed.tensor.obj (M, N)

/-- Tensor of whole-system arrows.
Source: Stacks 06YS (blueprint: lem-sf-semilinear-open-external-coherence). -/
def TensorData.tensorMap (X : Scheme.{u}) {M M' N N' : Derived C τ X}
    (f : M ⟶ M') (g : N ⟶ N') : o.tensor X M N ⟶ o.tensor X M' N' :=
  (o.systems X).closed.tensor.map (Prod.mkHom f g)

/-- Tensor of whole-system isomorphisms.
Source: Stacks 06YS (blueprint: lem-sf-semilinear-open-external-coherence). -/
def TensorData.tensorIsoMap (X : Scheme.{u}) {M M' N N' : Derived C τ X}
    (f : M ≅ M') (g : N ≅ N') : o.tensor X M N ≅ o.tensor X M' N' :=
  (o.systems X).closed.tensor.mapIso (Iso.prod f g)

/-- The signed symmetry, pinned by the recorded total-complex model.
Source: Stacks 06YN, 0FPT (blueprint: lem-sf-semilinear-open-external-coherence). -/
def TensorData.sigma (X : Scheme.{u}) (M N : Derived C τ X) : o.tensor X M N ⟶ o.tensor X N M :=
  ((o.symmetry X).toBraidedCategory.braiding M N).hom

/-- The unsigned associator on total tensor summands.
Source: Stacks 06YN, 0FPT (blueprint: lem-sf-semilinear-open-external-coherence). -/
def TensorData.associator (X : Scheme.{u}) (M N P : Derived C τ X) :
    o.tensor X (o.tensor X M N) P ≅ o.tensor X M (o.tensor X N P) :=
  (o.systems X).closed.monoidal.associator M N P

/-- The canonical tensor comparison of exact geometric inverse image.
Source: Stacks 07A4 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def TensorData.tensorPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Derived C τ Y) :=
  (o.mu f).app (M, N)

/-- The square comparison formed only from the existing normalized compositors.
Source: Stacks 07A7 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def square {A B D E : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ D)
    (p : B ⟶ E) (i : D ⟶ E) (h : k ≫ p = r ≫ i) :
    G C τ p ⋙ G C τ k ≅ G C τ i ⋙ G C τ r :=
  (gComp C τ k p).symm ≪≫ eqToIso (congrArg (G C τ) h) ≪≫ gComp C τ r i

/-- The inverse open tensor word, defined by the specified open-unit transpose.
Source: Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def TensorData.gammaInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Derived C τ U) (N : Derived C τ X) :
    (J C τ j).obj (o.tensor U M ((G C τ j).obj N)) ⟶
      o.tensor X ((J C τ j).obj M) N :=
  ((jAdj C τ j).homEquiv _ _).symm
    (o.tensorMap U ((jAdj C τ j).unit.app M) (𝟙 _) ≫
      (o.tensorPullIso j ((J C τ j).obj M) N).inv)

/-- Normalized open tensor maps, uniquely specified by their inverse transpose.
This is presentation data for the open comparisons of the dependency, not a
hypothesis asserting the external coherence being proved.
Source: Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
structure OpenTensorData
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    extends TensorData C τ where
  gamma : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    (J C τ j).prod (𝟭 _) ⋙ (systems X).closed.tensor ≅
      (𝟭 _).prod (G C τ j) ⋙ (systems U).closed.tensor ⋙ J C τ j
  gamma_inverse : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : Derived C τ U) (N : Derived C τ X),
    (gamma j).inv.app (M, N) = toTensorData.gammaInv j M N

variable (a : OpenTensorData C τ)

/-- The second-factor open tensor word includes both signed interchanges.
Source: Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def rho {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Derived C τ X) (N : Derived C τ U) :=
  a.toTensorData.sigma X M ((J C τ j).obj N) ≫
    (a.gamma j).hom.app (N, M) ≫
    (J C τ j).map (a.toTensorData.sigma U N ((G C τ j).obj M))

/-- Transport the existing extension functor along equality of scheme maps.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-open-external-coherence). -/
def shriekCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J C τ f ≅ J C τ g :=
  eqToIso (by cases h; rfl)

/-- Component of the normalized natural open tensor isomorphism.
Source: Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def gammaMap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Derived C τ U) (N : Derived C τ X) := (a.gamma j).hom.app (M, N)

variable {X Y Xb Yb T Tb : Scheme.{u}} {j : X ⟶ Xb} {k : Y ⟶ Yb}
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The ambient external product of the two extensions.
Source: V in the statement; proof step 2, Stacks 0GL1
(blueprint: lem-sf-semilinear-open-external-coherence). -/
def ambient (d : Diagram j k T Tb) (K : Derived C τ X) (L : Derived C τ Y) : Derived C τ Tb :=
  a.toTensorData.tensor Tb
    ((G C τ d.pb).obj ((J C τ j).obj K))
    ((G C τ d.qb).obj ((J C τ k).obj L))

/-- The external product on the open.
Source: D in the statement (blueprint: lem-sf-semilinear-open-external-coherence). -/
def inside (d : Diagram j k T Tb) (K : Derived C τ X) (L : Derived C τ Y) : Derived C τ T :=
  a.toTensorData.tensor T
    ((G C τ d.p).obj K) ((G C τ d.q).obj L)

/-- The prescribed first-factor construction: beta for j, gamma for j₁, beta for k,
then signed symmetry, gamma for k₁, signed symmetry inside k₁!, and the normalized
composition comparison. All equalities are transported by pullback composition.
Source: proof step 2, Stacks 03S6 and 0GL1
(blueprint: lem-sf-semilinear-open-external-coherence). -/
def comparison (d : Diagram j k T Tb) (K : Derived C τ X) (L : Derived C τ Y) :=
  a.toTensorData.tensorMap Tb
      ((openBaseChange C τ d.r d.j₁ j d.pb d.first.w d.first).app K) (𝟙 _) ≫
    gammaMap a d.j₁ ((G C τ d.r).obj K)
      ((G C τ d.qb).obj ((J C τ k).obj L)) ≫
    (J C τ d.j₁).map
      (a.toTensorData.tensorMap d.S (𝟙 _)
        (((gComp C τ d.j₁ d.qb).symm ≪≫
          eqToIso (congrArg (G C τ) d.j₁_qb)).hom.app
            ((J C τ k).obj L))) ≫
    (J C τ d.j₁).map
      (a.toTensorData.tensorMap d.S (𝟙 _)
        ((openBaseChange C τ d.q d.k₁ k d.s d.second.w d.second).app L)) ≫
    (J C τ d.j₁).map
      (rho a d.k₁
        ((G C τ d.r).obj K) ((G C τ d.q).obj L) ≫
        (J C τ d.k₁).map
          (a.toTensorData.tensorMap T
            (((gComp C τ d.k₁ d.r).symm ≪≫
              eqToIso (congrArg (G C τ) d.k₁_r)).hom.app K) (𝟙 _))) ≫
    ((jComp C τ d.k₁ d.j₁) ≪≫
      shriekCongr (C := C) (τ := τ) d.factor).hom.app (inside a d K L)

/-- Identify D with the restriction of H by the inverse tensor comparison, the two
projection squares and the section-normalized open units.
Source: proof step 3, Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def restriction (d : Diagram j k T Tb) (K : Derived C τ X) (L : Derived C τ Y) :=
  a.toTensorData.tensorMap T
    ((G C τ d.p).map ((jAdj C τ j).unit.app K) ≫
      (square (C := C) (τ := τ) _ _ _ _ d.left).inv.app ((J C τ j).obj K))
    ((G C τ d.q).map ((jAdj C τ k).unit.app L) ≫
      (square (C := C) (τ := τ) _ _ _ _ d.right).inv.app ((J C τ k).obj L)) ≫
    (a.toTensorData.tensorPullIso d.u _ _).inv

/-- The other factorization, with both signed interchanges in the specified places.
Source: proof step 5, Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def oppositeComparison (d : Diagram j k T Tb) (K : Derived C τ X) (L : Derived C τ Y) :=
  a.toTensorData.sigma Tb _ _ ≫ comparison a d.swap L K ≫
    (J C τ d.u).map (a.toTensorData.sigma T _ _)

/-- Morphisms of the ambient external product. Source: the naturality clause
(blueprint: lem-sf-semilinear-open-external-coherence). -/
def ambientMap (d : Diagram j k T Tb) {K K' : Derived C τ X} {L L' : Derived C τ Y}
    (f : K ⟶ K') (g : L ⟶ L') : ambient a d K L ⟶ ambient a d K' L' :=
  a.toTensorData.tensorMap Tb
    ((G C τ d.pb).map ((J C τ j).map f))
    ((G C τ d.qb).map ((J C τ k).map g))

/-- Morphisms of the open external product. Source: the naturality clause
(blueprint: lem-sf-semilinear-open-external-coherence). -/
def insideMap (d : Diagram j k T Tb) {K K' : Derived C τ X} {L L' : Derived C τ Y}
    (f : K ⟶ K') (g : L ⟶ L') : inside a d K L ⟶ inside a d K' L' :=
  a.toTensorData.tensorMap T
    ((G C τ d.p).map f) ((G C τ d.q).map g)

/-- The binary normalization, opposite-factorization and signed-symmetry equations.
The symmetry is written after transporting the swapped products to the same cones.
Source: proof steps 3--5, Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def BinaryAssertion (d : Diagram j k T Tb) (K : Derived C τ X) (L : Derived C τ Y) : Prop :=
  IsIso (comparison a d K L) ∧ IsIso (oppositeComparison a d K L) ∧
    (restriction a d K L ≫ (G C τ d.u).map (comparison a d K L) =
      (jAdj C τ d.u).unit.app (inside a d K L)) ∧
    (oppositeComparison a d K L = comparison a d K L) ∧
    (comparison a d K L ≫ (J C τ d.u).map
        (a.toTensorData.sigma T
          ((G C τ d.p).obj K) ((G C τ d.q).obj L)) =
      a.toTensorData.sigma Tb
          ((G C τ d.pb).obj ((J C τ j).obj K))
          ((G C τ d.qb).obj ((J C τ k).obj L)) ≫
        comparison a d.swap L K)

variable {W Wb T₁₂ T₂₃ Tb₁₂ Tb₂₃ : Scheme.{u}} {l : W ⟶ Wb}
  [IsOpenImmersion l]

/-- The triple ambient object, with left bracketing and composed projection pullbacks.
Source: H₃ in proof step 6, Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def tripleAmbient (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : Derived C τ X) (L : Derived C τ Y) (M : Derived C τ W) : Derived C τ Tb :=
  a.toTensorData.tensor Tb
    (a.toTensorData.tensor Tb
      ((G C τ dL.pb).obj
        ((G C τ d₁₂.pb).obj ((J C τ j).obj K)))
      ((G C τ dL.pb).obj
        ((G C τ d₁₂.qb).obj ((J C τ k).obj L))))
    ((G C τ dL.qb).obj ((J C τ l).obj M))

/-- The triple open object with the same left bracketing.
Source: D₃ in proof step 6, Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def tripleInside (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : Derived C τ X) (L : Derived C τ Y) (M : Derived C τ W) : Derived C τ T :=
  a.toTensorData.tensor T
    (a.toTensorData.tensor T
      ((G C τ dL.p).obj ((G C τ d₁₂.p).obj K))
      ((G C τ dL.p).obj ((G C τ d₁₂.q).obj L)))
    ((G C τ dL.q).obj M)

/-- First compare the first two factors, then their product with the third.
Source: F in proof step 6, Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def tripleLeft (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : Derived C τ X) (L : Derived C τ Y) (M : Derived C τ W) :=
  (a.toTensorData.tensorIsoMap _
    (a.toTensorData.tensorPullIso dL.pb _ _).symm (Iso.refl _)).hom ≫
    a.toTensorData.tensorMap Tb
      ((G C τ dL.pb).map (comparison a d₁₂ K L)) (𝟙 _) ≫
    comparison a dL (inside a d₁₂ K L) M ≫
    (J C τ dL.u).map
      (a.toTensorData.tensorIsoMap _
        (a.toTensorData.tensorPullIso dL.p _ _) (Iso.refl _)).hom

/-- The canonical outer reassociation and projection-composition identification.
Source: the ambient associator in proof step 6, Stacks 0GL1
(blueprint: lem-sf-semilinear-open-external-coherence). -/
def outerAssociator
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : Derived C τ X) (L : Derived C τ Y) (M : Derived C τ W) :
    tripleAmbient a d₁₂ dL K L M ≅
      a.toTensorData.tensor Tb
        ((G C τ dR.pb).obj ((J C τ j).obj K))
        ((G C τ dR.qb).obj (ambient a d₂₃ L M)) :=
  a.toTensorData.tensorIsoMap _ (a.toTensorData.tensorIsoMap _
      (((gComp C τ dL.pb d₁₂.pb).symm ≪≫
        eqToIso (congrArg (G C τ) t.outer₁)).app ((J C τ j).obj K))
      ((square (C := C) (τ := τ) _ _ _ _ t.outer₂).app ((J C τ k).obj L)))
    ((eqToIso (congrArg (G C τ) t.outer₃) ≪≫
      gComp C τ dR.qb d₂₃.qb).app ((J C τ l).obj M)) ≪≫
    (a.toTensorData.associator Tb _ _ _) ≪≫
      a.toTensorData.tensorIsoMap _ (Iso.refl _)
      (a.toTensorData.tensorPullIso dR.qb _ _).symm

/-- Reassociate the open factors using exactly the same projection-composition maps.
Source: the open associator in proof step 6, Stacks 0GL1
(blueprint: lem-sf-semilinear-open-external-coherence). -/
def innerAssociator
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : Derived C τ X) (L : Derived C τ Y) (M : Derived C τ W) :
    inside a dR K (inside a d₂₃ L M) ≅ tripleInside a d₁₂ dL K L M :=
  a.toTensorData.tensorIsoMap _ (Iso.refl _) (a.toTensorData.tensorPullIso dR.q _ _) ≪≫
    a.toTensorData.tensorIsoMap _
      (((eqToIso (congrArg (G C τ) t.inner₁)).symm ≪≫
        gComp C τ dL.p d₁₂.p).app K)
      (a.toTensorData.tensorIsoMap _ ((square (C := C) (τ := τ) _ _ _ _ t.inner₂).symm.app L)
        (((gComp C τ dR.q d₂₃.q).symm ≪≫
          eqToIso (congrArg (G C τ) t.inner₃.symm)).app M)) ≪≫
    (a.toTensorData.associator T _ _ _).symm

/-- First compare the last two factors, then the first factor with their product.
The final transport is the identity of the common product open, followed by its
canonical associator. Source: G in proof step 6, Stacks 0GL1
(blueprint: lem-sf-semilinear-open-external-coherence). -/
def tripleRight
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : Derived C τ X) (L : Derived C τ Y) (M : Derived C τ W) :=
  (outerAssociator a t K L M).hom ≫
    a.toTensorData.tensorMap Tb (𝟙 _)
      ((G C τ dR.qb).map (comparison a d₂₃ L M)) ≫
    comparison a dR K (inside a d₂₃ L M) ≫
    (J C τ dR.u).map (innerAssociator a t K L M).hom ≫
    (shriekCongr (C := C) (τ := τ) t.sameOpen).hom.app (tripleInside a d₁₂ dL K L M)

/-- The triple restriction uses the same section units and tensor comparisons on
both sides; it contains no occurrence of either triple comparison.
Source: the identity-on-the-open clause in proof step 6, Stacks 0GL1
(blueprint: lem-sf-semilinear-open-external-coherence). -/
def tripleRestriction (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : Derived C τ X) (L : Derived C τ Y) (M : Derived C τ W) :=
  a.toTensorData.tensorMap T
    ((a.toTensorData.tensorPullIso dL.p _ _).inv ≫
      (G C τ dL.p).map (restriction a d₁₂ K L) ≫
        (square (C := C) (τ := τ) _ _ _ _ dL.left).inv.app (ambient a d₁₂ K L))
    ((G C τ dL.q).map ((jAdj C τ l).unit.app M) ≫
      (square (C := C) (τ := τ) _ _ _ _ dL.right).inv.app ((J C τ l).obj M)) ≫
    (a.toTensorData.tensorPullIso dL.u _ _).inv ≫
    (G C τ dL.u).map
      (a.toTensorData.tensorIsoMap _
        (a.toTensorData.tensorPullIso dL.pb _ _) (Iso.refl _)).hom

/-- Equality of the two triple composites, and their separate identity restrictions.
Source: proof step 6, Stacks 0GL1 (blueprint: lem-sf-semilinear-open-external-coherence). -/
def TripleAssertion
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : Derived C τ X) (L : Derived C τ Y) (M : Derived C τ W) : Prop :=
  tripleLeft a d₁₂ dL K L M = tripleRight a t K L M ∧
    (tripleRestriction a d₁₂ dL K L M ≫
      (G C τ dL.u).map (tripleLeft a d₁₂ dL K L M) =
        (jAdj C τ dL.u).unit.app
          (tripleInside a d₁₂ dL K L M)) ∧
    (tripleRestriction a d₁₂ dL K L M ≫
      (G C τ dL.u).map (tripleRight a t K L M) =
        (jAdj C τ dL.u).unit.app
          (tripleInside a d₁₂ dL K L M))


/-- The external word on arbitrary whole derived systems is natural, invertible,
unit normalized, independent of the open factorization, symmetric with Koszul
signs, and associative on triple products, before evaluation or scalar restriction.

Source: Stacks Project, Tag 0GL1, `lemma-j-shriek-and-tensor`; the diagram-topos
external-product coherence obligation refining the open-factor reduction in
`lem-sf-kunneth-coherence` (blueprint: lem-sf-semilinear-open-external-coherence).

Proof, following the seven steps of the node:
1. Apply lem-coef-semilinear-derived-sections on every vertical sequence site.
Use lem-sf-open-tensor-normalization there, with arbitrary coefficient transitions.
The ordinary section formula and total K-flat models fix tensor pullback and
signed symmetry. Composite open adjunctions have the composite unit of
def-weil-pbc-composite-adjunction. The unit equation of
lem-weil-pbc-conjugate-iso-unit-equation fixes jComp and its identity restriction.
2. Through X times Y-bar, apply beta for j, gamma for j1, beta for k, the signed
symmetry, gamma for k1, the internal signed symmetry, and the final compositor.
This is comparison, with the intervening gComp identifications displayed. Every
factor is natural and invertible by lem-sf-open-tensor-normalization.
3. Restrict this word to the product open. Each beta and gamma is identity under
its open units and restriction/tensor comparison. The two Koszul signs multiply
to (-1)^(ij+ji)=1. The last compositor preserves the composite unit. Thus
restriction followed by G(u)(comparison) is exactly the unit at inside.
Use lem-sf-ringed-derived-closed-symmetric-monoidal for the signed cancellation.
4. Precompose two maps out of ambient into J(u)(D') with comparison inverse.
They become maps J(u)(D) to J(u)(D'). Full faithfulness writes these as J(u)
of maps on the open. Naturality of its invertible unit identifies equality after
restriction with equality of these maps. This proves the needed injectivity only
for the supported source, not for arbitrary ambient derived objects.
5. The opposite factorization and the transported reversed word restrict to the
same map. Their symmetries cancel by the same signed identity. Step 4 identifies
them with comparison and gives the stated signed symmetry square.
6. Form tripleLeft and tripleRight with the displayed canonical pullback/tensor
comparisons and associators. Restriction of each binary comparison is identity by
step 3. Open compositors preserve units by step 1. The remaining associator sends
((x tensor y) tensor z) to (x tensor (y tensor z)), with no sign. The total-complex
convention def-pc-tensor-complex-sheaves and localization
lem-weil-pbc-site-derived-tensor-descent carry this equality on whole-system
K-flat representatives to the ordinary derived category. This is the equation
with tripleRestriction for each word, after the displayed associators.
7. One iterated word is an isomorphism onto J(v)(D3). Apply step 4 with that word
and the triple open v: equal restrictions imply the triple words are equal.
Every arrow has been constructed in the category of whole semilinear systems, so
coefficient actions and all transitions are preserved. No normalization of the
objects, flatness of ring transitions, boundedness, constructibility or properness
is used. Naturality is the composite of the naturalities in step 2. -/
theorem semilinear_open_external_coherence
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n) :
    ∃ a : OpenTensorData C τ,
      ∀ {B X Y Xb Yb T Tb : Scheme.{u}}
        (j : X ⟶ Xb) (k : Y ⟶ Yb) [IsOpenImmersion j] [IsOpenImmersion k]
        (f : Xb ⟶ B) (g : Yb ⟶ B) (d : Diagram j k T Tb),
        IsPullback d.pb d.qb f g →
        IsPullback d.p d.q (j ≫ f) (k ≫ g) →
        ∀ (K : Derived C τ X) (L : Derived C τ Y),
          BinaryAssertion a d K L ∧
          (∀ (K' : Derived C τ X) (L' : Derived C τ Y) (s : K ⟶ K') (t : L ⟶ L'),
            comparison a d K L ≫ (J C τ d.u).map (insideMap a d s t) =
              ambientMap a d s t ≫ comparison a d K' L') ∧
          (∀ {W Wb T₂₃ Tb₂₃ T₃ Tb₃ : Scheme.{u}}
            (l : W ⟶ Wb) [IsOpenImmersion l] (h : Wb ⟶ B)
            (M : Derived C τ W) (d₂₃ : Diagram k l T₂₃ Tb₂₃)
            (dL : Diagram d.u l T₃ Tb₃) (dR : Diagram j d₂₃.u T₃ Tb₃)
            (t : Triple d d₂₃ dL dR),
            IsPullback d₂₃.pb d₂₃.qb g h →
            IsPullback d₂₃.p d₂₃.q (k ≫ g) (l ≫ h) →
            IsPullback dL.pb dL.qb (d.pb ≫ f) h →
            IsPullback dL.p dL.q (d.p ≫ j ≫ f) (l ≫ h) →
            IsPullback dR.pb dR.qb f (d₂₃.pb ≫ g) →
            IsPullback dR.p dR.q (j ≫ f) (d₂₃.p ≫ k ≫ g) →
            TripleAssertion a t K L M) := by
  sorry

end AlgebraicGeometry.ProEtale.SemilinearOpenExternal
