module

public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Mathlib.CategoryTheory.Localization.Prod

/-! # Relative derived tensor and its canonical projection arrow for algebraic spaces

Source: Stacks Project, sites-cohomology.tex, Tags 08I6 and 0B56;
spaces-perfect.tex, Tag 08IS
(blueprint: def-sfb-space-relative-derived-projection).

The relative tensor is the total left derived functor of the ordinary balanced tensor,
with its structure-module action through the first factor. Ordinary balanced tensor is
computed as M tensor over O_X with f* N: the two inverse balancing formulas are
m tensor (a tensor n) ↦ a m tensor n and m tensor n ↦ m tensor (1 tensor n).
Thus the construction retains the O_X action before localization. It does not choose
a replacement derived object from an unspecified existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

attribute [local irreducible] derivedDualityModel derivedTensorPullback
  smallModuleTensorPullback WeilConjectures.coefficientTotalTensor
  WeilConjectures.CoefficientTensorModels.iso CochainComplex.IsKFlatIndependentCoefficients

/-- The ordinary relative balanced tensor, with the action through the first factor,
formed as the signed direct-sum total of M tensor f* N and then localized.
The ordinary balancing identification is an equality of bifunctors via the inverse
pure-tensor formulas in the module header, so deriving this presentation derives the
relative tensor itself. Source: Stacks, Tag 08I6
(blueprint: def-sfb-space-relative-derived-projection). -/
def spaceRelativeTensorComplex (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] :
    CochainComplex X.SmallModules ℤ × CochainComplex Y.SmallModules ℤ ⥤ X.DerivedModules :=
  (𝟭 (CochainComplex X.SmallModules ℤ)).prod
      ((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)) ⋙
    WeilConjectures.coefficientTotalTensor.{u, u, u}
      X.smallEtaleModelTopology X.smallStructureSheaf ⋙ DerivedCategory.Q

/-- The relative balanced tensor has a total left derived functor at pairs of
quasi-isomorphisms. Source: Stacks, Tags 06YS, 06YY and 08I6
(blueprint: def-sfb-space-relative-derived-projection).
Proof: resolve each input by a flat-term K-flat complex. Inverse image preserves
flatness and K-flatness over the inverse-image ring. Tensoring its second input
with the first preserves quasi-isomorphisms on these resolutions. The action
through the first factor commutes with every differential and comparison. The ordinary
balanced tensor identification transports this to the displayed total complex.
The resolving-class localization theorem supplies its right Kan extension along the
product of the two localization functors, hence the claimed derived universal property.
No flatness of O_X over the inverse-image ring, or boundedness, is needed. -/
@[instance] theorem spaceRelativeTensorComplex_hasLeftDerived (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] :
    (spaceRelativeTensorComplex f).HasLeftDerivedFunctor
      ((HomologicalComplex.quasiIso X.SmallModules (.up ℤ)).prod
        (HomologicalComplex.quasiIso Y.SmallModules (.up ℤ))) := by
  sorry

/-- Relative derived tensor is the universal total left derivation of the actual
ordinary balanced tensor, not a freely chosen bifunctor.
Source: Stacks, Tags 06YS and 08I6 (blueprint: def-sfb-space-relative-derived-projection). -/
def spaceRelativeDerivedTensor (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    X.DerivedModules × Y.DerivedModules ⥤ X.DerivedModules :=
  (spaceRelativeTensorComplex f).totalLeftDerived
    ((DerivedCategory.Q (C := X.SmallModules)).prod
      (DerivedCategory.Q (C := Y.SmallModules)))
    ((HomologicalComplex.quasiIso X.SmallModules (.up ℤ)).prod
      (HomologicalComplex.quasiIso Y.SmallModules (.up ℤ)))

/-- The universal comparison to ordinary relative tensor on any pair of complexes.
Source: Stacks, Tags 06YS and 08I6 (blueprint: def-sfb-space-relative-derived-projection). -/
def spaceRelativeTensorCounit (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    ((DerivedCategory.Q (C := X.SmallModules)).prod
      (DerivedCategory.Q (C := Y.SmallModules))) ⋙ spaceRelativeDerivedTensor f ⟶
        spaceRelativeTensorComplex f :=
  (spaceRelativeTensorComplex f).totalLeftDerivedCounit _
    ((HomologicalComplex.quasiIso X.SmallModules (.up ℤ)).prod
      (HomologicalComplex.quasiIso Y.SmallModules (.up ℤ)))

/-- The scalar-restriction identification is uniquely normalized on every pair of
flat-term K-flat representatives by the ordinary balanced tensor formulas.
Source: Stacks, Tag 08I6 (blueprint: def-sfb-space-relative-derived-projection).
Proof: flat-term K-flat pullback computes Lf*. On those representatives apply the
ordinary balanced identification m tensor (a tensor n) ↦ a m tensor n. Its inverse
inserts 1. Both commute with the signed total differentials and all chain maps.
The fixed tensor representative isomorphism and the shared pullback counit give
exactly the displayed equation. Resolving-class localization in both variables
extends these maps uniquely to a natural isomorphism. Every derived object has such
a resolution, so the same equation proves uniqueness. This also proves the comparison
retains the first-factor O_X action without imposing flatness of the structural map. -/
theorem spaceRelativeTensorComparison_existsUnique (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    ∃! e : (𝟭 X.DerivedModules).prod (spaceDerivedPullback f) ⋙
        (derivedDualityModel X).closed.tensor ≅ spaceRelativeDerivedTensor f,
      ∀ (P : CochainComplex X.SmallModules ℤ) (Q : CochainComplex Y.SmallModules ℤ)
        (hP : SingleComplex.FlatKFlat X P) (hQ : SingleComplex.FlatKFlat Y Q),
        ∃ hQ' : SingleComplex.FlatKFlat X
          (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj Q),
        e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            (spaceRelativeTensorCounit f).app (P, Q) =
          (derivedDualityModel X).closed.tensor.map
              (Prod.mkHom (𝟙 _) ((spaceDerivedPullbackCounit f).app Q)) ≫
            (WeilConjectures.CoefficientTensorModels.iso.{u, u, u, w}
              X.smallEtaleModelTopology X.smallStructureSheaf
              (derivedDualityModel X).closed (derivedDualityModel X).models
              P (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj Q)
              hP.1 hQ'.1).inv := by
  sorry

/-- The canonical scalar-restriction identification, selected by its unique complete
representative normalization. Source: Stacks, Tag 08I6
(blueprint: def-sfb-space-relative-derived-projection). -/
def spaceRelativeTensorComparison (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    (𝟭 X.DerivedModules).prod (spaceDerivedPullback f) ⋙
      (derivedDualityModel X).closed.tensor ≅ spaceRelativeDerivedTensor f :=
  (spaceRelativeTensorComparison_existsUnique f).choose

/-- The canonical projection mate: transpose the pullback tensor comparison followed
by the derived counit on the first factor. Source: Stacks, Tag 0B56
(blueprint: def-sfb-space-relative-derived-projection). -/
def spaceProjectionComparison (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (E : X.DerivedModules) (G : Y.DerivedModules) :
    (derivedDualityModel Y).closed.tensor.obj ((derivedDirectImage f).obj E, G) ⟶
      (derivedDirectImage f).obj ((derivedDualityModel X).closed.tensor.obj
        (E, (spaceDerivedPullback f).obj G)) :=
  (spaceDerivedAdjunction f).homEquiv _ _
    ((moduleDerivedPullbackTensor f).hom.app ((derivedDirectImage f).obj E, G) ≫
      (derivedDualityModel X).closed.tensor.map
        (Prod.mkHom ((spaceDerivedAdjunction f).counit.app E) (𝟙 _)))

/-- Projection followed by the canonical balanced scalar-restriction identification.
Source: Stacks, Tags 08IS, 08I6 and 0B56
(blueprint: def-sfb-space-relative-derived-projection). -/
def spaceRelativeProjectionComparison (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (E : X.DerivedModules) (G : Y.DerivedModules) :
    (derivedDualityModel Y).closed.tensor.obj ((derivedDirectImage f).obj E, G) ⟶
      (derivedDirectImage f).obj ((spaceRelativeDerivedTensor f).obj (E, G)) :=
  spaceProjectionComparison f E G ≫
    (derivedDirectImage f).map ((spaceRelativeTensorComparison f).hom.app (E, G))

/-- The specified projection comparison is bifunctorial, even when it is not invertible.
Source: Stacks, Tags 0B56 and 08I6 (blueprint: def-sfb-space-relative-derived-projection).
Proof: transpose the two projection composites under the fixed derived adjunction.
Naturality of the tensor-pullback comparison and of the counit makes the transposes
equal. Injectivity of the adjunction bijection proves equality of the mates. Compose
with the natural balanced scalar-restriction identification to obtain this equation. -/
theorem spaceRelativeProjectionComparison_naturality (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    {E E' : X.DerivedModules} {G G' : Y.DerivedModules} (a : E ⟶ E') (b : G ⟶ G') :
    (derivedDualityModel Y).closed.tensor.map
        (Prod.mkHom ((derivedDirectImage f).map a) b) ≫
      spaceRelativeProjectionComparison f E' G' =
    spaceRelativeProjectionComparison f E G ≫
      (derivedDirectImage f).map ((spaceRelativeDerivedTensor f).map (Prod.mkHom a b)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
