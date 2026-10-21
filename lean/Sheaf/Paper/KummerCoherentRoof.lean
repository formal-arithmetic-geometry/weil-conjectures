/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerBarResolution
public import Sheaf.Paper.KummerGeometricColumns

/-! # Coherent normalized Kummer descent roofs
Source: direct-image proof (3), compatible resolutions before finite totalization.
(blueprint: def-sfb-kummer-coherent-roof).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- A coherent roof is one complex of full simplex diagrams, with column and total
quasi-isomorphisms. Thus its arrows commute with every face and degeneracy before
localization. Source: direct-image proof (3), whole derived diagram
(blueprint: def-sfb-kummer-coherent-roof). -/
structure KummerCoherentRoof (B : Model A G) {T W U S : Scheme.{u}}
    (a : W ⟶ U) (s : S ⟶ U) (v : T ⟶ W)
    {L : KummerModules A.X W} (I : InjectiveResolution L)
    {N : Equivariant A G} (J : InjectiveResolution N) where
  complex : CochainComplex (SimplexCategory ⥤ KummerModules A.X S) ℕ
  cech : complex ⟶ kummerCechResolution A.X a s v I.cocomplex
  bar : complex ⟶ kummerBarDiagram A G B S J
  cech_columns : ∀ n : ℕ, QuasiIso
    ((((evaluation SimplexCategory (KummerModules A.X S)).obj (.mk n)).mapHomologicalComplex
      (.up ℕ)).map cech)
  bar_columns : ∀ n : ℕ, QuasiIso
    ((((evaluation SimplexCategory (KummerModules A.X S)).obj (.mk n)).mapHomologicalComplex
      (.up ℕ)).map bar)
  cech_total : IsIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap ((kummerDiagramTotal A.X S).map cech)
      ComplexShape.embeddingUpNat))
  bar_total : IsIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap ((kummerDiagramTotal A.X S).map bar)
      ComplexShape.embeddingUpNat))

  totalComparison : DerivedCategory.Q.obj
        (((kummerDiagramTotal A.X S).obj
          (kummerCechResolution A.X a s v I.cocomplex)).extend
            ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Q.obj
        (((kummerDiagramTotal A.X S).obj (kummerBarDiagram A G B S J)).extend
          ComplexShape.embeddingUpNat)
  total_normalization :
    DerivedCategory.Q.map
      (HomologicalComplex.extendMap ((kummerDiagramTotal A.X S).map cech)
        ComplexShape.embeddingUpNat) ≫ totalComparison.hom =
      DerivedCategory.Q.map
        (HomologicalComplex.extendMap ((kummerDiagramTotal A.X S).map bar)
          ComplexShape.embeddingUpNat)


end AlgebraicGeometry.ProEtale.CondensedRing
