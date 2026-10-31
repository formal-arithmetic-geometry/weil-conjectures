/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientAction
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible
public import WeilConjectures.ZetaSeries
import WeilConjectures.CategoryTheory.StageSystemAdjunction
import WeilConjectures.AlgebraicGeometry.SmoothPurityQbarFinitePackage
import WeilConjectures.AlgebraicGeometry.SmoothPurityQbarRightIdentification

/-! # Smooth purity with algebraically closed coefficients

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-sp-qbar, order 1831
(blueprint: sk-thm-sp-qbar).

The compact-support action is a presentation of the already normalized finite-level,
integral and rational construction. It is not an arbitrary functor or comparison.
The right adjoint uses the intrinsic common-stage category throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Transport the inverse of l in the fixed base field to every residue field.
No invertibility assumption on the schemes is added.
Source: blueprint main-20261015, sk-thm-sp-qbar, global coefficient hypotheses
(blueprint: sk-thm-sp-qbar). -/
@[instance_reducible] def smoothQbarResidueInvertible (T : Scheme.{u}) [T.Over (Spec (.of D.k))] :
    ∀ x : T, Invertible (l : T.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D l hl).map
      ((T ↘ Spec (.of D.k)).residueFieldAlgebraMap x) : IsUnit (l : T.residueField x)).invertible

/-- The specified adic pullback followed by the signed coefficient twist and [2d].
All residue-field inverse instances are constructed from l distinct from p.
Source: blueprint main-20261015, sk-thm-sp-qbar, displayed right adjoint
(blueprint: sk-thm-sp-qbar). -/
def smoothQbarPurityRightFunctor
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    (f : X ⟶ Y) (d : ℕ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X := by
  letI := smoothQbarResidueInvertible D l hl X
  letI := smoothQbarResidueInvertible D l hl Y
  exact commonStageDerivedPullback l Ω f ⋙ intrinsicQbarComplexTwistFunctor D l hl X Ω
    (d : ℤ) ⋙ shiftFunctor (generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (2 * (d : ℤ))

section UnitCompatibility
universe u₁ v₁ u₂ v₂

/-- The counit coefficient equation implies the unit equation by transposition.
Source: the categorical mate calculation in CompactSupportStageActionAdjunction,
`mate_unit`; this is elementary glue in the adjunction step of sk-thm-sp-qbar. -/
private theorem smoothPurity_unit_of_counit
    {A : Type u₁} {B : Type u₂} {A' : Type u₁} {B' : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₁} A'] [Category.{v₂} B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (a : F ⊣ G) (a' : F' ⊣ G') (TX : A ⥤ A') (TY : B ⥤ B')
    (q : F ⋙ TY ≅ TX ⋙ F') (b : G ⋙ TX ≅ TY ⋙ G')
    (hc : ∀ L, q.hom.app (G.obj L) ≫ F'.map (b.hom.app L) ≫
      a'.counit.app (TY.obj L) = TY.map (a.counit.app L)) (K : A) :
    TX.map (a.unit.app K) ≫ b.hom.app (F.obj K) ≫
      G'.map (q.hom.app K) = a'.unit.app (TX.obj K) := by
  apply (a'.homEquiv _ _).symm.injective
  change F'.map _ ≫ a'.counit.app _ = F'.map _ ≫ a'.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [a'.counit_naturality]
  rw [← Category.assoc (F'.map (b.hom.app _))]
  have ht : F'.map (b.hom.app (F.obj K)) ≫ a'.counit.app (TY.obj (F.obj K)) =
      q.inv.app (G.obj (F.obj K)) ≫ TY.map (a.counit.app (F.obj K)) := by
    rw [← hc (F.obj K), ← Category.assoc, ← Category.assoc]
    simp only [Iso.inv_hom_id_app, Category.id_comp]
  rw [ht]
  have hn := q.inv.naturality (a.unit.app K)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Category.assoc (TY.map _) (TY.map _), ← TY.map_comp]
  erw [a.left_triangle_components K]
  change q.inv.app K ≫ TY.map (𝟙 (F.obj K)) ≫ q.hom.app K =
    F'.map (a'.unit.app (TX.obj K)) ≫ a'.counit.app (F'.obj (TX.obj K))
  rw [TY.map_id]
  calc
    _ = q.inv.app K ≫ q.hom.app K :=
      congrArg (fun t ↦ q.inv.app K ≫ t) (Category.id_comp (q.hom.app K))
    _ = 𝟙 _ := q.inv_hom_id_app K
    _ = _ := (a'.left_triangle_components (TX.obj K)).symm

end UnitCompatibility

/-- Smooth purity: the normalized common-stage compact-support direct image is
left adjoint to adic pullback followed by (d)[2d]. The existential S supplies the
published compact-support coefficient action, including its finite maps and the
normalized integral coefficient comparisons. Thus no functor-existence or
coefficient-compatibility hypothesis is imposed.
Source: blueprint main-20261015, sk-thm-sp-qbar, order 1831
(blueprint: sk-thm-sp-qbar).

Proof: obtain the normalized finite-stage adjunction package from the finite
integral adjunction, rational localization, and coefficient-extension comparisons.
Its counit equation implies the unit equation by adjunction transposition, as proved
in smoothPurity_unit_of_counit. These two equations construct compatible stage-system
unit and counit Hom families. The public stage-system adjunction constructor descends
those families and proves both triangles from their finite-stage counterparts.
Separately, finite smooth purity and right-adjoint uniqueness identify the right
stage functors with pullback, Tate twist, and shift. Coefficient compatibility lets
these isomorphisms descend to the explicit common-stage right functor. Transport
the descended adjunction through that natural isomorphism. -/
theorem smoothPurityQbar
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f) :
    ∃ S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c,
      Nonempty (S.system.functor ⊣ smoothQbarPurityRightFunctor D l hl Ω f d) := by
  obtain ⟨P⟩ := smoothPurityQbarFinitePackage_exists D l hl Ω f d c
  let unit : StageSystem.Morphism.Hom (StageSystem.Morphism.id _)
      (P.action.system.comp P.right) :=
    { τ := fun E ↦ (P.stageAdjunction E).unit
      comm := fun {E L} h K ↦ by
        change ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).map
            ((P.stageAdjunction E).unit.app K) ≫
            ((P.action.system.comp P.right).β h).hom.app K =
          𝟙 _ ≫ (P.stageAdjunction L).unit.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj K)
        rw [StageSystem.Morphism.comp_β_hom_app, Category.id_comp]
        exact smoothPurity_unit_of_counit
          (P.stageAdjunction E) (P.stageAdjunction L)
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h)
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h)
          (P.action.system.β h) (P.right.β h) (P.counit_compatible E L h) K }
  let counit : StageSystem.Morphism.Hom (P.right.comp P.action.system)
      (StageSystem.Morphism.id _) :=
    { τ := fun E ↦ (P.stageAdjunction E).counit
      comm := fun {E L} h K ↦ by
        change ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).map
            ((P.stageAdjunction E).counit.app K) ≫ 𝟙 _ =
          ((P.right.comp P.action.system).β h).hom.app K ≫
            (P.stageAdjunction L).counit.app
              (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h).obj K)
        simp only [StageSystem.Morphism.comp_β_hom_app, Category.comp_id]
        simpa only [Category.assoc] using (P.counit_compatible E L h K).symm }
  let A := StageSystem.Morphism.adjunction P.action.system P.right
    P.stageAdjunction unit counit (fun _ ↦ rfl) (fun _ ↦ rfl)
  obtain ⟨hright⟩ := smoothPurityQbarFinitePackage_right_identification
    D l hl Ω f d c P
  refine ⟨P.action, ?_⟩
  change Nonempty (P.action.system.functor ⊣ qbarPurityRightFunctor D l hl Ω f d)
  exact ⟨A.ofNatIsoRight hright⟩

end WeilConjectures
