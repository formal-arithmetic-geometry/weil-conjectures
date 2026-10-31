/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfOpenClosedTriangleData
import WeilConjectures.AlgebraicGeometry.SfNormalizedRecollementScalarCoherence
import WeilConjectures.AlgebraicGeometry.SfNormalizedRecollementTriangles
import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Descent of normalized recollement presentations over an arbitrary base field -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Already constructed normalized finite coefficient presentations descend to the
literal common-stage category, with triangles and shifted cross-object vanishing.
No existence of integral or rational presentations is asserted here.
Source: blueprint localization proof, coefficient passage and Hom-vanishing paragraphs
(blueprint: lem-sf-normalized-recollement-common-stage-descent).
Proof: coefficient extension commutes with the exact completed closed unit and its
kernel, including their specified maps. Compare each given integral presentation
with this ordinary one using its normalization on complexes. Essential surjectivity
and naturality extend the comparison to all derived objects. Rationalize these
comparisons. Tensor associativity and the scalar unit give the identity and cocycle
equations and preserve the counit and unit. Descend both rational endofunctors and
these transformations by coherent common-stage descent; on objects use precisely the
stage and vertex of the input pair. The descent maps give the displayed normalization
isomorphisms. Each object comes from its literal coefficient stage. Apply the exact
stage inclusion to its distinguished triangle and transport by normalization. Each
map between a shifted open vertex and a closed vertex is represented over a common
larger finite field. The scalar comparisons identify its vertices with those of the
normalized presentation there. Its Hom group vanishes by the normalized rational
triangle and orthogonality theorem. Thus every representative is zero and so is its
common-stage class. This applies to all integers, arbitrary k, and empty complements. -/
theorem sfNormalizedRecollement_commonStage_descent
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X))
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L))
    (hPQ : ∀ L, SfIntegralRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
        (sfRecollementNoetherian k X) (P L) ∧
      SfRationalRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (P L) (Q L)) :
    ∃ R : SfRecollementPresentation (generalAlgebraicallyClosedConstructibleCategory l Ω X),
      SfCommonStageRecollementNormalization l Ω X Q R ∧
      (∀ K, ∃ δ, Triangle.mk (R.counit.app K) (R.unit.app K) δ ∈ distTriang _) ∧
      ∀ (K L : generalAlgebraicallyClosedConstructibleCategory l Ω X) (n : ℤ),
        Subsingleton ((R.openTerm.obj K)⟦n⟧ ⟶ R.closedTerm.obj L) := by
  classical
  obtain ⟨a, c, ha, hc, hε, hη⟩ :=
    sfNormalizedRecollement_scalar_coherence l Ω k hk i j _hij P Q hPQ
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X
  let O : S.Morphism S := ⟨fun L ↦ (Q L).openTerm, a, ha⟩
  let C : S.Morphism S := ⟨fun L ↦ (Q L).closedTerm, c, hc⟩
  let ε : StageSystem.Morphism.Hom O (StageSystem.Morphism.id S) := {
    τ := fun L ↦ (Q L).counit
    comm := by
      intro L M h K
      change (S.T h).map ((Q L).counit.app K) ≫ 𝟙 _ =
        (a h).hom.app K ≫ (Q M).counit.app ((S.T h).obj K)
      simpa only [Category.comp_id] using hε h K }
  let η : StageSystem.Morphism.Hom (StageSystem.Morphism.id S) C := {
    τ := fun L ↦ (Q L).unit
    comm := by
      intro L M h K
      change (S.T h).map ((Q L).unit.app K) ≫ (c h).hom.app K =
        𝟙 _ ≫ (Q M).unit.app ((S.T h).obj K)
      simpa only [Category.id_comp] using hη h K }
  let R : SfRecollementPresentation
      (generalAlgebraicallyClosedConstructibleCategory l Ω X) := {
    openTerm := O.functor
    closedTerm := C.functor
    counit := StageSystem.Morphism.descNatTrans ε ≫ StageSystem.Morphism.functorIdIso.hom
    unit := StageSystem.Morphism.functorIdIso.inv ≫ StageSystem.Morphism.descNatTrans η }
  have hn : SfCommonStageRecollementNormalization l Ω X Q R := by
    refine ⟨fun K ↦ ⟨rfl, rfl⟩, fun L ↦ ?_⟩
    refine ⟨O.ιCompFunctorIso L, C.ιCompFunctorIso L, ?_, ?_⟩
    · intro K
      change 𝟙 _ ≫ (S.ι L).map ((Q L).counit.app K) =
        (S.ι L).map ((Q L).counit.app K) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    · intro K
      change (𝟙 _ ≫ (S.ι L).map ((Q L).unit.app K)) ≫ 𝟙 _ =
        (S.ι L).map ((Q L).unit.app K)
      simp only [Category.id_comp, Category.comp_id]
  have hfinite (L : AlgebraicallyClosedCoefficients.Index l Ω) :
      (∀ K, ∃ δ, Triangle.mk ((Q L).counit.app K) ((Q L).unit.app K) δ ∈ distTriang _) ∧
      ∀ (K M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L) (n : ℤ),
        Subsingleton (((Q L).openTerm.obj K)⟦n⟧ ⟶ (Q L).closedTerm.obj M) :=
    sfNormalizedRationalRecollement_triangle_orthogonality l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
      (sfRecollementNoetherian k X) (P L) (Q L) (hPQ L).1 (hPQ L).2
  refine ⟨R, hn, ?_, ?_⟩
  · rintro ⟨L, K⟩
    obtain ⟨δ, hδ⟩ := (hfinite L).1 K
    obtain ⟨a', c', hε', hη'⟩ := hn.2 L
    let F := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L
    let δ' := c'.hom.app K ≫ F.map δ ≫
      (F.commShiftIso (1 : ℤ)).hom.app ((Q L).openTerm.obj K) ≫
      (shiftFunctor _ (1 : ℤ)).map (a'.inv.app K)
    refine ⟨δ', isomorphic_distinguished _ (F.map_distinguished _ hδ) _
      (Triangle.isoMk _ _ (a'.app K) (Iso.refl _) (c'.app K) ?_ ?_ ?_)⟩
    · change R.counit.app (F.obj K) ≫ 𝟙 _ =
        a'.hom.app K ≫ F.map ((Q L).counit.app K)
      simpa only [Category.comp_id] using (hε' K).symm
    · change R.unit.app (F.obj K) ≫ c'.hom.app K = 𝟙 _ ≫ F.map ((Q L).unit.app K)
      simpa only [Category.id_comp] using hη' K
    · change δ' ≫ (shiftFunctor _ (1 : ℤ)).map (a'.hom.app K) =
        c'.hom.app K ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app _)
      simp only [δ', Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [(shiftFunctor (generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (1 : ℤ)).map_id (F.obj ((Q L).openTerm.obj K))]
      exact congrArg (fun f ↦ c'.hom.app K ≫ F.map δ ≫ f)
        (Category.comp_id ((F.commShiftIso (1 : ℤ)).hom.app ((Q L).openTerm.obj K)))
  · intro K L n
    let A : GeneralAlgebraicallyClosedCoefficients.Pair l Ω X :=
      ⟨K.stage, ((Q K.stage).openTerm.obj K.obj)⟦n⟧⟩
    let B := C.functor.obj L
    let e : A ≅ (R.openTerm.obj K)⟦n⟧ :=
      ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) K.stage).commShiftIso n).app
        ((Q K.stage).openTerm.obj K.obj)
    have hraw (M : AlgebraicallyClosedCoefficients.Index l Ω)
        (hA : A.stage ≤ M) (hB : B.stage ≤ M) :
        Subsingleton (A.toStage hA ⟶ B.toStage hB) := by
      let es : A.toStage hA ≅ ((Q M).openTerm.obj (K.toStage hA))⟦n⟧ :=
        ((GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω X K.stage M hA
          ).commShiftIso n).app ((Q K.stage).openTerm.obj K.obj) ≪≫
          (shiftFunctor _ n).mapIso ((a hA).app K.obj)
      let et : B.toStage hB ≅ (Q M).closedTerm.obj (L.toStage hB) :=
        (c hB).app L.obj
      have := (hfinite M).2 (K.toStage hA) (L.toStage hB) n
      exact (Iso.homCongr es et).injective.subsingleton
    have hz (f : A ⟶ B) : f = 0 := by
      induction f using StageSystem.PairCategory.hom_induction with
      | h M hA hB f =>
        rw [StageSystem.mkHom_eq_isoToStage]
        rw [(hraw M hA hB).elim f 0]
        change (S.isoToStage A hA).hom ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion M).map 0 ≫
          (S.isoToStage B hB).inv = 0
        simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
    have : Subsingleton (A ⟶ B) := ⟨fun f g ↦ (hz f).trans (hz g).symm⟩
    exact (Iso.homCongr e.symm (Iso.refl B)).injective.subsingleton

end WeilConjectures
