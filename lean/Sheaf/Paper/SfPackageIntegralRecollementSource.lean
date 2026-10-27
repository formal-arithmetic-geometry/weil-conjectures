/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
import Sheaf.Paper.SfPackageIntegralRecollementNormalization
import all Sheaf.Paper.SfNormalizedRecollementTriangles
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension

/-! # Source recollement for the supplied integral adjunctions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)

/-- The datum's completed counit and unit have a unique natural recollement boundary.
Source: current blueprint prop-functor-package.proof.md, clause (3), source
recollement before applying compact support; Stacks Tag 0152.
(blueprint: lem-sf-package-integral-recollement-source).

Proof: use the completed open/closed recollement of
prop-sf-open-closed-triangle-all-stages. Identify its open and closed terms with
those of the operation datum by uniqueness of the adjoints to the recorded
completed pullbacks. The adjunction isomorphisms carry the counit and unit to
exactly the datum's counit and unit. Conjugate the source triangle by these
isomorphisms and the full constructible inclusion. Shifted Hom groups from the
open term to the closed term vanish by recollement orthogonality. TR3 and Hom
exactness then give uniqueness of the third arrow and its naturality in every
input morphism. This also applies when either stratum is empty. -/
theorem sfPackageIntegralRecollementSource
    {Z U X : SixFunctorSpace D}
    [IsSeparated X.obj.hom]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i.hom.left]
    (hj : IsOpenImmersion j.hom.left)
    (hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ) :
    ∃ d : (S.higher.integral.pull i ⋙ S.higher.integral.direct i) ⋙
        (sfIntegralConstructible C.l E X.obj.left).ι ⟶
      ((S.higher.integral.pull j ⋙ S.higher.integral.openExtension j hj) ⋙
        (sfIntegralConstructible C.l E X.obj.left).ι) ⋙ shiftFunctor _ (1 : ℤ),
      ∀ K : sfIntegralConstructibleCategory C.l E X.obj.left,
        (Triangle.mk
          ((sfIntegralConstructible C.l E X.obj.left).ι.map
            ((S.higher.integral.openAdjunction j hj).counit.app K))
          ((sfIntegralConstructible C.l E X.obj.left).ι.map
            ((S.higher.integral.pullDirectAdjunction i).unit.app K))
          (d.app K) ∈ distTriang _) ∧
        ∀ d', Triangle.mk
          ((sfIntegralConstructible C.l E X.obj.left).ι.map
            ((S.higher.integral.openAdjunction j hj).counit.app K))
          ((sfIntegralConstructible C.l E X.obj.left).ι.map
            ((S.higher.integral.pullDirectAdjunction i).unit.app K))
          d' ∈ distTriang _ → d' = d.app K := by
  classical
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  let P : SfRecollementPresentation (sfIntegralConstructibleCategory C.l E X.obj.left) :=
    ⟨S.higher.integral.pull j ⋙ S.higher.integral.openExtension j hj,
      S.higher.integral.pull i ⋙ S.higher.integral.direct i,
      (S.higher.integral.openAdjunction j hj).counit,
      (S.higher.integral.pullDirectAdjunction i).unit⟩
  let I := (sfIntegralConstructible C.l E X.obj.left).ι
  obtain ⟨ht, ho⟩ := integral_normalized C.l E i.hom.left
    (sfRecollementNoetherian D.k X.obj.left) P
    (sfPackageIntegralRecollementNormalization S i j hj hij)
  have htI (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
      ∃ δ, Triangle.mk (I.map (P.counit.app K)) (I.map (P.unit.app K)) δ ∈
        distTriang _ := by
    obtain ⟨δ, hδ⟩ := ht K
    exact ⟨I.map δ ≫ (I.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj K),
      I.map_distinguished _ hδ⟩
  have hoI (K L : sfIntegralConstructibleCategory C.l E X.obj.left) :
      Subsingleton ((I.obj (P.openTerm.obj K))⟦(1 : ℤ)⟧ ⟶
        I.obj (P.closedTerm.obj L)) := by
    let e := Iso.homCongr ((I.commShiftIso (1 : ℤ)).symm.app (P.openTerm.obj K))
      (Iso.refl (I.obj (P.closedTerm.obj L)))
    have h := ho K L (1 : ℤ)
    refine ⟨fun f g ↦ e.injective ?_⟩
    rw [← I.map_preimage (e f), ← I.map_preimage (e g)]
    exact congrArg I.map (@Subsingleton.elim _ h _ _)
  have hu (K : sfIntegralConstructibleCategory C.l E X.obj.left)
      (δ : I.obj (P.closedTerm.obj K) ⟶ (I.obj (P.openTerm.obj K))⟦(1 : ℤ)⟧)
      (hδ : Triangle.mk (I.map (P.counit.app K)) (I.map (P.unit.app K)) δ ∈
        distTriang _) :
      ∀ δ', Triangle.mk (I.map (P.counit.app K)) (I.map (P.unit.app K)) δ' ∈
        distTriang _ → δ' = δ := by
    exact (triangle_morphism_extension _ _ hδ hδ (𝟙 (I.obj K))).2.2 (hoI K K)
  let d : P.closedTerm ⋙ I ⟶ (P.openTerm ⋙ I) ⋙ shiftFunctor _ (1 : ℤ) :=
    { app := fun K ↦ (htI K).choose
      naturality := by
        intro K L f
        obtain ⟨τ, _, _, _, hc⟩ :=
          ((triangle_morphism_extension _ _ (htI K).choose_spec (htI L).choose_spec
            (I.map f)).2.1 (hoI K L)).2.2
            (I.map (P.openTerm.map f)) (I.map (P.closedTerm.map f))
            (by
              change I.map (P.openTerm.map f) ≫ I.map (P.counit.app L) =
                I.map (P.counit.app K) ≫ I.map f
              simpa only [Functor.map_comp, Functor.id_map] using
                congrArg I.map (P.counit.naturality f))
            (by
              change I.map (P.unit.app K) ≫ I.map (P.closedTerm.map f) =
                I.map f ≫ I.map (P.unit.app L)
              simpa only [Functor.map_comp, Functor.id_map] using
                congrArg I.map (P.unit.naturality f).symm)
        exact hc.symm }
  exact ⟨d, fun K ↦ ⟨(htI K).choose_spec,
    hu K (d.app K) (htI K).choose_spec⟩⟩

end WeilConjectures
