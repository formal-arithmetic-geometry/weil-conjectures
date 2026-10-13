/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale

/-!
# Finite étale covers as finite locally constant sheaves

Source: Stacks Project, Tags 03RV, 03Q1, 00Y6 and 09ZB
(blueprint: thm-galois-lc-etale).
The torsor construction and its converse are the existing `EtaleTorsor.toSheafTorsor`
and `EtaleTorsor.exists_toSheafTorsor_equiv_of_iso`; the theorem supplies the missing
categorical equivalence and its natural compatibilities.
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The Yoneda equivalence, with base change and stalk compatibility.
Source: Stacks Project, Tags 03RV, 03Q1, 00Y6 and 09ZB
(blueprint: thm-galois-lc-etale).

Proof: `lem-galois-flc-representable` makes the sheaf of sections finite locally
constant and gives every such sheaf a finite étale representative. Yoneda
(`lem-galois-yoneda-fully-faithful`) gives full faithfulness, so this is an equivalence.
`lem-galois-inverse-image-representable` identifies its base change naturally.
`lem-galois-stalk-representable` identifies its stalk with the geometric fibre.
Naturality intertwines every finite group action, including simply transitive ones.
For torsors, `lem-galois-etale-torsor-sheaf-torsor` supplies the existing construction
`EtaleTorsor.toSheafTorsor` and the converse `exists_toSheafTorsor_equiv_of_iso`:
the locally constant group section acts on each of its open constant-value fibres.
The simply transitive map is carried to the corresponding sheaf map; local
nonemptiness is surjectivity of the cover. Conversely the action descends by Yoneda,
and the torsor map is an isomorphism since its sheaf map is an isomorphism. -/
theorem exists_finiteEtale_flc_equivalence (Y : Scheme.{v}) :
    ∃ Φ : Y.FiniteEtale ≌ Y.FLC,
      Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
      (∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙
            (pointSmallEtale s).sheafFiber (A := Type (v + 1)) ≅
          FiniteEtale.fiber s ⋙ CategoryTheory.forget FintypeCat.{v} ⋙ uliftFunctor.{v + 1, v})) ∧
      (∀ (X : Scheme.{v}) (f : X ⟶ Y), ∃ Ψ : X.FiniteEtale ≌ X.FLC,
        Nonempty (Ψ.functor ⋙ ObjectProperty.ι _ ≅
          ObjectProperty.ι _ ⋙ X.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙ etaleSetPullback f ≅
          FiniteEtale.pullback f ⋙ Ψ.functor ⋙ ObjectProperty.ι _)) := by
  classical
  have hobj (T : Scheme.{v}) (P : T.FiniteEtale) :
      IsFiniteLocallyConstantSheafOfTypes
        ((T.smallEtaleTopology.uliftYoneda.{v + 1}).obj P.obj) := by
    have : IsFinite P.obj.hom := P.property
    obtain ⟨hs, hfin⟩ :=
      (isFiniteLocallyConstant_yoneda_and_exists_iso T).1 P.obj.left P.obj.hom
    exact hfin
  let H (T : Scheme.{v}) : T.FiniteEtale ⥤ T.FLC :=
    ObjectProperty.lift _
      (ObjectProperty.ι _ ⋙ T.smallEtaleTopology.uliftYoneda.{v + 1}) (hobj T)
  have heq (T : Scheme.{v}) : (H T).IsEquivalence := by
    have : (H T).EssSurj := ⟨fun E ↦ by
      obtain ⟨P, π, hπ, hEt, ⟨e⟩⟩ :=
        (isFiniteLocallyConstant_yoneda_and_exists_iso T).2 E.obj E.property
      let Q : T.FiniteEtale := ⟨Etale.mk π, hπ⟩
      refine ⟨Q, ⟨?_⟩⟩
      exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e.symm)⟩
    exact { faithful := inferInstance, full := inferInstance }
  let Φ := (H Y).asEquivalence
  refine ⟨Φ, ⟨Iso.refl _⟩, ?_, ?_⟩
  · intro Ω _ _ s
    let p := pointSmallEtale s
    let e : Y.smallEtaleTopology.uliftYoneda.{v + 1} ⋙
        p.sheafFiber (A := Type (v + 1)) ≅ p.fiber ⋙ uliftFunctor.{v + 1, v} :=
      Functor.isoWhiskerLeft Y.smallEtaleTopology.uliftYoneda
        (p.uliftSheafFiberIso (Type (v + 1))).symm ≪≫
      Functor.isoWhiskerRight uliftYonedaIsoShrinkYoneda
        p.ulift.{v + 1}.presheafFiber ≪≫
      p.ulift.{v + 1}.shrinkYonedaCompPresheafFiberIso
    exact ⟨Functor.isoWhiskerLeft (ObjectProperty.ι _) e⟩
  · intro X f
    let Ψ := (H X).asEquivalence
    refine ⟨Ψ, ⟨Iso.refl _⟩, ?_⟩
    obtain ⟨e⟩ := AlgebraicGeometry.nonempty_inverseImage_representable_iso.{v, v + 1} f
      (etaleSetPullback f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous f.Etale
        (Type (v + 1)) Y.smallEtaleTopology X.smallEtaleTopology)
    exact ⟨Functor.isoWhiskerLeft (ObjectProperty.ι _) e⟩

/-- The Yoneda equivalence carries a finite abelian torsor and its action to its sheaf torsor.
Source: Stacks Project, proof of Tag 09ZB, with Tag 03RV
(blueprint: thm-galois-lc-etale).

Proof: `lem-galois-etale-torsor-sheaf-torsor` constructs `t.toSheafTorsor` on the
representable sheaf. Its simply transitive action and local sections are the fields
of this existing torsor. The Yoneda comparison identifies the image of `t` with that
sheaf, and naturality at each action morphism identifies the actions. Thus the
simply transitive action is carried to the same simply transitive sheaf action. -/
theorem finiteEtale_flc_preserves_torsors {Y : Scheme.{v}}
    (Φ : Y.FiniteEtale ≌ Y.FLC)
    (α : Φ.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) :
    ∀ (M : Type (v + 1)) [AddCommGroup M] [Finite M] (t : EtaleTorsor M Y),
      ∃ ε : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj ≅ t.toSheafTorsor.sheaf,
        ε = α.app ⟨t.toEtale, t.isFinite⟩ ∧
        ∀ (U : Y.Etale) (m : M)
          (x : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj.obj.obj (op U)),
          ε.hom.hom.app (op U)
            ((Φ.functor.map (ObjectProperty.homMk
              (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)))).hom.hom.app (op U) x) =
            ⟨(ε.hom.hom.app (op U) x).down ≫
              MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)⟩ := by
  intro M _ _ t
  refine ⟨α.app ⟨t.toEtale, t.isFinite⟩, rfl, ?_⟩
  intro U m x
  let P : Y.FiniteEtale := ⟨t.toEtale, t.isFinite⟩
  let g : P ⟶ P := ObjectProperty.homMk
    (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m))
  have h := α.hom.naturality g
  exact congrArg (fun f ↦ f.hom.app (op U) x) h

end AlgebraicGeometry.Scheme
