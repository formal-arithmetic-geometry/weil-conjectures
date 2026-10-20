/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.GaloisStalkActionFunctor
import Sheaf.AlgebraicGeometry.GaloisStalkActionFullyFaithful
import Sheaf.AlgebraicGeometry.GaloisStalkActionEssSurj
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension

/-!
# Étale sheaves and discrete Galois sets

Source: Stacks Project, Tag 03QT and the Galois action on stalks in Tag 03QW
(blueprint: lem-exc-etale-sheaves-gsets-point).
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory
open AlgebraicGeometry
open Opposite

namespace AlgebraicGeometry

private theorem representable_germ_bijective
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (X : (Spec (.of K)).Etale) :
    let p := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    let F := (Spec (.of K)).smallEtaleTopology.uliftYoneda.{v + 1}.obj X
    Function.Bijective (fun x : p.fiber.obj X ↦
      p.toPresheafFiber X x F.obj (ULift.up (𝟙 X))) := by
  dsimp only
  let p := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let F := (Spec (.of K)).smallEtaleTopology.uliftYoneda.{v + 1}.obj X
  let W := Type (max u (v + 1))
  let η (x : p.fiber.obj X) := p.toPresheafFiber X x F.obj (ULift.up (𝟙 X))
  let φ (Y : (Spec (.of K)).Etale) (y : p.fiber.obj Y) :
      F.obj.obj (op Y) ⟶ ULift.{v + 1} (p.fiber.obj X) :=
    ↾fun z ↦ ULift.up (p.fiber.map z.down y)
  have hφ : ∀ ⦃Y Z : (Spec (.of K)).Etale⦄ (f : Y ⟶ Z) (y : p.fiber.obj Y),
      F.obj.map f.op ≫ φ Y y = φ Z (p.fiber.map f y) := by
    intro Y Z f y
    ext z
    change p.fiber.map (f ≫ z.down) y = p.fiber.map z.down (p.fiber.map f y)
    rw [Functor.map_comp]
    rfl
  let ψ := p.presheafFiberDesc φ hφ
  have hleft (x : p.fiber.obj X) : ψ (η x) = ULift.up x := by
    change (p.toPresheafFiber X x F.obj ≫ ψ) (ULift.up (𝟙 X)) = ULift.up x
    rw [p.toPresheafFiber_presheafFiberDesc φ hφ X x]
    change ULift.up (p.fiber.map (𝟙 X) x) = ULift.up x
    rw [p.fiber.map_id]
    rfl
  constructor
  · intro x x' hh
    have h := congrArg ψ hh
    rw [hleft, hleft] at h
    exact congrArg ULift.down h
  · intro z
    obtain ⟨Y, y, t, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := F.obj) z
    refine ⟨p.fiber.map t.down y, ?_⟩
    have hm : F.obj.map t.down.op (ULift.up (𝟙 X)) = t := by
      change ULift.up (t.down ≫ 𝟙 X) = t
      simp only [Category.comp_id, ULift.up_down]
    exact (p.toPresheafFiber_w_apply t.down y F.obj
      (carrier := fun Z : W ↦ Z) (ULift.up (𝟙 X))).symm.trans
        (congrArg (p.toPresheafFiber Y y F.obj) hm)

/-
The theorem packages the two assertions of the node. `DiscreteContAction` (with the
discrete topology on sets from `etaleFieldDiscreteForget₂`, as in `etaleFieldGsets`) is the
category of `Gal(Ksep/K)`-sets with every stabilizer open for the Krull topology.
-/
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
(blueprint: lem-exc-etale-sheaves-gsets-point) Let `K` be a field, let `Ksep`
be a separable closure embedded in an algebraic closure `Ω` of `K`, and let
`s : Spec Ω ⟶ Spec K` be the corresponding geometric point.  Étale sheaves on
`Spec K` are equivalent, via the stalk at `s`, to discrete continuous actions
of `Gal(Ksep/K)`, and the stalk of the representable sheaf of an étale scheme
`X` is naturally `Hom_K(Spec Ksep, X)`.

The proof follows the four steps of the DAG node, using Stacks Tags 03QW and 03QT.
1. Represent germs by pointed-neighbourhood triples
   (`def-weil-pbc-geometric-stalks`) and change the lift by an extension of the
   Galois automorphism. Finite separable residue fields
   (`lem-weil-pbc-etale-fibre-discrete-separable-points`) give independence of
   that extension and an open subgroup contained in each stabilizer.
2. Representables are sheaves (`lem-weil-pbc-small-etale-representable-presheaf-sheaf`).
   Evaluate their stalks (`lem-galois-stalk-representable`), and use the finite
   separable components (`lem-weil-pbc-etale-fibre-discrete-separable-points`)
   to identify Omega-points with Ksep-points, naturally and equivariantly.
3. Sections over finite separable extensions are stabilizer invariants
   (`lem-exc-field-sections-stalk-invariants`), compatibly with embeddings.
   The component decomposition (`lem-weil-pbc-etale-fibre-discrete-separable-points`)
   and the sheaf condition give sections as products. Equivariant stalk maps
   therefore reconstruct sheaf morphisms, proving full faithfulness.
4. Realize each discrete Galois set by an etale scheme
   (`lem-exc-etale-field-gsets`). Step 2 gives its representable sheaf the
   required stalk, proving essential surjectivity and hence the equivalence.
-/
theorem etaleSheavesGsetsPoint
    (K Ksep Ω : Type u)
    [Field K] [Field Ksep] [Field Ω]
    [Algebra K Ksep] [Algebra K Ω]
    [IsSepClosure K Ksep] [IsAlgClosed Ω] [IsAlgClosure K Ω]
    (i : Ksep →ₐ[K] Ω) :
    ∃ E : Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
        (Type (max u (v + 1))) ≌
        DiscreteContAction (Type (max u (v + 1))) (Gal(Ksep / K)),
      ∃ η : E.functor ⋙
            forget₂ (DiscreteContAction (Type (max u (v + 1))) (Gal(Ksep / K)))
              (Type (max u (v + 1))) ≅
          (Scheme.pointSmallEtale
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber,
      (∀ (F : Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
            (Type (max u (v + 1))))
          (X : (Scheme.Spec.obj (op (.of K))).Etale)
          (l l' : Scheme.Spec.obj (op (.of Ω)) ⟶ X.left)
          (h : l ≫ X.hom = Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)
          (h' : l' ≫ X.hom = Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)
          (g : Gal(Ksep / K)) (τ : Ω ≃ₐ[K] Ω)
          (_hτ : τ.toAlgHom.comp i = i.comp g.toAlgHom)
          (_hl : l' = Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op ≫ l)
          (t : F.obj.obj (op X)),
        (η.hom.app F)
          (((E.functor.obj F).obj.obj.ρ g)
            ((η.inv.app F) ((Scheme.pointSmallEtale
              (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).toPresheafFiber
                X (Over.homMk l h) F.obj t))) =
          (Scheme.pointSmallEtale
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).toPresheafFiber
              X (Over.homMk l' h') F.obj t) ∧
      ∃ e : ∀ (X : (Scheme.Spec.obj (op (.of K))).Etale),
          ((Scheme.pointSmallEtale
              (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber.obj
                (((Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X) :
                  Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                    (Type (max u (v + 1))))) ≃
            {f : Scheme.Spec.obj (op (.of Ksep)) ⟶ X.left //
              f ≫ X.hom = Scheme.Spec.map
                (CommRingCat.ofHom (algebraMap K Ksep)).op},
        (∀ (X : (Scheme.Spec.obj (op (.of K))).Etale)
          (g : Gal(Ksep / K))
            (x : (Scheme.pointSmallEtale
              (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber.obj
                (((Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X) :
                  Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                    (Type (max u (v + 1))))),
            ((e X) ((η.hom.app ((Scheme.smallEtaleTopology
              (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X :
                Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                  (Type (max u (v + 1)))))
                (((E.functor.obj ((Scheme.smallEtaleTopology
                  (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X)).obj.obj.ρ g)
                  (η.inv.app ((Scheme.smallEtaleTopology
                  (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X :
                    Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                      (Type (max u (v + 1)))) x)))).val =
              Scheme.Spec.map (CommRingCat.ofHom g.toRingHom).op ≫ ((e X) x).val) ∧
        ∀ (X Y : (Scheme.Spec.obj (op (.of K))).Etale) (f : X ⟶ Y)
          (x : (Scheme.pointSmallEtale
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber.obj
              (((Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K)))).uliftYoneda.obj X) :
                Sheaf (Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K))))
                  (Type (max u (v + 1))))),
          ((e Y) ((Scheme.pointSmallEtale
            (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K Ω)).op)).sheafFiber.map
              ((Scheme.smallEtaleTopology (Scheme.Spec.obj (op (.of K)))).uliftYoneda.map f)
              x)).val = ((e X) x).val ≫ f.left := by
  classical
  let : Algebra Ksep Ω := i.toAlgebra
  have : IsScalarTower K Ksep Ω :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (i.commutes a).symm)
  obtain ⟨T, j, hj⟩ := Scheme.exists_galoisStalkActionFunctor.{u, v + 1} K Ksep Ω
  have hff := Scheme.galoisStalkActionFunctor_full_faithful.{u, v + 1} K Ksep Ω T j hj
  let := hff.1
  let := hff.2
  let := Scheme.galoisStalkActionFunctor_essSurj.{u, v + 1} K Ksep Ω T j hj
  let : T.IsEquivalence := {}
  refine ⟨T.asEquivalence, j, ?_, ?_⟩
  · intro F X l l' h h' g τ hτ hl t
    exact hj F g τ (congrArg AlgHom.toRingHom hτ.symm)
      X (Over.homMk l h) (Over.homMk l' h') hl t
  · let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let p := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    let sk := Spec.map (CommRingCat.ofHom (algebraMap K Ksep))
    let β := CommRingCat.ofHom i.toRingHom
    have ht : Spec.map β ≫ sk =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [← Spec.map_comp]
      congr 1
      ext t
      exact i.commutes t
    let P (X : S.Etale) :=
      {f : Spec (.of Ksep) ⟶ X.left // f ≫ X.hom = sk}
    let q (X : S.Etale) (y : P X) : p.fiber.obj X :=
      Over.homMk (Spec.map β ≫ y.val) (by
        change (Spec.map β ≫ y.val) ≫ X.hom = _
        rw [Category.assoc, y.property]
        exact ht)
    have hq (X : S.Etale) : Function.Bijective (q X) := by
      have : IsSepClosed Ksep := IsSepClosure.sep_closed K
      constructor
      · intro y y' hh
        apply Subtype.ext
        exact Scheme.SpecMap_comp_injective β (congrArg Over.Hom.left hh)
      · intro x
        obtain ⟨y, hy, hw⟩ := X.hom.exists_SpecMap_comp_eq_of_isSepClosed
          β sk x.left (by exact x.w.trans ht.symm)
        refine ⟨⟨y, hw⟩, ?_⟩
        apply Over.OverMorphism.ext
        exact hy
    let a (X : S.Etale) : p.fiber.obj X ≃ p.sheafFiber.obj (J.uliftYoneda.{v + 1}.obj X) :=
      Equiv.ofBijective _ (representable_germ_bijective.{u, v} K Ω X)
    let b (X : S.Etale) : P X ≃ p.fiber.obj X := Equiv.ofBijective (q X) (hq X)
    let e (X : S.Etale) := (a X).symm.trans (b X).symm
    have he (X : S.Etale) (x : p.sheafFiber.obj (J.uliftYoneda.{v + 1}.obj X)) :
        a X (q X (e X x)) = x := by
      change a X (b X ((b X).symm ((a X).symm x))) = x
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine ⟨e, ?_, ?_⟩
    · intro X g x
      let y := e X x
      let y' : P X := ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ y.val, by
        rw [Category.assoc, y.property]
        dsimp [sk]
        rw [← Spec.map_comp]
        congr 1
        ext t
        exact g.commutes t⟩
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ksep Ω g
      have hx : (q X y').left =
          Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (q X y).left := by
        change Spec.map β ≫ (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ y.val) =
          Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (Spec.map β ≫ y.val)
        rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        congr 2
        exact congrArg CommRingCat.ofHom hτ
      have hg := hj (J.uliftYoneda.{v + 1}.obj X) g τ hτ X (q X y) (q X y') hx
        (ULift.up (𝟙 X))
      have hy : a X (q X y) = x := he X x
      change (j.hom.app _) ((T.obj _).obj.obj.ρ g
        ((j.inv.app _) (a X (q X y)))) = a X (q X y') at hg
      rw [hy] at hg
      have hval : e X ((j.hom.app _) ((T.obj _).obj.obj.ρ g
          ((j.inv.app _) x))) = y' := by
        apply (b X).injective
        apply (a X).injective
        change a X (q X (e X _)) = a X (q X y')
        rw [he]
        exact hg
      exact congrArg Subtype.val hval
    · intro X Y f x
      let y := e X x
      let y' : P Y := ⟨y.val ≫ f.left, by
        have hf : f.left ≫ Y.hom = X.hom := f.w
        rw [Category.assoc, hf]
        exact y.property⟩
      have hqf : p.fiber.map f (q X y) = q Y y' := by
        apply Over.OverMorphism.ext
        exact Category.assoc _ _ _
      have hnat : p.sheafFiber.map (J.uliftYoneda.{v + 1}.map f) (a X (q X y)) =
          a Y (q Y y') := by
        change p.presheafFiber.map (J.uliftYoneda.{v + 1}.map f).hom
          (p.toPresheafFiber X (q X y) (J.uliftYoneda.{v + 1}.obj X).obj (ULift.up (𝟙 X))) = _
        rw [p.toPresheafFiber_naturality_apply]
        change p.toPresheafFiber X (q X y) (J.uliftYoneda.{v + 1}.obj Y).obj (ULift.up f) = _
        rw [← hqf]
        change p.toPresheafFiber X (q X y) (J.uliftYoneda.{v + 1}.obj Y).obj
          (ULift.up f) = p.toPresheafFiber Y (p.fiber.map f (q X y))
            (J.uliftYoneda.{v + 1}.obj Y).obj (ULift.up (𝟙 Y))
        have hm : (J.uliftYoneda.{v + 1}.obj Y).obj.map f.op (ULift.up (𝟙 Y)) =
            ULift.up f := by
          change ULift.up (f ≫ 𝟙 Y) = ULift.up f
          rw [Category.comp_id]
        have hw := p.toPresheafFiber_w_apply f (q X y) (J.uliftYoneda.{v + 1}.obj Y).obj
          (carrier := fun Z : Type (max u (v + 1)) ↦ Z) (ULift.up (𝟙 Y))
        rw [hm] at hw
        exact hw
      rw [he] at hnat
      have hval : e Y (p.sheafFiber.map (J.uliftYoneda.{v + 1}.map f) x) = y' := by
        apply (b Y).injective
        apply (a Y).injective
        change a Y (q Y (e Y _)) = a Y (q Y y')
        rw [he]
        exact hnat
      exact congrArg Subtype.val hval

end AlgebraicGeometry
