/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker F1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Invariants
public import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import Sheaf.AlgebraicGeometry.SepClosedEtalePointComparison
import Sheaf.CategoryTheory.ScalarStalkTransport
import Sheaf.AlgebraicGeometry.FieldModuleSectionsInvariants
import Sheaf.FieldTheory.GaloisAutomorphismExtension

/-!
# Etale modules on a field and discrete Galois modules

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-exc-field-discrete-modules.md`,
node `lem-exc-field-discrete-modules` (blueprint: lem-exc-field-discrete-modules).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] IsSepClosure.sep_closed in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- (blueprint: lem-exc-field-discrete-modules)
Let `K` be a field with separable closure `Ks`, `G = Gal(Ks/K)` with its Krull topology, and
`A` a finite commutative ring. The geometric fibre functor at the geometric point
`Spec Ks → Spec K` is an equivalence `E` from etale `A`-module sheaves on `Spec K` to discrete
continuous `A[G]`-modules: `i` identifies the underlying `A`-module of `E F` naturally with
the geometric stalk of `F`, and the `G`-action of `E F` is the Galois action on the stalk
(a germ represented at a lift `x` is sent by `g` to the same section at `x ∘ Spec g`).
The section functor at `Spec K` corresponds to the invariants functor (`σ`). An equivalence
of abelian categories is exact.

Proof:
1. Apply the abelian-sheaf equivalence at the algebraic closure of Ks. Enhance
it to modules by transporting the scalar endomorphisms through that additive
fully faithful equivalence. Naturality for scalar maps makes the stalk comparison
A-linear, and the comparison preserves the action formula on germs.
2. The set-valued sections-invariants theorem at the bottom intermediate field,
combined with the module/underlying-set stalk comparison, gives a natural linear
isomorphism from terminal sections to the invariant submodule.
3. Extending the separably closed field Ks to its algebraic closure does not change
etale lifts or stalks. Compose with this stalk comparison. Extend each Galois
automorphism to the algebraic closure, compare the changed lifts there, and apply
the comparison's formula on germs to obtain exactly the asserted action at Ks.
Source: Stacks Project, Tags 04JQ, 04JM, 03QW and 04FN. -/
theorem etaleModuleSheaves_equiv_discreteGModules
    (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
    (A : Type v) [CommRing A] [Finite A] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ks))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let D := Rep.DiscreteContinuousRep.{v, u, max (u + 1) v} A G
    let U : D ⥤ Rep.{max (u + 1) v} A G := ObjectProperty.ι _
    ∃ (E : Sheaf J (ModuleCat.{max (u + 1) v} A) ≌ D)
      (i : E.functor ⋙ U ⋙ Rep.RepToAction A G ⋙
          Action.forget (ModuleCat.{max (u + 1) v} A) G ≅ p.sheafFiber)
      (_σ : (sheafSections J (ModuleCat.{max (u + 1) v} A)).obj (op (Etale.mk (𝟙 S))) ≅
          E.functor ⋙ U ⋙ Rep.invariantsFunctor A G),
      ∀ (F : Sheaf J (ModuleCat.{max (u + 1) v} A)) (g : G)
          (X : S.Etale) (x x' : p.fiber.obj X)
          (_hx : x'.left = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (i.hom.app F) ((E.functor.obj F).obj.ρ g
          ((i.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z := by
  classical
  dsimp only
  let Ω := AlgebraicClosure Ks
  let : IsAlgClosed Ω := inferInstanceAs (IsAlgClosed (AlgebraicClosure Ks))
  let : IsSepClosed Ω := IsSepClosed.of_isAlgClosed Ω
  let : Algebra.IsAlgebraic K Ks := IsSepClosure.separable.isAlgebraic
  let : Algebra.IsAlgebraic Ks Ω := AlgebraicClosure.isAlgebraic Ks
  let : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K Ks Ω
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))
  let q := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let β := CommRingCat.ofHom (algebraMap Ks Ω)
  have hβ : Spec.map β ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ks)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [← Spec.map_comp]
    congr 1
  let b := sepClosedEtaleStalkIso _ _ β hβ (ModuleCat.{max (u + 1) v} A)
  let c := sepClosedEtaleFiberIso _ _ β hβ
  obtain ⟨Eab, _, iab, _, _, hiab, _⟩ :=
    abelianSheaves_equiv_discreteGModules.{u, v} K Ks Ω
  obtain ⟨E, iΩ, hiΩ⟩ := CategoryTheory.ScalarObject.scalarStalkTransport
    (Spec (.of K)).smallEtaleTopology q (Gal(Ks/K)) A Eab iab
  let i := iΩ ≪≫ b.symm
  have haction := fun F g τ hτ X x x' hx z ↦
    hiΩ F g X x x' z
      (hiab ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v} A)
        AddCommGrpCat)).obj F) g τ hτ X x x' hx z)
  obtain ⟨σ⟩ := nonempty_iso_etaleModuleSections_invariants K Ks Ω A E iΩ haction
  refine ⟨E, i, σ, ?_⟩
  intro F g X x x' hx z
  obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
  have hxΩ : (c.hom.app X x').left =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (c.hom.app X x).left := by
    change Spec.map β ≫ x'.left =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (Spec.map β ≫ x.left)
    have hm : Spec.map β ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Spec.map β := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom hτ)
    rw [hx, ← Category.assoc, hm, Category.assoc]
  have hgerm (y : p.fiber.obj X) :
      (b.hom.app F) (p.toPresheafFiber X y F.obj z) =
        q.toPresheafFiber X (c.hom.app X y) F.obj z :=
    ConcreteCategory.congr_hom
      (sepClosedEtaleStalkIso_germ _ _ β hβ (ModuleCat.{max (u + 1) v} A) F X y) z
  have ha := hiΩ F g X (c.hom.app X x) (c.hom.app X x') z
    (hiab ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v} A)
      AddCommGrpCat)).obj F) g τ hτ X _ _ hxΩ z)
  apply (ConcreteCategory.bijective_of_isIso (b.hom.app F)).1
  change (b.hom.app F) ((b.inv.app F) ((iΩ.hom.app F)
    ((E.functor.obj F).obj.ρ g ((iΩ.inv.app F)
      ((b.hom.app F) (p.toPresheafFiber X x F.obj z)))))) = _
  rw [b.inv_hom_id_app_apply, hgerm, ha, hgerm]

end AlgebraicGeometry.Scheme
