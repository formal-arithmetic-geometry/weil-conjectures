/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.RingIsoOrdinaryCoherence
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
import Sheaf.Algebra.Homology.MonoidalComplexComparison

/-! # Tensor coherence of coefficient restriction on cochain complexes

Source: Stacks Project, Tags 03EK and 06YP. Check each degree on the tensor summands.

(blueprint: lem-pur-u2-chain-restriction-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.RingIsoTransport
attribute [local irreducible] SheafOfModules.monoidalCategory
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)]

omit [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
private theorem gradedTensor (A : Sheaf J CommRingCat.{r})
    (X Y : GradedObject ℤ (scalarModules J A)) : X.HasTensor Y := inferInstance
omit [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem gradedFour (A : Sheaf J CommRingCat.{r})
    (X Y Z W : GradedObject ℤ (scalarModules J A)) :
    GradedObject.HasTensor₄ObjExt X Y Z W := inferInstance
omit [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem gradedLeft (A : Sheaf J CommRingCat.{r})
    (X Y Z : GradedObject ℤ (scalarModules J A)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
omit [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem gradedRight (A : Sheaf J CommRingCat.{r})
    (X Y Z : GradedObject ℤ (scalarModules J A)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
omit [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem tensorEmptyLeft (A : Sheaf J CommRingCat.{r}) (X : scalarModules J A) :
    PreservesColimit (Functor.empty.{0} (scalarModules J A))
      ((curriedTensor (scalarModules J A)).obj X) := inferInstance
omit [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (scalarModules J R)] in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem tensorEmptyRight (A : Sheaf J CommRingCat.{r}) (X : scalarModules J A) :
    PreservesColimit (Functor.empty.{0} (scalarModules J A))
      ((curriedTensor (scalarModules J A)).flip.obj X) := inferInstance
attribute [local instance] gradedTensor gradedFour gradedLeft gradedRight
  tensorEmptyLeft tensorEmptyRight

/-- The canonical strong structure on termwise coefficient restriction, with its
instance arguments cached behind a named definition.
Source: literature/stacks-project/sites-modules.tex;
literature/stacks-project/sites-cohomology.tex; Tags 03D7, 03EK and 06YP; ordinary and termwise
tensor comparison coherence.
(blueprint: lem-pur-u2-chain-restriction-coherence). -/
@[instance_reducible]
def cochainMonoidal {R S : Sheaf J CommRingCat.{r}} (a : R ≅ S)
    (o : RingIsoTensorTransport a.symm) :
    let : (scalarRestriction a.inv).Monoidal := o.monoidal.toMonoidal
    let : (scalarRestriction a.inv).IsEquivalence :=
      o.functor_eq ▸ o.equivalence.isEquivalence_functor
    ((scalarRestriction a.inv).mapHomologicalComplex (.up ℤ)).Monoidal := by
  let : (scalarRestriction a.inv).Monoidal := o.monoidal.toMonoidal
  let : (scalarRestriction a.inv).IsEquivalence :=
    o.functor_eq ▸ o.equivalence.isEquivalence_functor
  exact Functor.mapCochainComplexMonoidal (scalarRestriction a.inv)

/-- The identity comparison on complexes is monoidal: its degree-zero unit equation
is the ordinary equation, and each tensor summand is the ordinary tensor equation.
Source: literature/stacks-project/sites-modules.tex;
literature/stacks-project/sites-cohomology.tex; Tags 03D7, 03EK and 06YP; ordinary and termwise
tensor comparison coherence.
(blueprint: lem-pur-u2-chain-restriction-coherence). -/
theorem chainId_monoidal (R : Sheaf J CommRingCat.{r})
    (o : RingIsoTensorTransport (Iso.refl R).symm) :
    let : (scalarRestriction (Iso.refl R).inv).Monoidal := o.monoidal.toMonoidal
    let : (scalarRestriction (Iso.refl R).inv).IsEquivalence :=
      o.functor_eq ▸ o.equivalence.isEquivalence_functor
    let := cochainMonoidal (Iso.refl R) o
    NatTrans.IsMonoidal (chainId R).hom := by
  let F := scalarRestriction (Iso.refl R).inv
  let : F.Braided := o.monoidal
  let : (scalarRestriction (Iso.refl R).inv).IsEquivalence :=
    o.functor_eq ▸ o.equivalence.isEquivalence_functor
  let := Functor.mapCochainComplexMonoidal F
  let : NatTrans.IsMonoidal (ordinaryId R).hom := ordinaryId_monoidal R o
  refine ⟨?_, fun P Q ↦ ?_⟩
  · apply HomologicalComplex.from_single_hom_ext (j := (0 : ℤ))
    simp only [HomologicalComplex.comp_f]
    change F.mapCochainComplexεIso.hom.f 0 ≫ _ = _
    erw [Functor.mapCochainComplexεIso_hom_f_zero]
    change (_ ≫ Functor.LaxMonoidal.ε F ≫ F.map _) ≫
      (ordinaryId R).hom.app _ = 𝟙 _
    rw [Category.assoc, Category.assoc, (ordinaryId R).hom.naturality,
      ← Category.assoc (Functor.LaxMonoidal.ε F), NatTrans.IsMonoidal.unit,
      Functor.LaxMonoidal.id_ε, Category.id_comp]
    exact Iso.hom_inv_id _
  · apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simp only [HomologicalComplex.comp_f]
    change HomologicalComplex.ιTensorObj _ _ p q n h ≫
      (F.mapCochainComplexμIso P Q).hom.f n ≫ _ = _
    erw [Functor.ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
    change Functor.LaxMonoidal.μ F (P.X p) (Q.X q) ≫
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (ordinaryId R).hom.app _ = _
    rw [(ordinaryId R).hom.naturality, ← Category.assoc,
      NatTrans.IsMonoidal.tensor]
    erw [CochainComplex.ιTensorObj_tensorHom_f_assoc]
    simp only [Functor.LaxMonoidal.id_μ, Category.comp_id]
    rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Composition of coefficient restrictions on complexes is monoidal. The tensor
assertion is functoriality of the total tensor comparison; its hypothesis is the
ordinary normalized tensor equation. The unit is checked in degree zero.
Source: literature/stacks-project/sites-modules.tex;
literature/stacks-project/sites-cohomology.tex; Tags 03D7, 03EK and 06YP; ordinary and termwise
tensor comparison coherence.
(blueprint: lem-pur-u2-chain-restriction-coherence). -/
theorem chainComp_monoidal {R S T : Sheaf J CommRingCat.{r}}
    (a : R ≅ S) (b : S ≅ T)
    (oa : RingIsoTensorTransport a.symm) (ob : RingIsoTensorTransport b.symm)
    (oc : RingIsoTensorTransport (a ≪≫ b).symm) :
    let : (scalarRestriction a.inv).Monoidal := oa.monoidal.toMonoidal
    let : (scalarRestriction b.inv).Monoidal := ob.monoidal.toMonoidal
    let : (scalarRestriction (a ≪≫ b).inv).Monoidal := oc.monoidal.toMonoidal
    let : (scalarRestriction a.inv).IsEquivalence :=
      oa.functor_eq ▸ oa.equivalence.isEquivalence_functor
    let : (scalarRestriction b.inv).IsEquivalence :=
      ob.functor_eq ▸ ob.equivalence.isEquivalence_functor
    let : (scalarRestriction (a ≪≫ b).inv).IsEquivalence :=
      oc.functor_eq ▸ oc.equivalence.isEquivalence_functor
    let := cochainMonoidal a oa
    let := cochainMonoidal b ob
    let := cochainMonoidal (a ≪≫ b) oc
    NatTrans.IsMonoidal (chainComp a b).hom := by
  let F := scalarRestriction a.inv
  let G := scalarRestriction b.inv
  let H := scalarRestriction (a ≪≫ b).inv
  let : F.Monoidal := oa.monoidal.toMonoidal
  let : G.Monoidal := ob.monoidal.toMonoidal
  let : H.Monoidal := oc.monoidal.toMonoidal
  let : (scalarRestriction a.inv).IsEquivalence :=
    oa.functor_eq ▸ oa.equivalence.isEquivalence_functor
  let : (scalarRestriction b.inv).IsEquivalence :=
    ob.functor_eq ▸ ob.equivalence.isEquivalence_functor
  let : (scalarRestriction (a ≪≫ b).inv).IsEquivalence :=
    oc.functor_eq ▸ oc.equivalence.isEquivalence_functor
  let := Functor.mapCochainComplexMonoidal F
  let := Functor.mapCochainComplexMonoidal G
  let := Functor.mapCochainComplexMonoidal H
  let : NatTrans.IsMonoidal (ordinaryComp a b).hom := ordinaryComp_monoidal a b oa ob oc
  exact Functor.mapCochainComplexCompIso_monoidal F G H (ordinaryComp a b)

end SheafOfModules.RingIsoTransport
