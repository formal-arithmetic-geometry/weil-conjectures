/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-!
# Injective models for global sections with closed pro-etale support

Source: Stacks Project, etale-cohomology.tex, Tags 09XQ and 09XP, with the ordinary
pro-etale module adaptation in the DAG proof
(blueprint: lem-pur-proetale-injective-support-global-model).

Constant-coefficient module sheaves use the published `Sheaf ... (ModuleCat A)`
presentation. The comparison with the intrinsic constant-ring presentation is the
one in `ProEtaleFiniteModules`. The equality of section complexes is expressed by
its natural, inclusion-normalized isomorphism, since the chosen categorical kernels
and the global-section limit need not have definitionally identical carriers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range i) (Set.range j))

attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  finiteClosedUpperShriek

private noncomputable def supportKernelIsKernel
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  isLimitOfHasKernelOfPreservesLimit
    ((evaluation _ _).obj M)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit

set_option linter.unusedSectionVars false in
private theorem supportMap_unit_zero
    (hPair : IsCompl (Set.range i) (Set.range j))
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (f : (lowerStar (ModuleCat.{u + 1} A) i).obj N ⟶ M) :
    f ≫ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M = 0 := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).symm.injective
  have hz := isZero_upperStar_lowerStar_of_disjoint (ModuleCat.{u + 1} A) i j
    hPair.disjoint N
  exact hz.eq_of_src _ _

attribute [local irreducible] supportKernelIsKernel

private noncomputable def supportSheafHomEquiv
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    ((lowerStar (ModuleCat.{u + 1} A) i).obj N ⟶ M) ≃
      (N ⟶ (finiteClosedUpperShriek A i j).obj M) := by
  have := finiteSupportedClosedComparison_isIso A i j hPair
  let q := (asIso (finiteSupportedClosedComparison A i j)).app M
  let e : ((lowerStar (ModuleCat.{u + 1} A) i).obj N ⟶ M) ≃
      ((lowerStar (ModuleCat.{u + 1} A) i).obj N ⟶
        (finiteSupportedSections A j).obj M) :=
    { toFun := fun f ↦ (supportKernelIsKernel A j M).lift
        (KernelFork.ofι f (supportMap_unit_zero A i j hPair N M f))
      invFun := fun f ↦ f ≫ (finiteSupportedSectionsι A j).app M
      left_inv := by
        intro f
        exact (supportKernelIsKernel A j M).fac _ WalkingParallelPair.zero
      right_inv := by
        intro f
        apply Fork.IsLimit.hom_ext (supportKernelIsKernel A j M)
        exact (supportKernelIsKernel A j M).fac _ WalkingParallelPair.zero }
  exact e.trans ((Iso.homCongr (Iso.refl _) q).trans
    (fullyFaithfulLowerStar A i).homEquiv.symm)

private theorem supportSheafHomEquiv_symm
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (f : N ⟶ (finiteClosedUpperShriek A i j).obj M) :
    (supportSheafHomEquiv A i j hPair N M).symm f =
      (lowerStar (ModuleCat.{u + 1} A) i).map f ≫
        (supportModelInclusion A i j hPair).app M := by
  simp [supportSheafHomEquiv, supportKernelIsKernel, Iso.homCongr, supportModelInclusion]

attribute [local irreducible] supportSheafHomEquiv

private noncomputable def supportSheafAdjunction :
    lowerStar (ModuleCat.{u + 1} A) i ⊣ finiteClosedUpperShriek A i j :=
  Adjunction.mkOfHomEquiv
    { homEquiv := supportSheafHomEquiv A i j hPair
      homEquiv_naturality_left_symm := by
        intros
        simp only [supportSheafHomEquiv_symm, Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro N M M' f g
        apply (supportSheafHomEquiv A i j hPair N M').symm.injective
        rw [Equiv.symm_apply_apply, supportSheafHomEquiv_symm, Functor.map_comp,
          Category.assoc]
        change f ≫ g = _ ≫
          (finiteClosedUpperShriek A i j ⋙ lowerStar (ModuleCat.{u + 1} A) i).map g ≫ _
        rw [(supportModelInclusion A i j hPair).naturality g,
          ← Category.assoc, ← supportSheafHomEquiv_symm, Equiv.symm_apply_apply]
        rfl }

attribute [local irreducible] supportSheafAdjunction

private theorem supportSheafAdjunction_counit :
    (supportSheafAdjunction A i j hPair).counit =
      supportModelInclusion A i j hPair := by
  apply NatTrans.ext
  funext M
  simpa [supportSheafAdjunction] using
    supportSheafHomEquiv_symm A i j hPair _ M (𝟙 _)

include hPair in
omit [Finite A] [QuasiCompact j] in
private theorem supportRestriction_zero_iff
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (x : M.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) :
    M.obj.map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance
          trivial).counit.app (Scheme.ProEt.mk (𝟙 X))).op x = 0 ↔
      M.obj.map (supportRestrictionArrow i).op x = 0 := by
  let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
    (Scheme.ProEt.mk (𝟙 X))
  let W := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj V
  let e₀ : W ≅ Scheme.ProEt.mk j :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 X) j)) (by
      rfl)
  have hr : Set.range j = Set.range i.openComplement.ι := by
    simpa [Scheme.Hom.openComplement] using hPair.symm.eq_compl
  let e₁ : Scheme.ProEt.mk j ≅ Scheme.ProEt.mk i.openComplement.ι :=
    MorphismProperty.Over.isoMk (IsOpenImmersion.isoOfRangeEq j i.openComplement.ι hr)
      (IsOpenImmersion.isoOfRangeEq_hom_fac j i.openComplement.ι hr)
  let e := e₀ ≪≫ e₁
  have he : e.hom ≫ supportRestrictionArrow i =
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance
        trivial).counit.app (Scheme.ProEt.mk (𝟙 X)) :=
    (Scheme.ProEt.isTerminalMkId X).hom_ext _ _
  rw [← he, op_comp, M.obj.map_comp]
  change M.obj.map e.hom.op (M.obj.map (supportRestrictionArrow i).op x) = 0 ↔ _
  have hinj := (ModuleCat.mono_iff_injective (M.obj.map e.hom.op)).mp inferInstance
  exact ⟨fun h ↦ hinj (h.trans (map_zero _).symm), fun h ↦ by rw [h]; simp⟩

include hPair in
omit [QuasiCompact j] in
private theorem supportSectionExact
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    Function.Exact
        (((finiteSupportedSectionsι A j).app M).hom.app
          (op (Scheme.ProEt.mk (𝟙 X)))).hom
        (M.obj.map (supportRestrictionArrow i).op).hom ∧
      Function.Injective (((finiteSupportedSectionsι A j).app M).hom.app
        (op (Scheme.ProEt.mk (𝟙 X)))).hom := by
  obtain ⟨hinj, hrange⟩ := finiteSupportedSections_sections A j M
    (Scheme.ProEt.mk (𝟙 X))
  refine ⟨?_, hinj⟩
  intro x
  change M.obj.map (supportRestrictionArrow i).op x = 0 ↔
    x ∈ Set.range (((finiteSupportedSectionsι A j).app M).hom.app _)
  rw [hrange]
  exact (supportRestriction_zero_iff A i j hPair M x).symm

private noncomputable def supportSectionsKernelIso
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    ((finiteSupportedSections A j).obj M).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) ≅
      (supportSections i A).obj M := by
  let b := ((finiteSupportedSectionsι A j).app M).hom.app (op (Scheme.ProEt.mk (𝟙 X)))
  let r := M.obj.map (supportRestrictionArrow i).op
  let h := supportSectionExact A i j hPair M
  let e := (ModuleCat.isLimitKernelFork b r h.1 h.2).conePointUniqueUpToIso
    (kernelIsKernel r)
  exact e

omit [QuasiCompact j] in
private theorem supportSectionsKernelIso_hom_ι
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (supportSectionsKernelIso A i j hPair M).hom ≫
        kernel.ι (M.obj.map (supportRestrictionArrow i).op) =
      ((finiteSupportedSectionsι A j).app M).hom.app (op (Scheme.ProEt.mk (𝟙 X))) := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (ModuleCat.isLimitKernelFork _ _ (supportSectionExact A i j hPair M).1
      (supportSectionExact A i j hPair M).2)
    (kernelIsKernel (M.obj.map (supportRestrictionArrow i).op)) WalkingParallelPair.zero

private noncomputable def supportSectionsKernelNatIso :
    finiteSupportedSections A j ⋙
        (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj
          (op (Scheme.ProEt.mk (𝟙 X))) ≅
      supportSections i A :=
  NatIso.ofComponents (supportSectionsKernelIso A i j hPair) (by
    intro M N f
    apply (cancel_mono (kernel.ι (N.obj.map (supportRestrictionArrow i).op))).1
    dsimp only [Functor.comp_map]
    rw [Category.assoc, supportSectionsKernelIso_hom_ι]
    change _ = (supportSectionsKernelIso A i j hPair M).hom ≫
      kernel.map _ _ (f.hom.app _) (f.hom.app _) (f.hom.naturality _) ≫ _
    rw [kernel.lift_ι, ← Category.assoc, supportSectionsKernelIso_hom_ι]
    exact congrArg (fun α ↦ α.hom.app (op (Scheme.ProEt.mk (𝟙 X))))
      ((finiteSupportedSectionsι A j).naturality f))

private noncomputable def supportGlobalSectionsIso :
    finiteClosedUpperShriek A i j ⋙
        Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ≅ supportSections i A := by
  have := finiteSupportedClosedComparison_isIso A i j hPair
  exact Functor.isoWhiskerLeft _ (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) i).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (finiteSupportedClosedComparison A i j)).symm _ ≪≫
    Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)) ≪≫
    supportSectionsKernelNatIso A i j hPair

/-- The closed supported inverse image is right adjoint to exact closed direct image,
preserves injectives, and computes supported global cohomology on injective models.

The first equality fixes the sheaf counit. The natural isomorphism `c` identifies
`Γ(Z,i^!₀(-))` with the actual kernel-of-restriction functor; its normalization says
that the identification followed by the kernel inclusion is global sections of the
support counit, using `Γ(Z,-) ≅ Γ(X,i_*(-))` and evaluation at the terminal object.
Applying `c` termwise gives the displayed equality of complexes, with the induced
differentials and naturality in every chain map.

The isomorphism `e` is the consequent natural derived comparison. The last equation
normalizes it on every bounded-below injective representative by the three standard
right-derived units. Their invertibility states both model computations. Applying
`DerivedCategory.Plus.homologyFunctor (ModuleCat A) r` to `e` gives the comparison
of cohomology modules in every integer degree, including negative degrees.

Source: Stacks Project, Tags 09XQ (Hom argument) and 09XP (supported sections),
and the ordinary pro-etale adaptation in this node
(blueprint: lem-pur-proetale-injective-support-global-model).

Proof, following the seven steps of the node:
1. On the stated small sites the module-sheaf categories are Grothendieck abelian
by lem-weil-pbc-ring-sheaves-grothendieck, hence have enough injectives by
lem-sp-grothendieck-enough-injectives. All functors here are additive.
2. For N on Z, every map i_*N → M has zero composite with the open adjunction unit,
since j^*i_*N = 0 by lem-weil-pbc-proetale-ringed-open-closed. Factor uniquely through
G_ZM = ker(M → j_*j^*M). The canonical isomorphism q:G_ZM ≅ i_*i^!₀M of
def-pur-flasque-support and full faithfulness of closed direct image from
lem-exc-proetale-closed-fully-faithful give the natural Hom adjunction. Its counit
is q⁻¹ followed by the kernel inclusion, precisely supportModelInclusion.
3. Exactness of i_* and lem-sp-right-adjoint-preserves-injectives imply preservation
of injective objects by i^!₀. Additivity preserves every lower bound. Termwise
application gives the differential i^!₀(d), so its square is zero.
4. Apply lem-weil-pbc-right-derived-plus-injective first to i^!₀ and then to Γ(Z,-).
The first image complex is again bounded below and injective, so both derived units
are invertible. Thus Γ(Z,i^!₀I) computes RΓ(Z,SK).
5. The direct-image formula of def-weil-pbc-proetale-operations identifies sections
on Z with those of i_* on X. The inverse of q identifies the latter with sections
of G_ZI. Its section formula from def-pur-flasque-support is exactly the kernel of
I(X) → I(U), namely def-pur-support-cohomology. This gives c with its displayed
normalization. Naturality of q, restriction, and direct image makes these comparisons
commute with all differentials and all chain maps, without splittings or sign changes.
6. Apply lem-weil-pbc-right-derived-plus-injective to Γ_Z(X,-). Its derived unit
is invertible on I. Invert the first two units, apply the chain identification from
step 5, then apply this third unit; the resulting comparison is e.
7. By lem-weil-pbc-dplus-injective-representative every D⁺ object has such a model.
By lem-weil-pbc-kinjective-hom-derived a derived map is represented by a unique
homotopy class of maps between injective models. Additive functors preserve homotopies;
step 5 commutes with them. Hence e is independent of representatives and lifts and is
natural on D⁺. Apply degree-r cohomology to obtain an isomorphism of A-modules. -/
theorem proEtaleInjectiveSupportGlobalModel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    ∃ adj : lowerStar (ModuleCat.{u + 1} A) i ⊣ finiteClosedUpperShriek A i j,
      adj.counit = supportModelInclusion A i j hPair ∧
      (finiteClosedUpperShriek A i j).PreservesInjectiveObjects ∧
      ∃ c : finiteClosedUpperShriek A i j ⋙
          Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ≅ supportSections i A,
        (∀ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A),
          c.hom.app M ≫ kernel.ι (M.obj.map (supportRestrictionArrow i).op) =
            (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) i).inv.app
                ((finiteClosedUpperShriek A i j).obj M) ≫
              (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
                ((supportModelInclusion A i j hPair).app M) ≫
              (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
                (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M) ∧
        ∃ e : (finiteClosedUpperShriek A i j).rightDerivedFunctorPlus ⋙
            (Sheaf.Γ (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus ≅ derivedSupportSections i A,
          ∀ I : HomotopyCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
            (∀ r : ℤ, Injective (I.obj.as.X r)) →
            (∀ n : ℤ, CochainComplex.IsStrictlyGE I.obj.as n →
              CochainComplex.IsStrictlyGE
                (((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj
                  I.obj.as) n) ∧
            (∀ r : ℤ, Injective
              ((((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj
                I.obj.as).X r)) ∧
            IsIso ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app I) ∧
            IsIso ((Sheaf.Γ (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I)) ∧
            IsIso ((supportSections i A).rightDerivedFunctorPlusUnit.app I) ∧
            (Sheaf.Γ (Scheme.ProEt.topology Z)
                (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I) ≫
              (Sheaf.Γ (Scheme.ProEt.topology Z)
                (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
                ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app I) ≫
              e.hom.app (DerivedCategory.Plus.Qh.obj I) =
              DerivedCategory.Plus.Qh.map
                ((Functor.mapHomotopyCategoryPlusCompIso c).hom.app I) ≫
                (supportSections i A).rightDerivedFunctorPlusUnit.app I := by
  let adj := supportSheafAdjunction A i j hPair
  have hinj : (finiteClosedUpperShriek A i j).PreservesInjectiveObjects :=
    adj.preservesInjectiveObjects_of_preservesFiniteLimits
  refine ⟨adj, supportSheafAdjunction_counit A i j hPair, hinj, ?_⟩
  let c := supportGlobalSectionsIso A i j hPair
  refine ⟨c, ?_, Functor.rightDerivedFunctorPlusCompIso' _ _ c, ?_⟩
  · intro M
    have := finiteSupportedClosedComparison_isIso A i j hPair
    change (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) i).inv.app
        ((finiteClosedUpperShriek A i j).obj M) ≫
      (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        ((asIso (finiteSupportedClosedComparison A i j)).inv.app M) ≫
      (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
        (Scheme.ProEt.isTerminalMkId X)).hom.app ((finiteSupportedSections A j).obj M) ≫
      (supportSectionsKernelIso A i j hPair M).hom ≫
        kernel.ι (M.obj.map (supportRestrictionArrow i).op) = _
    rw [supportSectionsKernelIso_hom_ι]
    dsimp only [supportModelInclusion, NatTrans.comp_app]
    rw [Functor.map_comp, Category.assoc]
    congr 2
    exact ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.naturality
        ((finiteSupportedSectionsι A j).app M)).symm
  · intro I hI
    have himg : ∀ r : ℤ, Injective
        (((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I).obj.as.X r) := by
      intro r
      exact hinj.injective_obj (hI r)
    refine ⟨?_, ?_, inferInstance, inferInstance, inferInstance, ?_⟩
    · intro n hn
      have := hn
      infer_instance
    · exact himg
    · have hc : (Functor.mapHomotopyCategoryPlusCompIso c).hom.app I =
          (NatTrans.mapHomotopyCategoryPlus c.hom).app I := by
        apply (HomotopyCategory.Plus.ι (ModuleCat.{u + 1} A)).map_injective
        rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
        change (Functor.mapHomotopyCategoryCompIso c (.up ℤ)).hom.app I.obj = _
        obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective I.obj
        rw [← hL]
        rfl
      rw [hc]
      simpa only [Functor.rightDerivedFunctorPlusCompUnit_app, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using
        NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac
          (finiteClosedUpperShriek A i j)
          (Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) c) I

end AlgebraicGeometry.ProEtale
