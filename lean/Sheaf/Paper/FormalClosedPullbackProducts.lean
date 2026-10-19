/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Derived products and closed pro-etale restriction

Source: Stacks Project, Tags 09AA and 07KC; the closed-pullback portion of
`det-formal-closed-support-ii-limits`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem productSmallSupport
    {D : Type*} [Category D] [Preadditive D] [LocallySmall.{u} D]
    {I : Type*} (K : I → D) (t : Fan K) (ht : IsLimit t) :
    Small.{u} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : K i ⟶ t.pt := ht.lift (Fan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : p i ≫ t.proj j = Pi.single (M := fun j ↦ K i ⟶ K j)
      i (𝟙 (K i)) j := ht.fac (Fan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ t.proj i.val ≫ p i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ p i.val ≫ f ≫ t.proj i.val) hij
  have hi : p i.val ≫ t.proj i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : p j.val ≫ t.proj i.val = 0 := by simp [hp, Ne.symm hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [Category.assoc, hi, hj, Category.comp_id, comp_zero] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

private theorem preservesProductsOfSmall
    {D : Type*} [Category D] [Preadditive D] [LocallySmall.{u} D]
    {C : Type*} [Category C] [Preadditive C]
    (F : D ⥤ C) [F.PreservesZeroMorphisms]
    (hsmall : ∀ J : Type u, PreservesLimitsOfShape (Discrete J) F)
    (I : Type*) : PreservesLimitsOfShape (Discrete I) F := by
  classical
  have hpres (K : I → D) : PreservesLimit (Discrete.functor K) F := by
    refine ⟨fun {t} ht ↦ ⟨?_⟩⟩
    let t₀ : Fan K := t
    have hsupport : Small.{u} {i // ¬ IsZero (K i)} := productSmallSupport K t₀ ht
    let J := {i // ¬ IsZero (K i)}
    have : PreservesLimitsOfShape (Discrete (Shrink.{u} J)) F := hsmall _
    have : PreservesLimitsOfShape (Discrete J) F :=
      preservesLimitsOfShape_of_equiv (Discrete.equivalence (equivShrink J)).symm F
    let U : J → D := fun i ↦ K i.val
    let r : Fan U := Fan.mk t.pt (fun i ↦ t₀.proj i.val)
    have hr : IsLimit r := by
      refine Fan.IsLimit.mk r (fun s ↦ ht.lift (Fan.mk s.pt
        (fun i ↦ if hi : ¬ IsZero (K i) then s.proj ⟨i, hi⟩ else 0))) ?_ ?_
      · intro s i
        obtain ⟨i, hi⟩ := i
        change _ ≫ t.π.app (Discrete.mk i) = _
        rw [ht.fac]
        simp only [Fan.mk_π_app, dif_pos hi]
      · intro s m hm
        apply ht.hom_ext
        intro ⟨i⟩
        rw [ht.fac]
        by_cases hi : ¬ IsZero (K i)
        · simpa only [r, fan_mk_proj, t₀, Fan.proj, Fan.mk_π_app, dif_pos hi]
            using hm ⟨i, hi⟩
        · exact (not_not.mp hi).eq_of_tgt _ _
    let q : Fan (fun i ↦ F.obj (U i)) :=
      Fan.mk (F.obj t.pt) (fun i ↦ F.map (t₀.proj i.val))
    have hq : IsLimit q := isLimitFanMkObjOfIsLimit F U _ hr
    refine { lift := fun s ↦ hq.lift (Fan.mk s.pt
        (fun i ↦ s.π.app (Discrete.mk i.val))), fac := ?_, uniq := ?_ }
    · intro s ⟨i⟩
      by_cases hi : ¬ IsZero (K i)
      · exact hq.fac (Fan.mk s.pt (fun i ↦ s.π.app (Discrete.mk i.val)))
          (Discrete.mk ⟨i, hi⟩)
      · exact (F.map_isZero (not_not.mp hi)).eq_of_tgt _ _
    · intro s m hm
      apply Fan.IsLimit.hom_ext hq
      intro i
      exact (hm (Discrete.mk i.val)).trans
        (hq.fac (Fan.mk s.pt (fun i ↦ s.π.app (Discrete.mk i.val)))
          (Discrete.mk i)).symm
  exact preservesLimitsOfShape_of_discrete F

private theorem derivedPreservesProducts
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (I : Type*) [HasProductsOfShape I C] [HasProductsOfShape I D]
    [HasExactLimitsOfShape (Discrete I) C] [HasExactLimitsOfShape (Discrete I) D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete I) F] :
    PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory := by
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  have : PreservesLimitsOfShape (Discrete I) (F.mapHomologicalComplex (.up ℤ)) := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    exact inferInstanceAs
      (PreservesLimitsOfShape (Discrete I) (HomologicalComplex.eval C (.up ℤ) n ⋙ F))
  have : PreservesLimitsOfShape (Discrete I) (Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  have hrep (K : I → CochainComplex C ℤ) :
      PreservesLimit (Discrete.functor (fun i ↦ Q.obj (K i))) F.mapDerivedCategory := by
    apply preservesLimit_of_preserves_limit_cone (DerivedCategory.isLimitFanQ K)
    exact (isLimitMapConeFanMkEquiv F.mapDerivedCategory _ _).symm
      (isLimitFanMkObjOfIsLimit (Q ⋙ F.mapDerivedCategory) K _ (productIsProduct K))
  have (K : I → DerivedCategory C) :
      PreservesLimit (Discrete.functor K) F.mapDerivedCategory := by
    let K' : I → CochainComplex C ℤ := fun i ↦ Q.objPreimage (K i)
    let : PreservesLimit (Discrete.functor (fun i ↦ Q.obj (K' i)))
        F.mapDerivedCategory := hrep K'
    exact preservesLimit_of_iso_diagram F.mapDerivedCategory
      (Discrete.natIso (F := Discrete.functor fun i ↦ Q.obj (K' i))
        (G := Discrete.functor K) fun i ↦ Q.objObjPreimageIso (K i.as))
  exact preservesLimitsOfShape_of_discrete F.mapDerivedCategory

private theorem moduleProductsExact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (I : Type (u + 1)) :
    HasExactLimitsOfShape (Discrete I) (FormalSupportModules Λ X) := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  let R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (condensedRingObj Λ X))
  let : HasExactLimitsOfShape (Discrete I) (SheafOfModules.{u + 1} R) :=
    Scheme.ProEt.products_exact.{u, 0, u + 1} X R I
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete I) e.symm

/-- The exact coefficient-compatible pullback along a closed immersion preserves
products on the unbounded derived categories, with their specified projections.

Source: Stacks Project, Tag 09AA (1), and Tag 07KC; blueprint
`sec-six-functors-basics/sk-lem-formal-closed-support-ii/` proof, restriction paragraph
(blueprint: lem-formal-closed-pullback-derived-products).

Proof: the finite-type hypotheses make X compact and quasi-separated, and
quasi-compactness of the complementary open makes its range compact. Apply
`closed_inverseImage_preserves_limits` to the internal coefficient ring, then
compose with scalar transport along `condensedPullbackHom`, an equivalence.
This proves ordinary product preservation in the coefficient universe.

Use `InternalAbelianSheafModule.sectionModuleEquivalence` to identify internal
modules with sectionwise modules. Transfer `products_exact` across this
explicit equivalence, on both X and Z. The existing `DerivedCategory.isLimitFanQ`
then identifies each localized termwise product cone as a derived product cone.
Apply the exact pullback degreewise: evaluations detect its product preservation.
`mapDerivedCategoryFactors` identifies its localization with derived pullback.
Thus the composite of localization and derived pullback preserves products.
Choose complex representatives using essential surjectivity of localization;
transporting their product diagrams along the representative isomorphisms proves
derived product preservation for every family in the coefficient universe.

For an existing product indexed in any larger universe, insert each factor by
identity at its own coordinate and zero elsewhere. Projection followed by this
insertion gives an endomorphism of the product. The endomorphisms for nonzero
factors are distinct: sandwiching an alleged equality between insertion and
projection forces the identity of that factor to vanish. Local smallness of
Hom therefore makes the nonzero support small. Shrink it to the coefficient
universe and apply the small-product result. Removing zero factors leaves the
same limiting cone on both sides, since the additive derived functor preserves
zero objects. This proves preservation for the original existing large cone,
without asserting existence of larger products. Empty schemes, empty products,
and identity immersions are covered by the same constructions. -/
theorem formalClosedPullback_preservesDerivedProducts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k]
    {Z V X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∀ I : Type (u + 2), PreservesLimitsOfShape (Discrete I)
      (formalSupportPullback Λ i).mapDerivedCategory := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of k))
  let : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
  have hc : IsCompact ((Set.range i)ᶜ) := by
    rw [show Set.range i = Set.range i.base from rfl, hij, compl_compl]
    exact isCompact_range j.continuous
  let B := condensedRingObj Λ X
  have h := Scheme.closed_inverseImage_preserves_limits i hc B
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      ((ProEtale.upperStar Ab.{u + 1} i).mapMod B) := h.2.2.2.1
  have : PreservesLimitsOfSize.{u + 1, u + 1} (formalSupportPullback Λ i) := by
    change PreservesLimitsOfSize.{u + 1, u + 1} (_ ⋙
      (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).inverse)
    infer_instance
  intro I
  have : ((formalSupportPullback Λ i).mapDerivedCategory).Additive := inferInstance
  apply preservesProductsOfSmall.{u + 1} (formalSupportPullback Λ i).mapDerivedCategory
  intro J
  let : HasExactLimitsOfShape (Discrete J) (FormalSupportModules Λ X) :=
    moduleProductsExact Λ X J
  let : HasExactLimitsOfShape (Discrete J) (FormalSupportModules Λ Z) :=
    moduleProductsExact Λ Z J
  exact derivedPreservesProducts J (formalSupportPullback Λ i)

end AlgebraicGeometry.ProEtale.CondensedRing
