/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.Additive
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroOutsideStalk
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

/-!
# Extension by zero on the small pro-etale site

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-cbc,
`lem-cbc-proetale-extension-zero`; Stacks Project, Tags 09AE, 03DI, 03DJ and 03CY
(blueprint: lem-cbc-proetale-extension-zero).

We use the recorded extension-by-zero functor with fixed module coefficients. Its
termwise extension is Mathlib's `mapHomologicalComplex`. The scalar comparison is
specified as the mate of the identity on restricted sections, so its normalization
is fixed before invertibility is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Geometric stalk as a functor, with the colimit diagram of the recorded geometric stalk.
Its object is definitionally `Scheme.proEtaleGeometricFixedModuleStalk y A F`.
Source: Stacks Project, Tag 0F6B
(blueprint: lem-cbc-proetale-extension-zero). -/
def geometricModuleStalkFunctor (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ X) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (Scheme.proEtaleGeometricNeighbourhoodForget y).op ⋙ colim

/-- The stalk functor is additive, as a composite of additive evaluation and colimit functors.
Source: the colimit construction in Stacks Project, Tag 0F6B
(blueprint: lem-cbc-proetale-extension-zero). -/
instance geometricModuleStalkFunctor_additive (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ X) : (geometricModuleStalkFunctor A y).Additive :=
  inferInstanceAs ((sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (Scheme.proEtaleGeometricNeighbourhoodForget y).op ⋙ colim).Additive)

/-- The degreewise extension of the recorded `j_!`: terms are `j_!(K.X n)` and
its differentials are `j_!(K.d n m)`, including for unbounded complexes.
Source: blueprint lemma, last proof paragraph; Stacks Project, Tags 03DJ and 09AE
(blueprint: lem-cbc-proetale-extension-zero). -/
abbrev openExtensionCochain (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)

/-- Scalar restriction on fixed-module-valued sheaves is additive, section by section.
Source: Stacks Project, Tag 03CY, and `def-pc-sheaf-restrict-scalars`
(blueprint: lem-cbc-proetale-extension-zero). -/
instance openExtensionScalarRestriction_additive {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ)).Additive := by
  dsimp only [sheafCompose]
  infer_instance

/-- The identity-on-sections scalar square, transposed along the two recorded
extension/restriction adjunctions. This is the canonical map
`j_!^A Res_U ⟶ Res_X j_!^B`; invertibility supplies the comparison in the node's direction.
Source: blueprint lemma, scalar-restriction proof paragraph; Stacks Project, Tag 03CY
(blueprint: lem-cbc-proetale-extension-zero). -/
def openExtensionScalarMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    sheafCompose (Scheme.ProEt.topology U) (ModuleCat.restrictScalars.{u + 1} φ) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙
        sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ) :=
  ((mateEquiv
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)).symm
      (TwoSquare.mk _ _ _ _ (eqToHom (by rfl)))).natTrans

private theorem scalarMap_isIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openExtensionScalarMap φ j) := by
  have : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).isRightAdjoint
  let aU := sheafComposeAdjunction (Scheme.ProEt.topology U)
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let aX := sheafComposeAdjunction (Scheme.ProEt.topology X)
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let aB := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j
  let aA := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j
  let γ := TwoSquare.mk
    (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ))
    (openImmersionRestriction (ModuleCat.{u + 1} A) j)
    (openImmersionRestriction (ModuleCat.{u + 1} B) j)
    (sheafCompose (Scheme.ProEt.topology U)
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)) (eqToHom (by rfl))
  have hβ : (mateEquiv aX aU).symm γ =
      TwoSquare.mk (openImmersionRestriction (ModuleCat.{u + 1} B) j)
        (sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars φ))
        (sheafCompose (Scheme.ProEt.topology U) (ModuleCat.restrictScalars φ))
        (openImmersionRestriction (ModuleCat.{u + 1} A) j) (eqToHom (by rfl)) := by
    ext F : 1
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change (ModuleCat.restrictScalars φ).map
        ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).unit.app
          (F.obj.obj _)) ≫
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).counit.app _ = 𝟙 _
    exact (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).left_triangle_components _
  have h := iterated_mateEquiv_conjugateEquiv_symm aB aA aU aX γ
  rw [hβ] at h
  have hi : IsIso ((conjugateEquiv (aB.comp aX) (aU.comp aA)).symm γ.natTrans) := by
    exact inferInstance
  change IsIso (((mateEquiv aB aA).symm
    (TwoSquare.mk _ _ _ _ (eqToHom (by rfl)))).natTrans)
  rw [h]
  exact hi

private abbrev neighbourhoodInclusion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ U) :
    Scheme.ProEtaleGeometricNeighbourhood y ⥤
      Scheme.ProEtaleGeometricNeighbourhood (y ≫ j) :=
  StructuredArrow.map₂ (F := MorphismProperty.Over.map ⊤
    (inferInstance : WeaklyEtale j)) (G := Over.map j)
    (𝟙 _) (eqToHom (by rfl))

private instance neighbourhoodInclusion_initial {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ U) : (neighbourhoodInclusion j y).Initial := by
  have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).Faithful :=
    MorphismProperty.Over.faithful_map _
  have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).Full :=
    MorphismProperty.Over.full_map _
  have : (Over.map j).Faithful := by
    constructor
    intro P Q f g h
    apply Over.OverMorphism.ext
    exact congrArg (fun k : (Over.map j).obj P ⟶ (Over.map j).obj Q ↦ k.left) h
  have hf : (neighbourhoodInclusion j y).Faithful :=
    StructuredArrow.faithful_map₂ _ _
  have hfull : (neighbourhoodInclusion j y).Full :=
    StructuredArrow.full_map₂ _ _
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro N
  let V : U.ProEt := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj N.right
  let a : Spec (.of Ω) ⟶ V.left :=
    pullback.lift N.hom.left y (by exact Over.w N.hom)
  let M : Scheme.ProEtaleGeometricNeighbourhood y :=
    StructuredArrow.mk (Y := V) (Over.homMk a (by
      change a ≫ pullback.snd N.right.hom j = y
      exact pullback.lift_snd _ _ _))
  refine ⟨M, ⟨StructuredArrow.homMk
    (MorphismProperty.Over.homMk (pullback.fst N.right.hom j) (by
      change pullback.fst N.right.hom j ≫ N.right.hom =
        pullback.snd N.right.hom j ≫ j
      exact pullback.condition)) ?_⟩⟩
  apply Over.OverMorphism.ext
  simp [neighbourhoodInclusion, M, a]

private def insideStalkIso (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ U) :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
      geometricModuleStalkFunctor A (y ≫ j) ≅ geometricModuleStalkFunctor A y := by
  let e : openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
      geometricModuleStalkFunctor A y ≅ geometricModuleStalkFunctor A (y ≫ j) :=
    Functor.isoWhiskerLeft
      (sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (Scheme.proEtaleGeometricNeighbourhoodForget (y ≫ j)).op)
      (Functor.Final.colimIso (neighbourhoodInclusion j y).op)
  exact Functor.isoWhiskerLeft _ e.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit).symm _ ≪≫
    Functor.leftUnitor _

/-- Extension by zero is the exact left adjoint of restriction, acts termwise on
complexes, has the usual two geometric-stalk cases, and commutes canonically with
restriction along every map of finite commutative rings.
The stalk comparisons are isomorphisms of functors on complexes, so they include
compatibility with differentials and morphisms. The scalar comparison is the specified
mate `openExtensionScalarMap`, extended degreewise.
Source: Weil conjectures blueprint, lemma `lem-cbc-proetale-extension-zero`, order 1582;
Stacks Project, Tags 09AE, 03DI, 03DJ, 03CY
(blueprint: lem-cbc-proetale-extension-zero).

Proof:
1. `lem-weil-proetale-weakly-etale-localization` identifies the open site with the
localized site and its constant coefficients with the restricted coefficients.
`lem-pur-site-restriction-module-adjunction-exact` gives the exact adjunction for
`def-weil-extension-by-zero`. Apply it to fixed A-module-valued sheaves.
2. By `lem-cbc-proetale-sheafification-geometric-stalk`, the stalk is the colimit of
its extension presheaf on `def-weil-proetale-geometric-stalk` neighbourhoods. At a point
in U, refinement by the fibre product with U gives a cofinal collection of neighbourhoods
factoring through U. It is surjective on representative classes, and equality of two
classes can be checked after another common refinement through U. This gives the stalk
of the original sheaf. Outside U no pointed neighbourhood factors through U; all values
of the extension presheaf vanish. These constructions commute with sheaf morphisms.
3. Restriction of scalars leaves every section group and restriction map unchanged and
acts by a • m = φ(a) • m. Thus it commutes with the extension presheaf and, by the unique
extended action of module sheafification (`def-weil-presheaf-modules-sheafification`,
Tag 03CY), with its sheafification. Transposing this identity on restricted sections
gives precisely `openExtensionScalarMap`, hence this map is invertible.
4. Apply all functors and comparisons in each degree, with differential j_!(d).
Naturality makes the comparison components chain maps, and makes the degreewise unit
and counit an adjunction on complexes. Exactness gives H^q(j_!K) = j_!H^q(K), so the
termwise functors preserve quasi-isomorphisms and descend, with this adjunction, to the
abstract derived localization. The degreewise stalk calculation gives the displayed
formula for the entire complex. -/
theorem proEtale_extension_by_zero (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (openImmersionLowerShriek (ModuleCat.{u + 1} A) j) ∧
    PreservesFiniteColimits (openImmersionLowerShriek (ModuleCat.{u + 1} A) j) ∧
    Nonempty (openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⊣
      openImmersionRestriction (ModuleCat.{u + 1} A) j) ∧
    Nonempty (openExtensionCochain A j ⊣
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ U),
      Nonempty (openExtensionCochain A j ⋙
          (geometricModuleStalkFunctor A (y ≫ j)).mapHomologicalComplex (.up ℤ) ≅
        (geometricModuleStalkFunctor A y).mapHomologicalComplex (.up ℤ))) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ X),
      (¬ ∃ z : Spec (.of Ω) ⟶ U, z ≫ j = y) →
      ∀ K : CochainComplex (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)) ℤ,
        IsZero (((geometricModuleStalkFunctor A y).mapHomologicalComplex (.up ℤ)).obj
          ((openExtensionCochain A j).obj K))) ∧
    (∀ (B : Type (u + 1)) [CommRing B] [Finite B] (φ : A →+* B),
      IsIso (openExtensionScalarMap φ j) ∧
      IsIso ((openExtensionScalarMap φ j).mapHomologicalComplex (.up ℤ))) := by
  refine ⟨inferInstance, inferInstance,
    ⟨openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j⟩,
    ⟨(openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).mapHomologicalComplex
      (.up ℤ)⟩, ?_, ?_, ?_⟩
  · intro Ω _ _ y
    exact ⟨Functor.mapHomologicalComplexCompIso (insideStalkIso A j y) (.up ℤ)⟩
  · intro Ω _ _ y hy K
    apply (IsZero.iff_id_eq_zero _).mpr
    ext n : 1
    exact (openExtension_outside_stalk A j y hy (K.X n)).eq_of_src _ _
  · intro B _ _ φ
    have := scalarMap_isIso φ j
    refine ⟨inferInstance, ?_⟩
    exact inferInstanceAs (IsIso
      (NatIso.mapHomologicalComplex (asIso (openExtensionScalarMap φ j)) (.up ℤ)).hom)

end AlgebraicGeometry.ProEtale
