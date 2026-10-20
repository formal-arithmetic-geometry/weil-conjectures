/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.AffineComponentSiteProjection
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.RingTheory.ProEtale.WContractible
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.Paper.CondensedPointBasis
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant

/-!
# Sections of the generic-fibre component map

Source: Hemo--Richarz--Scholbach, proof of Theorem 4.13, irreducible case and
(4.4), with fibre-product points from Stacks Tag 03H4
(blueprint: lem-zl-generic-fiber-components-section).

The theorem records the component map of an affine ind-etale w-contractible object over
an irreducible affine base, its continuous section, the component-site square, and the
coefficient-compatible equivalence on the geometric generic fibre. All equivalences and
coefficient comparisons are statement-level data; their proofs are postponed.
-/

@[expose] public section

set_option autoImplicit false

universe u wR wS wV wCJ wCK

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProEt

/-- The affine component functor characterized by the locally ringed space
`|T| ×_π₀(T) E`, using the full construction theorem, not an arbitrary functor.
The characterization determines it up to the unique natural isomorphism over T
and over E, which is the equality used for the ensuing sheaf morphisms.
Source: Bhatt--Scholze Lemma 2.2.8 and 4.2.13(1)
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable def genericComponentFunctor (T : Scheme.{u}) [IsAffine T] :
    Over (componentProfinite T) ⥤ T.ProEt :=
  (affine_component_site_projection T).choose

/-- Coordinates of the canonical component functor, retained from its geometric
characterization. Source: Bhatt--Scholze Lemma 2.2.8
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable def genericComponentCoordinates (T : Scheme.{u}) [IsAffine T] :
    ∀ E : Over (componentProfinite T),
      C(((genericComponentFunctor T).obj E).left, E.left) :=
  (affine_component_site_projection T).choose_spec.choose

/-- Continuity of the chosen, geometrically characterized component functor.
Source: Bhatt--Scholze Lemma 4.2.13(1)
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable instance genericComponentContinuous (T : Scheme.{u}) [IsAffine T] :
    (genericComponentFunctor T).IsContinuous
      ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T) :=
  ((affine_component_site_projection T).choose_spec.choose_spec.2.2.2.2).choose

/-- The canonical component morphism on sets, extracted from the evaluation of the
same functor. Its direct image is restriction along `genericComponentFunctor T`.
Source: Bhatt--Scholze Lemma 4.2.13(1)
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable def genericComponentProjection (T : Scheme.{u}) [IsAffine T] :
    GeometricMorphism (Sheaf (topology T) (Type (u + 1)))
      (Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite T))
        (Type (u + 1))) :=
  ((affine_component_site_projection T).choose_spec.choose_spec.2.2.2.2).choose_spec.1.choose

/-- The ring-valued inverse image induced by the very same component functor.
Its right adjoint is restriction along that functor, so its operations and
adjunction unit are those of the canonical algebraic lift.
Source: Bhatt--Scholze Lemma 4.2.13(1) and HRS Theorem 4.13, diagram (4.4)
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable abbrev genericComponentRingPush (T : Scheme.{u}) [IsAffine T] :=
  (genericComponentFunctor T).sheafPushforwardContinuous RingCat.{u + 1}
    ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T)

/-- The scalar-extension compatibility, characterized without any choice of a resolution.
For a ring map from a discrete ring to global coefficients, extension of constants is
left adjoint to global sections with that scalar action. Its unbounded left derived
functor is characterized by the displayed localization counit. The assertion says that
these actual scalar extensions commute with the specified component-derived equivalence.
Source: HRS Theorem 4.13, proof after (4.4)
(blueprint: lem-zl-generic-fiber-components-section). -/
def GenericComponentScalarCompatibility
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u + 1}) (B : Sheaf K RingCat.{u + 1})
    (c : C) (d : D) (e : A.obj.obj (op c) ≅ B.obj.obj (op d))
    [HasDerivedCategory.{wS} (ringedSiteModules.{u + 1} A)]
    [HasDerivedCategory.{wV} (ringedSiteModules.{u + 1} B)]
    (E : DerivedCategory (ringedSiteModules.{u + 1} A) ≌
      DerivedCategory (ringedSiteModules.{u + 1} B)) : Prop :=
  (∀ (R : Type (u + 1)) [Ring R]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    (a : R →+* A.obj.obj (op c))
    (FS : ModuleCat.{u + 1} R ⥤ ringedSiteModules.{u + 1} A)
    (FV : ModuleCat.{u + 1} R ⥤ ringedSiteModules.{u + 1} B)
    [FS.Additive] [FV.Additive],
    Nonempty (FS ⊣ SheafOfModules.evaluation A (op c) ⋙ ModuleCat.restrictScalars a) →
    Nonempty (FV ⊣ SheafOfModules.evaluation B (op d) ⋙
      ModuleCat.restrictScalars (e.hom.hom.comp a)) →
    ∀ (LS : DerivedCategory (ModuleCat.{u + 1} R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} A))
      (LV : DerivedCategory (ModuleCat.{u + 1} R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} B))
      (εS : DerivedCategory.Qh ⋙ LS ⟶
        FS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (εV : DerivedCategory.Qh ⋙ LV ⟶
        FV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LS.IsLeftDerivedFunctor εS
        (HomotopyCategory.quasiIso (ModuleCat.{u + 1} R) (ComplexShape.up ℤ)) →
      LV.IsLeftDerivedFunctor εV
        (HomotopyCategory.quasiIso (ModuleCat.{u + 1} R) (ComplexShape.up ℤ)) →
      Nonempty (LS ⋙ E.functor ≅ LV)) ∧
  (∀ (R : Type (u + 1)) [CommRing R]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    [HasDerivedCategory.{wCJ} (realizationModules J R)]
    [HasDerivedCategory.{wCK} (realizationModules K R)]
    (aS : (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (realizationRing J R) ⟶ A)
    (aV : (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (realizationRing K R) ⟶ B),
    (∀ r : R,
      e.hom.hom ((aS.hom.app (op c)).hom ((realizationRingUnit J R).app (op c) r)) =
        (aV.hom.app (op d)).hom ((realizationRingUnit K R).app (op d) r)) →
    ∀ (FS : realizationModules J R ⥤ ringedSiteModules.{u + 1} A)
      (FV : realizationModules K R ⥤ ringedSiteModules.{u + 1} B)
      [FS.Additive] [FV.Additive],
    Nonempty (FS ⊣ SheafOfModules.restrictScalars aS) →
    Nonempty (FV ⊣ SheafOfModules.restrictScalars aV) →
    ∀ (LS : DerivedCategory (realizationModules J R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} A))
      (LV : DerivedCategory (realizationModules K R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} B))
      (εS : DerivedCategory.Qh ⋙ LS ⟶
        FS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (εV : DerivedCategory.Qh ⋙ LV ⟶
        FV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
    LS.IsLeftDerivedFunctor εS
      (HomotopyCategory.quasiIso (realizationModules J R) (ComplexShape.up ℤ)) →
    LV.IsLeftDerivedFunctor εV
      (HomotopyCategory.quasiIso (realizationModules K R) (ComplexShape.up ℤ)) →
    Nonempty (commutativeSiteDerivedConstantModuleFunctor J R ⋙ LS ⋙ E.functor ≅
      commutativeSiteDerivedConstantModuleFunctor K R ⋙ LV))


/-- The generic-fibre component map is a split surjection and gives the component-site
comparison, including its coefficient and derived-category consequences.

Source: Hemo--Richarz--Scholbach, proof of Theorem 4.13, irreducible case and diagram
(4.4); fibre-product points from Stacks Tag 03H4
(blueprint: lem-zl-generic-fiber-components-section).

Proof for stage 3, following the seven DAG steps:
1. By affine fibre products and ind-etale stability, V is affine and ind-etale over Ω.
   Affine schemes are qcqs and spectral; the spectral component theorem makes S and Sη
   profinite. The first projection induces r on the actual quotient component spaces.
2. For a component of U choose a point q. Flat going-down gives a generalization q₀
   over the generic point of X, in the same component. The nonzero tensor product of
   κ(q₀) and Ω over κ(η) has a prime; the fibre-product-point theorem lifts q₀ to V.
   Thus r is surjective, including the empty case.
3. W-contractibility makes S extremally disconnected. Gleason's section theorem splits
   the continuous surjection r.
4. Use `affine_component_site_projection` for U and V. For E over S, base change of U_E
   is V_(E ×_S Sη), with the same locally ringed space and inverse-image structure sheaf.
   Naturality identifies the test-object functors and hence their geometric morphisms.
5. The geometric-field and ind-etale basis theorems identify V with Ω[Sη] and its affine
   ind-etale basis with profinite sets over Sη. Finite covers are exactly finite jointly
   surjective families. The resulting sheaf equivalence is the component inverse image.
6. Base change of Ω[E] along V → Spec Ω is Ω[Sη × E]; hence the structure map corresponds
   to Sη → *. The analogous identity for U gives p_U = q_S π_U. Transporting ring
   operations gives the coefficient comparisons for every condensed coefficient ring.
7. Transport module actions and linear maps along that same coefficient comparison.
   The inverse module functor is left adjoint to restriction along the component functor
   with the adjunction-unit ring map γ. This equivalence is additive and exact. Apply
   it termwise and descend at all quasi-isomorphisms to get the unbounded derived
   equivalence, with its Q-factorization. Terminal evaluation identifies global scalar
   actions by eΓ. Thus the ordinary extension-of-constants left adjoints commute, as do
   their unbounded left derived functors by the localization universal property. In the
   commutative constant-sheaf presentation this is precisely the displayed comparison
   after `commutativeSiteDerivedConstantModuleFunctor`, with constants normalized by
   `realizationRingUnit`. For R = Γ(*,Λ) and its constant-section map this gives the
   scalar extensions used after HRS (4.4).
-/
theorem generic_fiber_components_section
    (X : Scheme.{u}) [IsAffine X] [Nonempty X] [IrreducibleSpace X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : AlgebraicGeometry.Scheme.Spec.obj (Opposite.op (CommRingCat.of Ω)) ⟶ X)
    (hη : ∀ x : (AlgebraicGeometry.Scheme.Spec.obj (Opposite.op (CommRingCat.of Ω))),
      η x = genericPoint X)
    (U : X.ProEt) [IsAffine U.left]
    (hind : RingHom.IndEtaleAcrossUniverses U.hom.appTop.hom)
    (hw : IsWContractibleRing Γ(U.left, ⊤)) :
    letI : IsAffineHom (show U.left ⟶ X from U.hom) :=
      isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
    letI : IsAffineHom η := isAffineHom_of_isAffine η
    letI : IsAffine (pullback U.hom η) :=
      instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
    let V : Scheme := pullback U.hom η
    let S : Profinite.{u} := Scheme.ProEt.componentProfinite U.left
    let Sη : Profinite.{u} := Scheme.ProEt.componentProfinite V
    let r : C(Sη, S) :=
      ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
        (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
    (∃ s : C(S, Sη), Function.LeftInverse r s) ∧
      (∃ (ρ : GeometricMorphism
          (Sheaf ((coherentTopology Profinite.{u}).over Sη) (Type (u + 1)))
          (Sheaf ((coherentTopology Profinite.{u}).over S) (Type (u + 1))))
        (g : GeometricMorphism
          (Sheaf (Scheme.ProEt.topology V) (Type (u + 1)))
          (Sheaf (Scheme.ProEt.topology U.left) (Type (u + 1)))),
        ρ.inverse = (coherentTopology Profinite.{u}).overMapPullback
            (Type (u + 1)) (ConcreteCategory.ofHom r : Sη ⟶ S) ∧
        Nonempty (ρ.direct ≅
          (Over.pullback (ConcreteCategory.ofHom r : Sη ⟶ S)).sheafPushforwardContinuous
            (Type (u + 1))
            ((coherentTopology Profinite.{u}).over S)
            ((coherentTopology Profinite.{u}).over Sη)) ∧
        g.inverse = Scheme.proEtaleSheafInverseImage
            (pullback.fst U.hom η) (Type (u + 1)) ∧
        (genericComponentProjection V).inverse.IsEquivalence ∧
        Nonempty (ρ.inverse ⋙ (genericComponentProjection V).inverse ≅
          (genericComponentProjection U.left).inverse ⋙ g.inverse)) ∧
      (∃ pΩ : GeometricMorphism
          (Sheaf (topology (AlgebraicGeometry.Scheme.Spec.obj
            (op (CommRingCat.of Ω)))) (Type (u + 1)))
          (Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
        Nonempty (pΩ.direct ⋙
            sheafToPresheaf (coherentTopology Profinite.{u}) (Type (u + 1)) ≅
          sheafToPresheaf (topology (AlgebraicGeometry.Scheme.Spec.obj
            (op (CommRingCat.of Ω)))) (Type (u + 1)) ⋙
          (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
            (AlgebraicGeometry.ProEtale.profiniteToProEtOf
              (AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of Ω)))).op) ∧
        Nonempty ((coherentTopology Profinite.{u}).overPullback (Type (u + 1)) Sη ⋙
            (genericComponentProjection V).inverse ≅
          pΩ.inverse ⋙ Scheme.proEtaleSheafInverseImage
            (pullback.snd U.hom η) (Type (u + 1)))) ∧
      (∀ Λ : Profinite.CondensedRing.{u},
        ∃ (A : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
          (AU : Sheaf (topology U.left) RingCat.{u + 1})
          (AV : Sheaf (topology V) RingCat.{u + 1}),
        Nonempty (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj A) ≅ Λ) ∧
        Nonempty (Mon.mk ((sheafCompose (topology U.left)
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj AU) ≅
          AlgebraicGeometry.ProEtale.coefficientRing U.left Λ) ∧
        Nonempty (Mon.mk ((sheafCompose (topology V)
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj AV) ≅
          AlgebraicGeometry.ProEtale.coefficientRing V Λ) ∧
        ∃ (LU : Sheaf ((coherentTopology Profinite.{u}).over S) RingCat.{u + 1} ⥤
            Sheaf (topology U.left) RingCat.{u + 1})
          (LV : Sheaf ((coherentTopology Profinite.{u}).over Sη) RingCat.{u + 1} ⥤
            Sheaf (topology V) RingCat.{u + 1})
          (adjU : LU ⊣ genericComponentRingPush U.left)
          (adjV : LV ⊣ genericComponentRingPush V)
          (iU : LU.obj (A.over S) ≅ AU)
          (iV : LV.obj (A.over Sη) ≅ AV)
          (γ : A.over Sη ⟶ (genericComponentRingPush V).obj AV),
        γ = adjV.unit.app (A.over Sη) ≫ (genericComponentRingPush V).map iV.hom ∧
        Nonempty (LU ⋙ sheafCompose (topology U.left) (CategoryTheory.forget RingCat.{u + 1}) ≅
          sheafCompose ((coherentTopology Profinite.{u}).over S)
            (CategoryTheory.forget RingCat.{u + 1}) ⋙ (genericComponentProjection U.left).inverse) ∧
        Nonempty (LV ⋙ sheafCompose (topology V) (CategoryTheory.forget RingCat.{u + 1}) ≅
          sheafCompose ((coherentTopology Profinite.{u}).over Sη)
            (CategoryTheory.forget RingCat.{u + 1}) ⋙ (genericComponentProjection V).inverse) ∧
        ∃ (t : (genericComponentFunctor V).obj (Over.mk (𝟙 Sη)) ≅ ProEt.mk (𝟙 V))
          (eΓ : (A.over Sη).obj.obj (op (Over.mk (𝟙 Sη))) ≅
            AV.obj.obj (op (ProEt.mk (𝟙 V)))),
        eΓ.hom = γ.hom.app (op (Over.mk (𝟙 Sη))) ≫ AV.obj.map t.inv.op ∧
        ∃ eM : ringedSiteModules.{u + 1} (A.over Sη) ≌ ringedSiteModules.{u + 1} AV,
        Nonempty (eM.functor ⊣ SheafOfModules.pushforward γ) ∧
        ∃ (_ : eM.functor.Additive),
        ∀ [HasDerivedCategory.{wS} (ringedSiteModules.{u + 1} (A.over Sη))]
          [HasDerivedCategory.{wV} (ringedSiteModules.{u + 1} AV)],
        ∃ eD : DerivedCategory (ringedSiteModules.{u + 1} (A.over Sη)) ≌
            DerivedCategory (ringedSiteModules.{u + 1} AV),
        Nonempty (DerivedCategory.Q ⋙ eD.functor ≅
          eM.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
        GenericComponentScalarCompatibility.{u, wR, wS, wV, wCJ, wCK}
          (A.over Sη) AV (Over.mk (𝟙 Sη)) (ProEt.mk (𝟙 V)) eΓ eD) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt

