/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.SixFunctors.ClosedProjectionEtale
import Sheaf.SixFunctors.ClosedProjectionProEtale
import Sheaf.CategoryTheory.RingedSiteDualityMaps

/-!
# Exceptional restriction of a Verdier dual

Source: the current Weil conjectures blueprint, six-functors basics,
`sk-prop-sf-biduality-general/lem-weil-closed-costalk-duality.md`
(blueprint: lem-weil-closed-costalk-duality).

The two statements cover the small etale and small pro-etale sites. A termwise
localization comparison specifies each derived functor, rather than allowing an
unrelated functor. The duals are the recorded derived internal Hom construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

section FormalDuality

universe a b v₁ v₂

private noncomputable def costalkHomEquiv
    {A : Type a} {B : Type b} [Category.{v₁} A] [Category.{v₂} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : WeilConjectures.CoefficientClosedStructure HA)
    (SB : WeilConjectures.CoefficientClosedStructure HB)
    {L : A ⥤ B} {V : B ⥤ A} {E : A ⥤ B} (adj : V ⊣ E)
    (p : ((𝟭 B).prod L) ⋙ SB.tensor ⋙ V ≅ (V.prod (𝟭 A)) ⋙ SA.tensor)
    (O K : A) (N : B) :
    (N ⟶ E.obj (HA.obj (op K, O))) ≃ (N ⟶ HB.obj (op (L.obj K), E.obj O)) := by
  let e₁ := (adj.homEquiv N (HA.obj (op K, O))).symm
  let e₂ := (SA.transpose (V.obj N) K O).symm
  let e₃ := Iso.homCongr (p.app (N, K)).symm (Iso.refl O)
  let e₄ := adj.homEquiv (SB.tensor.obj (N, L.obj K)) O
  let e₅ := SB.transpose N (L.obj K) (E.obj O)
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

private theorem costalkTranspose_left
    {D : Type a} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    {T T' P Q : D} (f : T' ⟶ T) (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T' P Q (S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ g) =
      f ≫ S.transpose T P Q g := by
  let _ := S.monoidal
  dsimp only [WeilConjectures.CoefficientClosedStructure.transpose,
    WeilConjectures.CoefficientClosedStructure.tensor, MonoidalCategory.tensor]
  rw [MonoidalCategory.tensorHom_id]
  exact (S.adjunction P).homEquiv_naturality_left f g

private theorem costalkTranspose_source
    {D : Type a} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (T : D) {P P' Q : D} (f : P' ⟶ P) (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T P' Q (S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ g) =
      S.transpose T P Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q)) := by
  let _ := S.monoidal
  apply (S.transpose T P' Q).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = (tensorRight P').map
    (S.transpose T P Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q))) ≫ S.evaluation P' Q
  rw [Functor.map_comp, Category.assoc]
  change _ = (S.transpose T P Q g ▷ P') ≫
    (H.map (Prod.mkHom f.op (𝟙 Q)) ▷ P') ≫ S.evaluation P' Q
  rw [show (H.map (Prod.mkHom f.op (𝟙 Q)) ▷ P') ≫ S.evaluation P' Q =
    (H.obj (op P, Q) ◁ f) ≫ S.evaluation P Q from S.evaluation_naturality P P' Q f]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  change _ = (T ◁ f) ≫ (S.transpose T P Q).symm (S.transpose T P Q g)
  rw [Equiv.symm_apply_apply]
  simp only [WeilConjectures.CoefficientClosedStructure.tensor, tensor_map, id_tensorHom]

private theorem costalkHomEquiv_left
    {A : Type a} {B : Type b} [Category.{v₁} A] [Category.{v₂} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : WeilConjectures.CoefficientClosedStructure HA)
    (SB : WeilConjectures.CoefficientClosedStructure HB)
    {L : A ⥤ B} {V : B ⥤ A} {E : A ⥤ B} (adj : V ⊣ E)
    (p : ((𝟭 B).prod L) ⋙ SB.tensor ⋙ V ≅ (V.prod (𝟭 A)) ⋙ SA.tensor)
    (O : A)
    (K : A) {N N' : B} (f : N' ⟶ N)
    (g : N ⟶ E.obj (HA.obj (op K, O))) :
    costalkHomEquiv SA SB adj p O K N' (f ≫ g) =
      f ≫ costalkHomEquiv SA SB adj p O K N g := by
  dsimp only [costalkHomEquiv, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_left_symm]
  have hA := costalkTranspose_left SA (V.map f)
    ((SA.transpose (V.obj N) K O).symm ((adj.homEquiv N _).symm g))
  rw [Equiv.apply_symm_apply] at hA
  rw [← hA, Equiv.symm_apply_apply]
  dsimp only [Iso.homCongr, Iso.symm, Iso.refl]
  simp only [Category.comp_id]
  dsimp only [Equiv.coe_fn_mk]
  simp only [← Category.assoc]
  change SB.transpose N' (L.obj K) (E.obj O)
    (adj.homEquiv _ _ ((p.hom.app (N', K) ≫
      SA.tensor.map (Prod.mkHom (V.map f) (𝟙 K))) ≫ _)) = _
  have hp := p.hom.naturality (Prod.mkHom f (𝟙 K))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hp
  rw [← hp, Category.assoc, L.map_id]
  rw [adj.homEquiv_naturality_left]
  exact costalkTranspose_left SB f _


private theorem costalkHomEquiv_source
    {A : Type a} {B : Type b} [Category.{v₁} A] [Category.{v₂} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : WeilConjectures.CoefficientClosedStructure HA)
    (SB : WeilConjectures.CoefficientClosedStructure HB)
    {L : A ⥤ B} {V : B ⥤ A} {E : A ⥤ B} (adj : V ⊣ E)
    (p : ((𝟭 B).prod L) ⋙ SB.tensor ⋙ V ≅ (V.prod (𝟭 A)) ⋙ SA.tensor)
    (O : A)
    {K K' : A} (f : K' ⟶ K) (N : B)
    (g : N ⟶ E.obj (HA.obj (op K, O))) :
    costalkHomEquiv SA SB adj p O K' N
        (g ≫ E.map (HA.map (Prod.mkHom f.op (𝟙 O)))) =
      costalkHomEquiv SA SB adj p O K N g ≫
        HB.map (Prod.mkHom (L.map f).op (𝟙 (E.obj O))) := by
  dsimp only [costalkHomEquiv, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_right_symm]
  have hA := costalkTranspose_source SA (V.obj N) f
    ((SA.transpose (V.obj N) K O).symm ((adj.homEquiv N _).symm g))
  rw [Equiv.apply_symm_apply] at hA
  rw [← hA, Equiv.symm_apply_apply]
  dsimp only [Iso.homCongr, Iso.symm, Iso.refl]
  simp only [Category.comp_id]
  dsimp only [Equiv.coe_fn_mk]
  simp only [← Category.assoc]
  change SB.transpose N (L.obj K') (E.obj O)
    (adj.homEquiv _ _ ((p.hom.app (N, K') ≫
      SA.tensor.map (Prod.mkHom (𝟙 (V.obj N)) f)) ≫ _)) = _
  have hp := p.hom.naturality (Prod.mkHom (𝟙 N) f)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hp
  rw [V.map_id] at hp
  rw [← hp, Category.assoc, adj.homEquiv_naturality_left]
  exact costalkTranspose_source SB N (L.map f) _

private theorem costalkDualityOfProjection
    {A : Type a} {B : Type b} [Category.{v₁} A] [Category.{v₂} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : WeilConjectures.CoefficientClosedStructure HA)
    (SB : WeilConjectures.CoefficientClosedStructure HB)
    {L : A ⥤ B} {V : B ⥤ A} {E : A ⥤ B} (adj : V ⊣ E)
    (p : ((𝟭 B).prod L) ⋙ SB.tensor ⋙ V ≅ (V.prod (𝟭 A)) ⋙ SA.tensor)
    (O : A) :
    Nonempty (((𝟭 Aᵒᵖ).prod' ((Functor.const _).obj O)) ⋙ HA ⋙ E ≅
      L.op ⋙ ((𝟭 Bᵒᵖ).prod' ((Functor.const _).obj (E.obj O))) ⋙ HB) := by
  let F := ((𝟭 Aᵒᵖ).prod' ((Functor.const _).obj O)) ⋙ HA ⋙ E
  let G := L.op ⋙ ((𝟭 Bᵒᵖ).prod' ((Functor.const _).obj (E.obj O))) ⋙ HB
  let e (K : Aᵒᵖ) (N : B) := costalkHomEquiv SA SB adj p O K.unop N
  have hn (K : Aᵒᵖ) {N N' : B} (f : N' ⟶ N) (g : N ⟶ F.obj K) :
      e K N' (f ≫ g) = f ≫ e K N g := costalkHomEquiv_left SA SB adj p O _ f g
  let c (K : Aᵒᵖ) : F.obj K ≅ G.obj K :=
    Yoneda.ext _ _ (fun {N} ↦ e K N) (fun {N} ↦ (e K N).symm)
      (fun _ ↦ (e K _).symm_apply_apply _) (fun _ ↦ (e K _).apply_symm_apply _)
      (fun f g ↦ hn K f g)
  have hc (K : Aᵒᵖ) (N : B) (g : N ⟶ F.obj K) :
      g ≫ (c K).hom = e K N g := by
    change g ≫ e K (F.obj K) (𝟙 _) = e K N g
    simpa using (hn K g (𝟙 _)).symm
  refine ⟨NatIso.ofComponents c ?_⟩
  intro K K' f
  rw [hc]
  change e K' (F.obj K) (F.map f) =
    e K (F.obj K) (𝟙 _) ≫ G.map f
  simpa [e, F, G] using
    costalkHomEquiv_source SA SB adj p O f.unop (F.obj K) (𝟙 _)


end FormalDuality

namespace AlgebraicGeometry.Scheme

/-- Modules over arbitrary commutative etale coefficients, without boundedness.
Source: Stacks, Modules on Sites, Tag 03D1
(blueprint: lem-weil-closed-costalk-duality). -/
abbrev closedCostalkEtaleModules (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard ordinary unbounded localization on the small etale site.
Source: Stacks, Tag 05RU (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable instance closedCostalkEtaleModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :
    HasDerivedCategory (closedCostalkEtaleModules X R) :=
  HasDerivedCategory.standard _

/-- Ring inverse image, by left Kan extension and sheafification on the actual etale sites.
Source: Stacks, Tags 00VC and 00WX (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleRingPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology CommRingCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology CommRingCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- The canonical ring-sheaf adjunction determining the coefficient unit.
Source: Stacks, Tag 00YV (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleRingAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    closedCostalkEtaleRingPullback f ⊣
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
        (X.smallGrothendieckTopology @Etale) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- Actual closed direct image with scalars restricted through the inverse-image unit.
Source: Stacks, Modules on Sites, Tag 03D6
(blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleModulePush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R) ⥤
      closedCostalkEtaleModules Y R :=
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.pullback @Etale ⊤ f)
    (J := Y.smallGrothendieckTopology @Etale) (K := X.smallGrothendieckTopology @Etale)
    (S := (sheafCompose Y.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (R := (sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((closedCostalkEtaleRingPullback f).obj R))
    ⟨Functor.whiskerRight ((closedCostalkEtaleRingAdjunction f).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Closed direct image is additive since its linear components are unchanged.
Source: Stacks, Tag 03D6 (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable instance closedCostalkEtaleModulePush_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    (closedCostalkEtaleModulePush f R).Additive where
  map_add := by intros; rfl

-- The recorded open-complement coefficient is intentionally unused in the conclusion.
set_option linter.unusedVariables false in
/-- Exceptional restriction of derived internal Hom, on the small etale site.
The underived inverse image is specified by its adjunction to the actual module
pushforward; the two factorization isomorphisms specify termwise descent through Q.
Thus all presentations of the source's exact inverse image and closed direct image
are allowed, and their derived functors are determined up to unique isomorphism.

Source: current blueprint, six-functors basics, closed-costalk-duality;
Stacks, Tags 04CA, 07A4, 08J9 and 08JA (blueprint: lem-weil-closed-costalk-duality).

Proof:
1. Closed pushforward is exact and fully faithful, with invertible inverse-image
counit, by lem-kun-04ca and the closed geometric-stalk formula. Geometric stalks
are exact and conservative. Its composite with complementary open restriction is zero.
2. Exact inverse image and closed direct image descend termwise. Pullback commutes
with derived tensor (lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
3. The projection morphism i_*N tensor K -> i_*(N tensor i^*K), adjoint to
pullback-tensor comparison followed by the closed counit, is invertible: its
closed restriction is invertible and its open restriction is a map of zero objects.
Apply both restrictions to its cone; joint detection makes the cone zero.
4. Currying and derived global Hom (lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-pur-rhom-global-sections) give Hom(P,RHom(Q,L)) = Hom(P tensor Q,L).
5. For every N, apply the exceptional adjunction, tensor-Hom, the inverse projection
identity, the exceptional adjunction again, and tensor-Hom. This identifies
Hom(N,Ri! RHom(K,omega)) with Hom(N,RHom(i^*K,Ri!omega)).
6. These bijections are natural in N and K. Their values on identities and their
inverse values on identities give mutually inverse Yoneda maps, natural in K.
All arrows are induced by adjunction and evaluation, as in the source.

The Lean proof uses the normalized closed tensor-Hom model for step 4, and delegates
steps 1--3 to closedImmersionEtaleProjection. The Hom-chain naturality and Yoneda
construction in steps 5--6 are proved directly in this module. -/
theorem exceptionalRestrictionVerdierDuality_etale
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1})
    (iStar : closedCostalkEtaleModules T R ⥤
      closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R))
    [iStar.Additive] (_ai : iStar ⊣ closedCostalkEtaleModulePush i R)
    (iPull : DerivedCategory (closedCostalkEtaleModules T R) ⥤
      DerivedCategory (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (_pullFactors : DerivedCategory.Q ⋙ iPull ≅
      iStar.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (iPush : DerivedCategory
        (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)) ⥤
      DerivedCategory (closedCostalkEtaleModules T R))
    (_pushFactors : DerivedCategory.Q ⋙ iPush ≅
      (closedCostalkEtaleModulePush i R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (riExcl : DerivedCategory (closedCostalkEtaleModules T R) ⥤ DerivedCategory
      (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (_adj : iPush ⊣ riExcl) (ωT : DerivedCategory (closedCostalkEtaleModules T R)) :
    let ΛU := (closedCostalkEtaleRingPullback j).obj R
    Nonempty
      ((((𝟭 (DerivedCategory (closedCostalkEtaleModules T R))ᵒᵖ).prod'
          ((Functor.const _).obj ωT)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} T.smallEtaleTopology R) ⋙ riExcl ≅
      iPull.op ⋙ ((𝟭 _).prod' ((Functor.const _).obj (riExcl.obj ωT))) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} Z.smallEtaleTopology
          ((closedCostalkEtaleRingPullback i).obj R)) := by
  intro ΛU
  clear ΛU
  obtain ⟨t⟩ := ringedSiteDualityMaps_exists.{u + 1, u, 0, u + 2}
    T.smallEtaleTopology R
  obtain ⟨z⟩ := ringedSiteDualityMaps_exists.{u + 1, u, 0, u + 2}
    Z.smallEtaleTopology ((closedCostalkEtaleRingPullback i).obj R)
  obtain ⟨p⟩ := closedImmersionEtaleProjection i j _hij R iStar _ai iPull
    _pullFactors iPush _pushFactors t z
  exact costalkDualityOfProjection t.closed z.closed _adj p ωT

-- The recorded open-complement coefficient is intentionally unused in the conclusion.
set_option linter.unusedVariables false in
/-- Exceptional restriction of a Verdier dual, on the small pro-etale site.
Here the open complement is quasi-compact, as required for the ringed recollement.
The coefficient ring on Z is exactly the actual inverse image of R; its identification
in the recorded ringed derived operations is the identity. The dualizing object on Z
is Ri!omegaT itself, and both duals are the recorded K-injective internal Hom.

Source: current blueprint, six-functors basics, closed-costalk-duality;
Stacks, Tags 09AA, 09BM, 09AH, 07A4, 08J9 and 08JA
(blueprint: lem-weil-closed-costalk-duality).

Proof: follow the six steps in exceptionalRestrictionVerdierDuality_etale, replacing
geometric-stalk detection in step 1 by lem-weil-pbc-proetale-ringed-open-closed.
Its quasi-compact-complement hypothesis is supplied by j. The closed counit and the
open-closed exact sequence give joint detection, so the projection map is invertible
on arbitrary unbounded complexes. The ringed tensor-Hom and global-Hom comparisons
and the assumed ambient exceptional adjunction give the same natural Hom chain.
Yoneda gives the natural isomorphism, without a biduality or Tor bound.

The Lean proof uses the normalized closed tensor-Hom model and the separate
closedImmersionProEtaleProjection statement. The Hom-chain and both naturality
checks are the same proved categorical argument as on the etale site. -/
theorem exceptionalRestrictionVerdierDuality
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (riExcl : DerivedCategory (proEtaleRingModules T R) ⥤ DerivedCategory
      (proEtaleRingModules Z ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)))
    (_adj : proEtaleRingDerivedDirectImage i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) ⊣ riExcl)
    (ωT : DerivedCategory (proEtaleRingModules T R)) :
    let ΛU := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
    Nonempty
      ((((𝟭 (DerivedCategory (proEtaleRingModules T R))ᵒᵖ).prod'
          ((Functor.const _).obj ωT)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology T) R) ⋙ riExcl ≅
      (proEtaleRingDerivedPullback i R
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).op ⋙
      ((𝟭 _).prod' ((Functor.const _).obj (riExcl.obj ωT))) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology Z)
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)) := by
  intro ΛU
  clear ΛU
  obtain ⟨t⟩ := ringedSiteDualityMaps_exists.{u + 1, u, 0, u + 2}
    (ProEt.topology T) R
  obtain ⟨z⟩ := ringedSiteDualityMaps_exists.{u + 1, u, 0, u + 2}
    (ProEt.topology Z) ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
  obtain ⟨p⟩ := closedImmersionProEtaleProjection i j _hij R t z
  exact costalkDualityOfProjection t.closed z.closed _adj p ωT

end AlgebraicGeometry.Scheme
