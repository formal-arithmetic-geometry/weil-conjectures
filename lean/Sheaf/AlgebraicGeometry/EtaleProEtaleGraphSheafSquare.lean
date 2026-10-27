/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Compactification.Defs
public import Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import Sheaf.AlgebraicGeometry.ProEtaleCompactifiedGraphExistence
import Sheaf.AlgebraicGeometry.CompactifiedGraphComparisonGenerators

/-! # The adjunction-normalized compactification graph square

Source: Stacks Project, Tags 09AF and 0F4L
(blueprint: lem-sp-et-proet-graph-sheaf-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The sheafified sum extension for an etale morphism, without a mono assumption.
This is left Kan extension along the opposite localization followed by sheafification.
Source: Stacks, Tags 03DH and 09AF (blueprint: lem-sp-et-proet-graph-sheaf-square). -/
def etaleSumExtension (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale e))
    (ModuleCat.{u + 1} A) (Scheme.ProEt.topology U) (Scheme.ProEt.topology T)

/-- The actual sum-extension/restriction adjunction, including its generator unit.
Source: Stacks, Tags 03DH and 09AF (blueprint: lem-sp-et-proet-graph-sheaf-square). -/
def etaleSumAdjunction (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    etaleSumExtension A e ⊣ localizationRestriction (ModuleCat.{u + 1} A) e
      (inferInstance : WeaklyEtale e) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale e))
    (ModuleCat.{u + 1} A) (Scheme.ProEt.topology U) (Scheme.ProEt.topology T)

/-- The common right adjoint is restriction along the same composite inclusion.
Source: Stacks, Tag 09AF (blueprint: lem-sp-et-proet-graph-sheaf-square). -/
def etaleSumComparisonRestrictionIso (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙
        Etale.localizationRestriction (ModuleCat.{u + 1} A) e inferInstance ≅
      localizationRestriction (ModuleCat.{u + 1} A) e inferInstance ⋙
        comparisonLowerStar (ModuleCat.{u + 1} A) U :=
  Iso.refl _

/-- The unique comparison preserving the composite adjunctions.
Source: Stacks, Tag 09AF (blueprint: lem-sp-et-proet-graph-sheaf-square). -/
def etaleSumComparisonIso (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙ etaleSumExtension A e :=
  (((Etale.etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
    (comparisonAdjunction (ModuleCat.{u + 1} A) T)).ofNatIsoRight
      (etaleSumComparisonRestrictionIso A e)).leftAdjointUniq
    ((comparisonAdjunction (ModuleCat.{u + 1} A) U).comp (etaleSumAdjunction A e))

/-- The underived counit mate of the inverse pullback comparison.
Source: Stacks, Tag 0B65 (blueprint: lem-sp-et-proet-graph-sheaf-square). -/
def graphComparisonDirectImageMate (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (p : Z ⟶ T) :
    Etale.lowerStar (ModuleCat.{u + 1} A) p ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) T ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) Z ⋙ lowerStar (ModuleCat.{u + 1} A) p :=
  (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (TwoSquare.mk (comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (Etale.upperStar (ModuleCat.{u + 1} A) p) (upperStar (ModuleCat.{u + 1} A) p)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
      (comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) p).inv)).natTrans

/-- A graph map has the prescribed value on each sheafification generator: its
restriction to the graph is the open-extension unit, and it is zero on the complement.
The graph is specified by both fibre-product projections, so there is no free map.
Source: Stacks, Tag 0F4L (blueprint: lem-sp-et-proet-graph-sheaf-square). -/
def IsCompactifiedProEtaleGraphMap (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (c : Compactification e)
    (G : etaleSumExtension A e ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g) : Prop :=
  ∀ (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)) (b : U.ProEt),
    ∃ γ :
      (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
        (inferInstance : WeaklyEtale c.i)).obj b ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c.g).obj
        ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
          (inferInstance : WeaklyEtale e)).obj b),
      γ.left ≫ pullback.fst (b.hom ≫ e) c.g = 𝟙 b.left ∧
      γ.left ≫ pullback.snd (b.hom ≫ e) c.g = b.hom ≫ c.i ∧
      IsOpenImmersion γ.left ∧ IsClosedImmersion γ.left ∧
      ∀ m : M.obj.obj (op b),
        (((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M).obj.map γ.op)
          (((G.app M).hom.app
            (op ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
              (inferInstance : WeaklyEtale e)).obj b)))
            (((etaleSumAdjunction A e).unit.app M).hom.app (op b) m)) =
          (((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) c.i).unit.app M).hom.app
            (op b) m) ∧
        ∀ (D : c.Z.ProEt)
          (k : D ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c.g).obj
            ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
              (inferInstance : WeaklyEtale e)).obj b)),
          IsOpenImmersion k.left → Set.range k.left = (Set.range γ.left)ᶜ →
          (((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M).obj.map k.op)
            (((G.app M).hom.app
              (op ((MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
                (inferInstance : WeaklyEtale e)).obj b)))
              (((etaleSumAdjunction A e).unit.app M).hom.app (op b) m)) = 0

/-- The normalized comparison preserves raw lift generators and the compactified graphs.
Source: Stacks, Tags 09AF and 0F4L
(blueprint: lem-sp-et-proet-graph-sheaf-square).

Proof:
1. Use the constant-coefficient comparison exactness, weakly etale localization and
localized module adjunction to identify both sum extensions as exact left adjoints of
restriction. Localization of the comparison identifies the right adjoints sectionwise.
Composite adjunctions and the conjugate-isomorphism unit equation give the unique sigma.
Use lem-sf-comparison-pullback-exact, lem-weil-proetale-weakly-etale-localization,
lem-pur-site-restriction-module-adjunction-exact, lem-amb-etale-adjoint-locality and
lem-weil-pbc-localize-ringed-site-morphism; identify etale restriction using
lem-weil-pbc-etale-inverse-image-restriction.
2. Transpose the identity of the pro-etale sum extension. The comparison unit followed
by the pro-etale sum unit inserts m in the same lift summand. Direct-sum elimination
and the sheafification universal property give the displayed generator equation
(def-weil-extension-by-zero-presheaf, def-weil-presheaf-modules-sheafification).
3. For each test scheme the compactified graph is open and closed. The open-extension
unit gives the value on the graph; glue it with zero on the complement. Uniqueness of
gluing proves compatibility with restrictions and module-sheaf maps. Sheafification
therefore gives the natural graph map. On the etale site this is the existing canonical
etaleCompactificationGraphMap. Use lem-weil-pbc-extension-by-zero-unit-iso for
the open-extension unit. The pro-etale construction is also the constant-system
case of lem-sp-semilinear-compactified-graph-evaluation.
4. Expand the counit mate. The conjugate unit equation cancels the inverse pullback
comparison; naturality of the comparison unit and the proper-map triangle identity give
R_T(d) eta_T = p_* eta_Z. No invertibility of d is used.
The dependencies are def-weil-pbc-adjunction-mate, lem-weil-pbc-comparison-pullback,
def-weil-pbc-composite-adjunction and lem-weil-pbc-conjugate-iso-unit-equation.
5. The open-comparison unit normalization and comparison-pullback open-unit equation
identify the restriction of R_Z(o) eta_Z on U with eta_U. It therefore sends the etale
graph extension of m to the pro-etale graph extension of eta_U(m): both have that value
on the graph and zero on its complement. Uniqueness of disjoint-open gluing applies.
Use lem-sf-open-comparison-unit-normalization, lem-pur-comparison-pullback-open-unit,
lem-cbc-proetale-extension-zero-comparison and lem-exc-proetale-open-unit.
6. Transpose both sides of the square under comparison. Steps 2, 4 and 5 identify their
values on each presheaf summand. The direct-sum and sheafification universal properties
make the transposes equal, hence the original maps equal. Each construction commutes
with a sheaf morphism. The same generator argument (values on the graph and zero on its
complement, then the direct-sum and sheafification universal properties) proves that the
graph conditions alone determine the graph map.
-/
theorem etale_proEtale_graph_sheaf_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    PreservesFiniteLimits (etaleSumExtension A e) ∧
    PreservesFiniteColimits (etaleSumExtension A e) ∧
    PreservesFiniteLimits (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance) ∧
    PreservesFiniteColimits (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance) ∧
    (∀ σ : Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
          comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
        comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙ etaleSumExtension A e,
      (conjugateIsoEquiv
        ((comparisonAdjunction (ModuleCat.{u + 1} A) U).comp (etaleSumAdjunction A e))
        ((Etale.etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
          (comparisonAdjunction (ModuleCat.{u + 1} A) T))) σ =
            (etaleSumComparisonRestrictionIso A e).symm → σ = etaleSumComparisonIso A e) ∧
    (∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (b : U.Etale)
      (m : M.obj.obj (op b)),
      (((comparisonLowerStar (ModuleCat.{u + 1} A) T).map
        ((etaleSumComparisonIso A e).hom.app M)).hom.app
          (op ((MorphismProperty.Over.map (P := @Etale) ⊤
            (inferInstance : Etale e)).obj b)))
        ((((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).hom.app
            (op ((MorphismProperty.Over.map (P := @Etale) ⊤
              (inferInstance : Etale e)).obj b)))
          ((((Etale.etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e
            inferInstance).unit.app M).hom.app (op b)) m)) =
        (((etaleSumAdjunction A e).unit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj M)).hom.app
            (op ((Scheme.toProEt U).obj b)))
          ((((comparisonAdjunction (ModuleCat.{u + 1} A) U).unit.app M).hom.app (op b)) m)) ∧
    ∃ G : etaleSumExtension A e ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
          lowerStar (ModuleCat.{u + 1} A) c.g,
      (∀ G' : etaleSumExtension A e ⟶
          openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
            lowerStar (ModuleCat.{u + 1} A) c.g,
        IsCompactifiedProEtaleGraphMap A e c G' ↔ G' = G) ∧
      ∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
        (etaleSumComparisonIso A e).hom.app M ≫
          G.app ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj M) =
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).map
            ((Etale.etaleCompactificationGraphMap A e c).app M) ≫
          (graphComparisonDirectImageMate A c.g).app
            ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) ≫
          (lowerStar (ModuleCat.{u + 1} A) c.g).map
            ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A)
              c.i).hom.app M) := by
  let adj₁ := (Etale.etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
    (comparisonAdjunction (ModuleCat.{u + 1} A) T)
  let adj₂ := (comparisonAdjunction (ModuleCat.{u + 1} A) U).comp (etaleSumAdjunction A e)
  have ht : adj₁.ofNatIsoRight (etaleSumComparisonRestrictionIso A e) = adj₁ := by
    apply Adjunction.ext
    ext M
    simp [Adjunction.ofNatIsoRight, etaleSumComparisonRestrictionIso]
  have hs : etaleSumComparisonIso A e = adj₁.leftAdjointUniq adj₂ := by
    unfold etaleSumComparisonIso
    change (adj₁.ofNatIsoRight _).leftAdjointUniq adj₂ = _
    rw [ht]
  have hlan := SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian
    (ModuleCat.{u + 1} A) (P := @WeaklyEtale) (inferInstance : WeaklyEtale e)
  have hlim : PreservesFiniteLimits (etaleSumExtension A e) := by
    unfold etaleSumExtension Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  have hcol := (etaleSumAdjunction A e).leftAdjoint_preservesColimits
  have hgen : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (b : U.Etale)
      (m : M.obj.obj (op b)),
      (((comparisonLowerStar (ModuleCat.{u + 1} A) T).map
        ((etaleSumComparisonIso A e).hom.app M)).hom.app
          (op ((MorphismProperty.Over.map (P := @Etale) ⊤
            (inferInstance : Etale e)).obj b)))
        ((((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).hom.app
            (op ((MorphismProperty.Over.map (P := @Etale) ⊤
              (inferInstance : Etale e)).obj b)))
          ((((Etale.etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e
            inferInstance).unit.app M).hom.app (op b)) m)) =
        (((etaleSumAdjunction A e).unit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj M)).hom.app
            (op ((Scheme.toProEt U).obj b)))
          ((((comparisonAdjunction (ModuleCat.{u + 1} A) U).unit.app M).hom.app (op b)) m) := by
    intro M b m
    have h := adj₁.unit_leftAdjointUniq_hom_app adj₂ M
    rw [← hs] at h
    dsimp only [adj₁, adj₂, Adjunction.comp_unit_app] at h
    have hh := congrArg (fun f ↦ f.hom.app (op b)) h
    exact ConcreteCategory.congr_hom hh m
  refine ⟨hlim, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro σ hσ
    apply (conjugateIsoEquiv adj₂ adj₁).injective
    rw [hσ, hs]
    apply Iso.ext
    exact (conjugateEquiv_leftAdjointUniq_hom adj₁ adj₂).symm
  · exact hgen
  · obtain ⟨G, hG, huniq⟩ := compactified_graph_existsUnique A e c
      (etaleSumExtension A e) (etaleSumAdjunction A e)
    refine ⟨G, ?_, ?_⟩
    · intro G'
      constructor
      · intro hG'
        exact huniq G' hG'
      · rintro rfl
        exact hG
    · exact compactified_graph_comparison_of_generators A e c
        (etaleSumExtension A e) (etaleSumAdjunction A e)
        (etaleSumComparisonIso A e) hgen G hG

/-- The canonical pro-etale graph map, extracted from its unique graph specification.
The theorem determines this natural transformation up to equality; no unspecified
isomorphism or arbitrary map is chosen.
Source: Stacks, Tags 09AF and 0F4L (blueprint: lem-sp-et-proet-graph-sheaf-square). -/
def compactifiedProEtaleGraphMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    etaleSumExtension A e ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g :=
  (etale_proEtale_graph_sheaf_square A e c).2.2.2.2.2.2.choose

end AlgebraicGeometry.ProEtale
