module

public import Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation
public import Sheaf.CategoryTheory.SiteHypercoverDisjointUnion
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.AlgebraicGeometry.ProEtaleHypercoverQuasiIso
import Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveRow
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveComparison
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple

/-!
# Augmentation-normalized single-site hypercover descent

Source: Stacks Project, Tags 09A2 and 0946; Derived Categories, Tags 070I, 070J, 070Y.
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt.NormalizedDescent

/-- The recorded module category, with no new objects or morphisms.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
abbrev Modules (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1}
    ((sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- Ordinary module evaluation followed by forgetting scalars.
Source: Stacks, Tags 09A2 and 0946
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def evaluation (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) : Modules X R ⥤ AddCommGrpCat.{u + 1} :=
  SheafOfModules.evaluation _ (op W) ⋙ forget₂ (ModuleCat _) AddCommGrpCat

/-- Evaluation is additive, since its maps are the sectionwise linear maps.
Source: Stacks, Tag 0946
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: evaluate the sum of two sheaf morphisms; its underlying additive map is
by definition the sum of their evaluated maps. -/
theorem evaluation_additive (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt) :
    (evaluation X R W).Additive := by
  constructor
  intro M N f g
  rfl

attribute [instance] evaluation_additive

/-- The published signed total followed by forgetting scalars.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def total (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W)) :=
  hypercoverTotal X R W U ⋙
    (forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ)

/-- The published restriction augmentation, followed by forgetting scalars.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def augmentation (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W)) :
    (evaluation X R W).mapHomologicalComplex (.up ℤ) ⟶ total X R W U :=
  Functor.whiskerRight (hypercoverAugmentation X R W U)
    ((forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ))

/-- The matching-object existence and covering conditions in the slice over W.
Source: Stacks, Tag 09A2, and the recorded proper-face matching predicate
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def IsHypercover (X : Scheme.{u}) (W : X.ProEt) (U : SimplicialObject (Over W)) : Prop :=
  ∀ n : ℕ, ∃ (M : Over W) (μ : U _⦋n⦌ ⟶ M),
    SimplicialObject.IsProperFaceMatchingArrow U n M μ ∧
      Sieve.generate (Presieve.singleton μ.left) ∈ topology X M.left

variable (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
  (W : X.ProEt) (U : SimplicialObject (Over W))

/-- Cache the existing abelian sheafification instance for this site.
Source: Mathlib sheafification on essentially small sites
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
theorem site_hasSheafify : HasSheafify (topology X) AddCommGrpCat.{u + 1} :=
  inferInstance

/-- Cache the existing local-bijection characterization on this site.
Source: Mathlib sheafification on essentially small sites
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
theorem site_wEqualsLocallyBijective :
    (topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

attribute [local instance] site_hasSheafify site_wEqualsLocallyBijective

private instance module_smallCoproducts (A : Type (u + 1)) [Ring A] :
    HasCoproducts.{0} (ModuleCat.{u + 1} A) := by infer_instance

/-- Supply total coproducts directly, without searching through reducible function types. -/
private instance (priority := 2000) bicomplex_hasTotal
    {A : Type*} [Category* A] [Preadditive A] [HasCoproducts.{0} A]
    (K : HomologicalComplex₂ A (.up ℤ) (.up ℤ)) : K.HasTotal (.up ℤ) :=
  fun _ ↦ HasColimitsOfShape.has_colimit _

private instance forget_preservesHomology (A : Type (u + 1)) [Ring A] :
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).PreservesHomology := by
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} A
  infer_instance

private instance moduleEvaluation_additive (V : X.ProEt) :
    (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op V)).Additive := by
  constructor
  intro M N f g
  rfl

private theorem yoneda_epi_of_cover {A B : X.ProEt} (f : A ⟶ B)
    (hf : Sieve.generate (Presieve.singleton f) ∈ topology X B) :
    Epi ((topology X).yoneda.map f) := by
  constructor
  intro F g h heq
  apply (topology X).yonedaEquiv.injective
  apply Sheaf.isSeparated F B _ hf
  rintro V k ⟨Z, a, b, hb, hab⟩
  cases hb
  subst k
  have he := congrArg (topology X).yonedaEquiv heq
  rw [← (topology X).yonedaEquiv_naturality,
    ← (topology X).yonedaEquiv_naturality] at he
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using congrArg (F.obj.map a.op) he

private theorem comp_preservesHomology
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesHomology] [G.PreservesHomology] : (F ⋙ G).PreservesHomology := by
  have := Functor.preservesFiniteLimits_of_preservesHomology F
  have := Functor.preservesFiniteColimits_of_preservesHomology F
  have := Functor.preservesFiniteLimits_of_preservesHomology G
  have := Functor.preservesFiniteColimits_of_preservesHomology G
  infer_instance

/-- Exact evaluation at every simplex, with no affineness assumption.
Source: Stacks, Tag 0946 (1)
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: weak contractibility lifts sections of epimorphisms of set sheaves.
Module epimorphisms are locally surjective; hence evaluation preserves epimorphisms.
Kernels are sectionwise. Thus evaluation is exact and preserves homology.
Forgetting scalars preserves kernels and cokernels as well. -/
theorem evaluation_exact
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left) :
    ∀ p : ℕ, (evaluation X R (U _⦋p⦌).left).PreservesHomology := by
  intro p
  have := weaklyContractible_evaluation_preservesHomology X R (U _⦋p⦌).left
    (fun F G f hf ↦ hweak p f ((Sheaf.isLocallySurjective_iff_epi f).mpr hf))
  change (SheafOfModules.evaluation.{u + 1} _ (op (U _⦋p⦌).left) ⋙
    forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).PreservesHomology
  exact comp_preservesHomology _ _

/-- Exact simplex evaluation preserves all coefficient quasi-isomorphisms.
Source: Stacks, Tags 0946 and 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: evaluation_exact commutes with homology, so the homology map is the
image of an isomorphism. No boundedness is required for this clause. -/
theorem evaluation_quasiIso
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (E F : CochainComplex (Modules X R) ℤ) (f : E ⟶ F) [QuasiIso f] (p : ℕ) :
    QuasiIso (((evaluation X R (U _⦋p⦌).left).mapHomologicalComplex (.up ℤ)).map f) := by
  have := evaluation_exact X R W U hweak p
  infer_instance

/-- Signed totals preserve quasi-isomorphisms between strictly bounded-below complexes.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: choose the minimum of the two lower bounds. Simplex evaluation makes each
column a quasi-isomorphism. Both bicomplexes vanish for p<0 or q below that bound;
apply lem-weil-pbc-bounded-below-total-column-comparison. Each effective diagonal
has only 0≤p≤n-N, so no convergence or affineness hypothesis is required. -/
theorem total_quasiIso
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (E F : CochainComplex (Modules X R) ℤ) (NE NF : ℤ)
    [E.IsStrictlyGE NE] [F.IsStrictlyGE NF] (f : E ⟶ F) [QuasiIso f] :
    QuasiIso ((total X R W U).map f) := by
  have h : QuasiIso ((hypercoverTotal X R W U).map f) :=
    hypercoverTotal_map_quasiIso_of_weaklyContractible X R W U
    (fun p F G f hf ↦ hweak p f ((Sheaf.isLocallySurjective_iff_epi f).mpr hf))
    ⟨E, NE, inferInstance⟩ ⟨F, NF, inferInstance⟩ ⟨f⟩ inferInstance
  change QuasiIso (((forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).map ((hypercoverTotal X R W U).map f))
  exact inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Restriction augmentation is a quasi-isomorphism for every bounded-below
termwise-injective complex.
Source: Stacks, Tags 09A2, 01GE and 01GW
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: subcanonicity and covering matching arrows give epimorphic represented
matching maps, including degree zero W. Apply the ringed hypercover injective-row
lemma to each injective module sheaf; its underlying abelian sheaf need not be
injective. Apply the bounded-below row augmentation comparison to those exact rows.
This is the actual restriction augmentation into bidegree (0,q). -/
theorem augmentation_quasiIso (hcover : IsHypercover X W U)
    (I : CochainComplex (Modules X R) ℤ) (N : ℤ)
    [I.IsStrictlyGE N] [∀ n : ℤ, Injective (I.X n)] :
    QuasiIso ((augmentation X R W U).app I) := by
  have hepi (n : ℕ) : ∃ (M : Over W) (μ : U _⦋n⦌ ⟶ M),
      SimplicialObject.IsProperFaceMatchingArrow U n M μ ∧
        Epi ((topology X).yoneda.map μ.left) := by
    obtain ⟨M, μ, hμ, hc⟩ := hcover n
    exact ⟨M, μ, hμ, yoneda_epi_of_cover X μ.left hc⟩
  have hzero : Epi ((topology X).yoneda.map (U _⦋0⦌).hom) := by
    obtain ⟨M, μ, ⟨hM⟩, hμ⟩ := hepi 0
    have : IsIso M.hom := by
      let e := hM.uniqueUpToIso (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 W)))
      have he : e.hom.left = M.hom := by simpa using e.hom.w
      rw [← he]
      infer_instance
    rw [← μ.w, Functor.map_comp]
    infer_instance
  have hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt, (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((topology X).yoneda.map μ.left) := by
    obtain ⟨M, μ, ⟨p, hp, hμ⟩, he⟩ := hepi 1
    exact ⟨Fan.mk M p, hp, μ, hμ, he⟩
  have hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left) := by
    intro n
    obtain ⟨M, μ, ⟨c, hc, e, he⟩, hμ⟩ := hepi (n + 2)
    refine ⟨c, hc, μ ≫ e.hom, ?_, ?_⟩
    · simpa only [Category.assoc] using he
    · change Epi ((topology X).yoneda.map (μ.left ≫ e.hom.left))
      rw [Functor.map_comp]
      infer_instance
  have := hypercoverAugmentation_quasiIso_of_injective_rows X R W U
    (fun J hJ ↦ hypercoverRowAugmentationComplex_quasiIso_of_injective
      X R W U hzero hone hhigher J) ⟨I, N, inferInstance⟩ (fun n ↦ inferInstance)
  change QuasiIso (((forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).map ((hypercoverAugmentation X R W U).app I))
  infer_instance


/-- Every coefficient complex has a K-injective resolution on the chosen small site.
Source: Stacks, Tag 079P, as used in Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: apply prop-pur-kinjective-resolutions-exist to the site with object universe
u+1, morphism universe u, and coefficient universe u+1. Its functorial resolution
supplies the stated quasi-isomorphism and K-injectivity; discard termwise injectivity. -/
theorem coefficient_resolutions :
    ∀ K : CochainComplex (Modules X R) ℤ,
      ∃ (I : CochainComplex (Modules X R) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s := by
  obtain ⟨_, _, I, η, hη⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{_, _, 0}
      (topology X) R
  intro K
  exact ⟨I.obj K, η.app K, (hη K).2.1, (hη K).1⟩

private abbrev flipMap {A : Type*} [Category* A] [HasZeroMorphisms A]
    {K L : HomologicalComplex₂ A (.up ℤ) (.up ℤ)} (f : K ⟶ L) :
    HomologicalComplex₂.flip K ⟶ HomologicalComplex₂.flip L :=
  (HomologicalComplex₂.flipFunctor A (.up ℤ) (.up ℤ)).map f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def totalHomotopy
    {A : Type*} [Category* A] [Preadditive A]
    {K L : HomologicalComplex₂ A (.up ℤ) (.up ℤ)}
    [(HomologicalComplex₂.flip K).HasTotal (.up ℤ)]
    [(HomologicalComplex₂.flip L).HasTotal (.up ℤ)] {f g : K ⟶ L}
    (h : Homotopy f g) :
    Homotopy (HomologicalComplex₂.total.map (flipMap f) (.up ℤ))
      (HomologicalComplex₂.total.map (flipMap g) (.up ℤ)) := by
  classical
  let H : ∀ n m : ℤ, ((HomologicalComplex₂.flip K).total (.up ℤ)).X n ⟶
      ((HomologicalComplex₂.flip L).total (.up ℤ)).X m :=
    fun n m ↦ (HomologicalComplex₂.flip K).totalDesc (fun p q _ ↦
      ((-1 : ℤˣ) ^ p) • (h.hom q (q - 1)).f p ≫
        (HomologicalComplex₂.flip L).ιTotalOrZero (.up ℤ) p (q - 1) m)
  have hH (p q n m : ℤ) (hpq : p + q = n) :
      (HomologicalComplex₂.flip K).ιTotal (.up ℤ) p q n hpq ≫ H n m =
        ((-1 : ℤˣ) ^ p) • (h.hom q (q - 1)).f p ≫
          (HomologicalComplex₂.flip L).ιTotalOrZero (.up ℤ) p (q - 1) m := by
    exact (HomologicalComplex₂.flip K).ι_totalDesc _ _ _ _
  refine { hom := H, zero := ?_, comm := ?_ }
  · intro n m hnm
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rw [hH, (HomologicalComplex₂.flip L).ιTotalOrZero_eq_zero _ _ _ _ (by
      change ¬ m + 1 = n at hnm
      change p + q = n at hpq
      change ¬ p + (q - 1) = m
      omega), comp_zero, smul_zero, comp_zero]
  · intro n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p + q = n at hpq
    subst n
    simp only [HomologicalComplex₂.ιTotal_map, Preadditive.comp_add]
    change ((f.f q).f p ≫ (HomologicalComplex₂.flip L).ιTotal (.up ℤ) p q (p + q) rfl :
        ((HomologicalComplex₂.flip K).X p).X q ⟶ _) =
      (HomologicalComplex₂.flip K).ιTotal (.up ℤ) p q (p + q) rfl ≫
        ((HomologicalComplex₂.flip K).total (.up ℤ)).d (p + q) (p + q + 1) ≫ H (p + q + 1) (p + q) +
      (HomologicalComplex₂.flip K).ιTotal (.up ℤ) p q (p + q) rfl ≫ H (p + q) (p + q - 1) ≫
        ((HomologicalComplex₂.flip L).total (.up ℤ)).d (p + q - 1) (p + q) +
      ((g.f q).f p ≫ (HomologicalComplex₂.flip L).ιTotal (.up ℤ) p q (p + q) rfl :
        ((HomologicalComplex₂.flip K).X p).X q ⟶ _)
    simp only [← Category.assoc]
    rw [hH, (HomologicalComplex₂.flip L).ιTotalOrZero_eq (.up ℤ) p (q - 1) (p + q - 1) (by
      change p + (q - 1) = p + q - 1; omega)]
    simp only [HomologicalComplex₂.total_d, Preadditive.comp_add,
      Preadditive.add_comp, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    simp only [Category.assoc, Linear.units_smul_comp,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [(HomologicalComplex₂.flip K).d₁_eq' (.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      (HomologicalComplex₂.flip K).d₂_eq' (.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl),
      (HomologicalComplex₂.flip L).d₁_eq' (.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      (HomologicalComplex₂.flip L).d₂_eq' (.up ℤ) p
        (show (ComplexShape.up ℤ).Rel (q - 1) q by simp)]
    rw [(HomologicalComplex₂.flip K).ιTotalOrZero_eq (.up ℤ) (p + 1) q (p + q + 1) (by
      change p + 1 + q = p + q + 1; omega),
      (HomologicalComplex₂.flip K).ιTotalOrZero_eq (.up ℤ) p (q + 1) (p + q + 1) (by
        change p + (q + 1) = p + q + 1; omega)]
    simp only [Linear.units_smul_comp, Category.assoc, hH, Linear.comp_units_smul]
    rw [(HomologicalComplex₂.flip L).ιTotalOrZero_eq (.up ℤ) (p + 1) (q - 1) (p + q) (by
      change p + 1 + (q - 1) = p + q; omega),
      (HomologicalComplex₂.flip L).ιTotalOrZero_eq (.up ℤ) p (q + 1 - 1) (p + q) (by
        change p + (q + 1 - 1) = p + q; omega),
      (HomologicalComplex₂.flip L).ιTotalOrZero_eq (.up ℤ) p q (p + q) rfl]
    have he₁ (a b : ℤ) :
        ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (a, b) = 1 := rfl
    have he₂ (a b : ℤ) :
        ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (a, b) = (-1 : ℤˣ) ^ a := rfl
    simp only [he₁, he₂, one_smul, smul_smul, Int.units_mul_self,
      one_smul, zpow_add, zpow_one, mul_neg, mul_one, Units.neg_smul]
    have hn := (h.hom q (q - 1)).comm p (p + 1)
    have hc := congrArg (fun z ↦ z.f p) (h.comm q)
    simp only [dNext_eq _ (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (q - 1) q by simp),
      HomologicalComplex.add_f_apply, HomologicalComplex.comp_f] at hc
    change (f.f q).f p ≫ _ = _
    rw [hc]
    simp only [Preadditive.add_comp, Category.assoc]
    simp only [HomologicalComplex₂.flip_d_f, HomologicalComplex₂.flip_X_d]
    erw [← reassoc_of% hn]
    have hindex (t : ℤ) (ht : t = q) (hpt : p + t = p + q) :
        (K.d q (q + 1)).f p ≫ (h.hom (q + 1) t).f p ≫
            (HomologicalComplex₂.flip L).ιTotal (.up ℤ) p t (p + q) hpt =
          (K.d q (q + 1)).f p ≫ (h.hom (q + 1) q).f p ≫
            (HomologicalComplex₂.flip L).ιTotal (.up ℤ) p q (p + q) rfl := by
      subst t
      rfl
    rw [hindex (q + 1 - 1) (by omega)]
    abel


set_option backward.isDefEq.respectTransparency false in
private theorem totalHomotopy_ι
    {A : Type*} [Category* A] [Preadditive A]
    {K L : HomologicalComplex₂ A (.up ℤ) (.up ℤ)}
    [(HomologicalComplex₂.flip K).HasTotal (.up ℤ)]
    [(HomologicalComplex₂.flip L).HasTotal (.up ℤ)] {f g : K ⟶ L}
    (h : Homotopy f g) (p q q' n m : ℤ) (hn : p + q = n) (hm : p + q' = m)
    (hq : q' + 1 = q) :
    (HomologicalComplex₂.flip K).ιTotal (.up ℤ) p q n hn ≫
        (totalHomotopy h).hom n m =
      ((-1 : ℤˣ) ^ p) • (h.hom q q').f p ≫
        (HomologicalComplex₂.flip L).ιTotal (.up ℤ) p q' m hm := by
  obtain rfl : q' = q - 1 := by omega
  change _ ≫ (HomologicalComplex₂.flip K).totalDesc (c₁₂ := .up ℤ)
    (fun a b _ ↦ ((-1 : ℤˣ) ^ a) • (h.hom b (b - 1)).f a ≫
      (HomologicalComplex₂.flip L).ιTotalOrZero (.up ℤ) a (b - 1) m) = _
  rw [HomologicalComplex₂.ι_totalDesc, HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ hm]

attribute [local irreducible] totalHomotopy

private instance modules_enoughInjectives : EnoughInjectives (Modules X R) := by
  have :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{_, _, 0}
      (topology X) R).1
  infer_instance

private theorem coproduct_inclusion_isIso
    {A I : Type*} [Category* A] [HasZeroMorphisms A] (F : I → A) [HasCoproduct F]
    (i : I) (hF : ∀ j, j ≠ i → IsZero (F j)) : IsIso (Sigma.ι F i) := by
  classical
  let r : ∐ F ⟶ F i := Sigma.desc fun j ↦ if h : j = i then eqToHom (congrArg F h) else 0
  refine ⟨r, ?_, ?_⟩
  · simp [r]
  · apply Sigma.hom_ext
    intro j
    by_cases h : j = i
    · subst j
      simp [r]
    · exact (hF j h).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem singleTotal
    {B A : Type*} [Category* B] [Category* A] [Abelian B] [Abelian A]
    [HasCoproducts.{0} A] (S : B ⥤ CochainComplex A ℤ) [S.Additive] (M : B) :
    ∃ e : S.obj M ≅ (HomologicalComplex₂.flip
        ((S.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M))).total (.up ℤ),
      ∀ n : ℤ, e.hom.f n =
        (S.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv).f n ≫
          (HomologicalComplex₂.flip ((S.mapHomologicalComplex (.up ℤ)).obj
            ((HomologicalComplex.single _ (.up ℤ) 0).obj M))).ιTotal
              (.up ℤ) n 0 n (by simp) := by
  let C := (S.mapHomologicalComplex (.up ℤ)).obj
    ((HomologicalComplex.single _ (.up ℤ) 0).obj M)
  let K := HomologicalComplex₂.flip C
  let a := S.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv
  let t : S.obj M ⟶ K.total (.up ℤ) :=
    { f := fun n ↦ a.f n ≫ K.ιTotal (.up ℤ) n 0 n (by simp)
      comm' := by
        intro n m h
        change n + 1 = m at h
        subst m
        rw [Category.assoc, HomologicalComplex₂.total_d, Preadditive.comp_add,
          ← Category.assoc, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
        rw [K.d₁_eq (.up ℤ) (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)
          0 (n + 1) (by simp)]
        rw [K.d₂_eq (.up ℤ) n (show (ComplexShape.up ℤ).Rel 0 1 from rfl)
          (n + 1) (by simp)]
        have he : ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (n, 0) = 1 := rfl
        simp only [he, one_smul]
        have hz : (K.X n).d 0 1 = 0 := by
          change (S.map (((HomologicalComplex.single _ (.up ℤ) 0).obj M).d 0 1)).f n = _
          rw [HomologicalComplex.single_obj_d, S.map_zero, HomologicalComplex.zero_f_apply]
        simp only [hz, zero_comp, smul_zero, add_zero]
        change a.f n ≫ (S.obj _).d n (n + 1) ≫ _ = _
        rw [← a.comm, Category.assoc] }
  have hi (n : ℤ) : IsIso (K.ιTotal (.up ℤ) n 0 n (by simp)) := by
    apply coproduct_inclusion_isIso
    rintro ⟨⟨p, q⟩, hpq⟩ hne
    have hq : q ≠ 0 := by
      intro h
      subst q
      have hp : p = n := by simpa using hpq
      subst p
      exact hne rfl
    exact (HomologicalComplex.eval A (.up ℤ) p).map_isZero
      (S.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq))
  have hα (n : ℤ) : IsIso (a.f n) := by
    change IsIso ((HomologicalComplex.eval A (.up ℤ) n).map
      (S.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv))
    infer_instance
  have ht : IsIso t := by
    apply HomologicalComplex.Hom.isIso_of_components
  exact ⟨asIso t, fun _ ↦ rfl⟩

section GenericDerived

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{w} D]
  (F : C ⥤ D) [F.Additive]
  (h : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

attribute [local irreducible] Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit

private def derivedUnitFor :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h) ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).hom
      (F.rightDerivedFunctorOfQuasiIsoResolutions h)

set_option backward.isDefEq.respectTransparency false in
private theorem derivedUnitFor_isIso (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((derivedUnitFor F h).app I) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  dsimp only [derivedUnitFor, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem computation_unit {E I : CochainComplex C ℤ} [I.IsKInjective]
    (i : E ⟶ I) [QuasiIso i] :
    (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h i).hom ≫
        (derivedUnitFor F h).app I =
      (F.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map i) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app I = 𝟙 _ := rfl
  simp [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso,
    derivedUnitFor, hid, Category.assoc, ← Functor.map_comp]

end GenericDerived

variable [HasDerivedCategory.{v} (Modules X R)]
  [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}]

/-- The actual right derived evaluation with its universal unit, from the recorded API.
Source: Stacks, Tags 070K and 070Y
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def derivedEvaluation : DerivedCategory (Modules X R) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (evaluation X R W).rightDerivedFunctorOfQuasiIsoResolutions (coefficient_resolutions X R)

/-- Canonical computation on any bounded-below termwise-injective resolution.
Source: Stacks, Tags 070J and 070Y
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
This is RF(Qi) followed by the inverse universal unit at I, with the canonical
quotient/localization identifications; it is not an unspecified isomorphism. -/
def resolutionComputation {E I : CochainComplex (Modules X R) ℤ} (N : ℤ)
    [I.IsStrictlyGE N] [∀ n : ℤ, Injective (I.X n)] (i : E ⟶ I) [QuasiIso i] :
    (derivedEvaluation X R W).obj (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj (((evaluation X R W).mapHomologicalComplex (.up ℤ)).obj I) :=
  letI := CochainComplex.isKInjective_of_injective I N
  (evaluation X R W).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
    (coefficient_resolutions X R) i

attribute [local irreducible] Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit

private def derivedUnit :
    (evaluation X R W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedEvaluation X R W :=
  derivedUnitFor (evaluation X R W) (coefficient_resolutions X R)

set_option backward.isDefEq.respectTransparency false in
private theorem derivedUnit_isIso (I : CochainComplex (Modules X R) ℤ) [I.IsKInjective] :
    IsIso ((derivedUnit X R W).app I) := by
  exact derivedUnitFor_isIso (evaluation X R W) (coefficient_resolutions X R) I

set_option backward.isDefEq.respectTransparency false in
private theorem resolutionComputation_unit {E I : CochainComplex (Modules X R) ℤ}
    (N : ℤ) [I.IsStrictlyGE N] [∀ n : ℤ, Injective (I.X n)]
    (i : E ⟶ I) [QuasiIso i] :
    (resolutionComputation X R W N i).hom ≫ (derivedUnit X R W).app I =
      (derivedEvaluation X R W).map (DerivedCategory.Q.map i) := by
  have := CochainComplex.isKInjective_of_injective I N
  exact computation_unit (evaluation X R W) (coefficient_resolutions X R) i

attribute [local irreducible] derivedEvaluation resolutionComputation derivedUnit

omit [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}] in
private theorem resolutionMap_lift {E I J : CochainComplex (Modules X R) ℤ}
    (i : E ⟶ I) [QuasiIso i] [J.IsKInjective] (j : E ⟶ J) :
    ∃ k : I ⟶ J, Nonempty (Homotopy (i ≫ k) j) := by
  let q := HomotopyCategory.quotient (Modules X R) (.up ℤ)
  obtain ⟨k, hk⟩ := (CochainComplex.IsKInjective.precomp_bijective_of_quasiIso i J).2
    (q.map j)
  obtain ⟨k, rfl⟩ := q.map_surjective k
  exact ⟨k, ⟨HomotopyCategory.homotopyOfEq _ _ (by simpa only [Functor.map_comp] using hk)⟩⟩

omit [HasDerivedCategory.{v} (Modules X R)] in
private theorem total_homotopy_eq
    {E F : CochainComplex (Modules X R) ℤ} {f g : E ⟶ F} (s : Homotopy f g) :
    DerivedCategory.Q.map ((total X R W U).map f) =
      DerivedCategory.Q.map ((total X R W U).map g) := by
  exact DerivedCategory.Q_map_eq_of_homotopy _
    ((forget₂ (ModuleCat _) AddCommGrpCat.{u + 1}).mapHomotopy
      (totalHomotopy ((hypercoverSectionRows X R W U).mapHomotopy s)))

attribute [local irreducible] evaluation total augmentation
set_option backward.isDefEq.respectTransparency true

/-- The explicit comparison identities for homotopy-commuting resolution triangles.
Source: Stacks, Tags 070I and 070Y
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: signed_homotopy makes the first equality hold after localization. Ordinary
evaluation preserves the same homotopy; naturality of the universal derived unit
then gives the second equality for the canonical computation maps rho. -/
theorem resolution_comparison
    (E I I' : CochainComplex (Modules X R) ℤ) (NI NI' : ℤ)
    [I.IsStrictlyGE NI] [I'.IsStrictlyGE NI']
    [∀ n : ℤ, Injective (I.X n)] [∀ n : ℤ, Injective (I'.X n)]
    (i : E ⟶ I) (i' : E ⟶ I') [QuasiIso i] [QuasiIso i']
    (k : I ⟶ I') (s : Homotopy (i ≫ k) i') :
    DerivedCategory.Q.map ((total X R W U).map i) ≫
        DerivedCategory.Q.map ((total X R W U).map k) =
      DerivedCategory.Q.map ((total X R W U).map i') ∧
    (resolutionComputation X R W NI i).hom ≫
        DerivedCategory.Q.map (((evaluation X R W).mapHomologicalComplex (.up ℤ)).map k) =
      (resolutionComputation X R W NI' i').hom := by
  constructor
  · simpa only [Functor.map_comp] using total_homotopy_eq X R W U s
  · have := CochainComplex.isKInjective_of_injective I NI
    have := CochainComplex.isKInjective_of_injective I' NI'
    have := derivedUnit_isIso X R W I'
    apply (cancel_mono ((derivedUnit X R W).app I')).mp
    have hn := (derivedUnit X R W).naturality k
    change DerivedCategory.Q.map (((evaluation X R W).mapHomologicalComplex (.up ℤ)).map k)
      ≫ (derivedUnit X R W).app I' = (derivedUnit X R W).app I ≫
        (derivedEvaluation X R W).map (DerivedCategory.Q.map k) at hn
    rw [Category.assoc, hn]
    rw [← Category.assoc, resolutionComputation_unit, resolutionComputation_unit]
    rw [← Functor.map_comp, ← Functor.map_comp, DerivedCategory.Q_map_eq_of_homotopy _ s]

/-- The unique derived comparison normalized by every injective resolution.
Source: Stacks, Tag 09A2, and Derived Categories, Tags 070I, 070J and 070Y
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: choose a bounded-below termwise-injective resolution, which exists by enough
injectives and lem-sc-bounded-below-injective-resolution-existence. Exact column
comparison makes T(i) a quasi-isomorphism; the injective rows make alpha_I one too.
Compose rho_i, Q(alpha_I), and the inverse of Q(T(i)). For any other resolution,
K-injective comparison gives k with ki homotopic to i'. The signed homotopy makes
QT(k)QT(i)=QT(i'), while naturality of the actual derived unit gives
QGamma(k)rho_i=rho_i'. Augmentation naturality and cancellation prove independence
and normalization for every resolution. For uniqueness, cancel the invertible QT(i).
This also proves both resolution quasi-isomorphism assertions in the node. -/
theorem descent (hcover : IsHypercover X W U)
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (E : CochainComplex (Modules X R) ℤ) (NE : ℤ) [E.IsStrictlyGE NE] :
    ∃! A : (derivedEvaluation X R W).obj (DerivedCategory.Q.obj E) ≅
        DerivedCategory.Q.obj ((total X R W U).obj E),
      ∀ (I : CochainComplex (Modules X R) ℤ) (NI : ℤ)
        [I.IsStrictlyGE NI] [∀ n : ℤ, Injective (I.X n)] (i : E ⟶ I) [QuasiIso i],
        QuasiIso ((total X R W U).map i) ∧
          QuasiIso ((augmentation X R W U).app I) ∧
          A.hom ≫ DerivedCategory.Q.map ((total X R W U).map i) =
            (resolutionComputation X R W NI i).hom ≫
              DerivedCategory.Q.map ((augmentation X R W U).app I) := by
  classical
  obtain ⟨I, i, hi, hI, hIN⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective E NE
  have := hi
  have := hIN
  have := hI
  have ha := total_quasiIso X R W U hweak E I NE NE i
  have hb := augmentation_quasiIso X R W U hcover I NE
  let a := asIso (DerivedCategory.Q.map ((total X R W U).map i))
  let b := asIso (DerivedCategory.Q.map ((augmentation X R W U).app I))
  let A := resolutionComputation X R W NE i ≪≫ b ≪≫ a.symm
  have hA : A.hom ≫ a.hom = (resolutionComputation X R W NE i).hom ≫ b.hom := by
    simp only [A, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  refine ⟨A, ?_, ?_⟩
  · intro J NJ _ hJ j _
    have ht := total_quasiIso X R W U hweak E J NE NJ j
    have hα := augmentation_quasiIso X R W U hcover J NJ
    refine ⟨ht, hα, ?_⟩
    have := CochainComplex.isKInjective_of_injective J NJ
    obtain ⟨k, ⟨s⟩⟩ := resolutionMap_lift X R i j
    obtain ⟨htk, hrk⟩ := resolution_comparison X R W U E I J NE NJ i j k s
    have hn := congrArg DerivedCategory.Q.map ((augmentation X R W U).naturality k)
    simp only [Functor.map_comp] at hn
    rw [← htk, ← Category.assoc]
    change (A.hom ≫ a.hom) ≫ _ = _
    rw [hA]
    change ((resolutionComputation X R W NE i).hom ≫
      DerivedCategory.Q.map ((augmentation X R W U).app I)) ≫ _ = _
    rw [Category.assoc, ← hn, ← Category.assoc, hrk]
  · intro A' hA'
    apply Iso.ext
    apply (cancel_mono a.hom).mp
    exact (hA' I NE i).2.2.trans hA.symm


/-- The comparison determined uniquely by its every-resolution normalization.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
The existence theorem determines this isomorphism up to equality, so this choice
postpones only its proof and leaves no undetermined mathematical data. -/
def comparison (hcover : IsHypercover X W U)
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (E : CochainComplex (Modules X R) ℤ) (NE : ℤ) [E.IsStrictlyGE NE] :
    (derivedEvaluation X R W).obj (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj ((total X R W U).obj E) :=
  Classical.choose (descent X R W U hcover hweak E NE).exists

/-- The localized total of a resolution map, with its actual underlying arrow.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def resolutionTotalIso
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (E I : CochainComplex (Modules X R) ℤ) (NE NI : ℤ)
    [E.IsStrictlyGE NE] [I.IsStrictlyGE NI] (i : E ⟶ I) [QuasiIso i] :
    DerivedCategory.Q.obj ((total X R W U).obj E) ≅
      DerivedCategory.Q.obj ((total X R W U).obj I) :=
  letI := total_quasiIso X R W U hweak E I NE NI i
  asIso (DerivedCategory.Q.map ((total X R W U).map i))

/-- The localized actual augmentation at an injective complex.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def injectiveAugmentationIso (hcover : IsHypercover X W U)
    (I : CochainComplex (Modules X R) ℤ) (NI : ℤ)
    [I.IsStrictlyGE NI] [∀ n : ℤ, Injective (I.X n)] :
    DerivedCategory.Q.obj (((evaluation X R W).mapHomologicalComplex (.up ℤ)).obj I) ≅
      DerivedCategory.Q.obj ((total X R W U).obj I) :=
  letI := augmentation_quasiIso X R W U hcover I NI
  asIso (DerivedCategory.Q.map ((augmentation X R W U).app I))

/-- The explicit formula A=(QT(i))⁻¹ Q(alpha_I) rho_i for every resolution i.
Source: Stacks, Tag 09A2, augmentation-normalized injective-resolution computation
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: normalization identifies the composites with the actual invertible QT(i).
Cancel that isomorphism, or compose with its inverse. This proves that the
specified formula gives the same comparison for every choice of resolution. -/
theorem comparison_formula (hcover : IsHypercover X W U)
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (E I : CochainComplex (Modules X R) ℤ) (NE NI : ℤ)
    [E.IsStrictlyGE NE] [I.IsStrictlyGE NI] [∀ n : ℤ, Injective (I.X n)]
    (i : E ⟶ I) [QuasiIso i] :
    comparison X R W U hcover hweak E NE =
      resolutionComputation X R W NI i ≪≫ injectiveAugmentationIso X R W U hcover I NI ≪≫
        (resolutionTotalIso X R W U hweak E I NE NI i).symm := by
  have h := ((Classical.choose_spec (descent X R W U hcover hweak E NE).exists)
    I NI i).2.2
  apply Iso.ext
  have := total_quasiIso X R W U hweak E I NE NI i
  apply (cancel_mono (DerivedCategory.Q.map ((total X R W U).map i))).mp
  dsimp only [Iso.trans_hom, Iso.symm_hom, resolutionTotalIso,
    injectiveAugmentationIso, asIso_hom]
  simp only [Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id]
  exact h

/-- The comparison satisfies its specified normalization for each resolution.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: the defining unique-existence theorem for comparison gives this equation;
it is the equation QT(i) A = Q(alpha_I) rho_i in diagrammatic composition order. -/
theorem comparison_normalization (hcover : IsHypercover X W U)
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (E I : CochainComplex (Modules X R) ℤ) (NE NI : ℤ)
    [E.IsStrictlyGE NE] [I.IsStrictlyGE NI] [∀ n : ℤ, Injective (I.X n)]
    (i : E ⟶ I) [QuasiIso i] :
    (comparison X R W U hcover hweak E NE).hom ≫
        DerivedCategory.Q.map ((total X R W U).map i) =
      (resolutionComputation X R W NI i).hom ≫
        DerivedCategory.Q.map ((augmentation X R W U).app I) := by
  exact ((Classical.choose_spec (descent X R W U hcover hweak E NE).exists)
    I NI i).2.2

attribute [local irreducible] comparison

/-- Coefficient naturality holds for every chain map, without choosing a strictly
commutative comparison of resolutions.
Source: Stacks, Tags 09A2, 070I and 070Y
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: choose resolutions i,j and lift jf across i into the K-injective target.
Thus ki is homotopic to jf. Apply the signed total homotopy, naturality of the
derived unit and augmentation naturality, then cancel QT(j) in the normalization. -/
theorem comparison_naturality (hcover : IsHypercover X W U)
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (E F : CochainComplex (Modules X R) ℤ) (NE NF : ℤ)
    [E.IsStrictlyGE NE] [F.IsStrictlyGE NF] (f : E ⟶ F) :
    (comparison X R W U hcover hweak E NE).hom ≫
        DerivedCategory.Q.map ((total X R W U).map f) =
      (derivedEvaluation X R W).map (DerivedCategory.Q.map f) ≫
        (comparison X R W U hcover hweak F NF).hom := by
  obtain ⟨I, i, hi, hI, hIN⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective E NE
  obtain ⟨J, j, hj, hJ, hJN⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective F NF
  have := hi
  have := hj
  have := hI
  have := hJ
  have := hIN
  have := hJN
  have := CochainComplex.isKInjective_of_injective I NE
  have := CochainComplex.isKInjective_of_injective J NF
  obtain ⟨k, ⟨s⟩⟩ := resolutionMap_lift X R i (f ≫ j)
  have ht := total_homotopy_eq X R W U s
  simp only [Functor.map_comp] at ht
  have hr : (resolutionComputation X R W NE i).hom ≫
        DerivedCategory.Q.map (((evaluation X R W).mapHomologicalComplex (.up ℤ)).map k) =
      (derivedEvaluation X R W).map (DerivedCategory.Q.map f) ≫
        (resolutionComputation X R W NF j).hom := by
    have := derivedUnit_isIso X R W J
    apply (cancel_mono ((derivedUnit X R W).app J)).mp
    have hn := (derivedUnit X R W).naturality k
    change DerivedCategory.Q.map (((evaluation X R W).mapHomologicalComplex (.up ℤ)).map k)
      ≫ (derivedUnit X R W).app J = (derivedUnit X R W).app I ≫
        (derivedEvaluation X R W).map (DerivedCategory.Q.map k) at hn
    rw [Category.assoc, hn, ← Category.assoc,
      resolutionComputation_unit, Category.assoc, resolutionComputation_unit,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.Q_map_eq_of_homotopy _ s]
  have hn := congrArg DerivedCategory.Q.map ((augmentation X R W U).naturality k)
  simp only [Functor.map_comp] at hn
  have := total_quasiIso X R W U hweak F J NF NF j
  apply (cancel_mono (DerivedCategory.Q.map ((total X R W U).map j))).mp
  rw [Category.assoc, ← ht, ← Category.assoc,
    comparison_normalization X R W U hcover hweak E I NE NE i,
    Category.assoc, ← hn, ← Category.assoc, hr, Category.assoc,
    Category.assoc, comparison_normalization X R W U hcover hweak F J NF NF j]


attribute [local semireducible] evaluation total augmentation
set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false in
/-- Signed total homotopy, explicitly characterized on every total summand.
Source: Stacks, Tag 09A2, signed-total convention; agent calculation
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: on bidegree (p,q) use (-1)^p times the section map of s into (p,q-1).
The horizontal mixed terms cancel because restrictions commute with s; the
vertical terms are ds+sd=f-g. Total coproduct injections characterize the maps,
and their finite support makes the formula valid for every lower bound. -/
theorem signed_homotopy (E F : CochainComplex (Modules X R) ℤ)
    (NE NF : ℤ) [E.IsStrictlyGE NE] [F.IsStrictlyGE NF] (f g : E ⟶ F) (s : Homotopy f g) :
    ∃ H : Homotopy ((total X R W U).map f) ((total X R W U).map g),
      ∀ (p q q' n m : ℤ) (hn : p + q = n) (hm : p + q' = m), q' + 1 = q →
        (forget₂ (ModuleCat _) AddCommGrpCat).map
            ((HomologicalComplex₂.flip
              (((hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj E)).ιTotal
                (.up ℤ) p q n hn) ≫ H.hom n m =
          (forget₂ (ModuleCat _) AddCommGrpCat).map
            (((-1 : ℤˣ) ^ p) • (((hypercoverSectionRows X R W U).map (s.hom q q')).f p) ≫
              (HomologicalComplex₂.flip
                (((hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj F)).ιTotal
                  (.up ℤ) p q' m hm) := by
  let S := hypercoverSectionRows X R W U
  let K := (S.mapHomologicalComplex (.up ℤ)).obj E
  let L := (S.mapHomologicalComplex (.up ℤ)).obj F
  let h := totalHomotopy (S.mapHomotopy s)
  let G := forget₂ (ModuleCat.{u + 1}
    (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W)))
        AddCommGrpCat.{u + 1}
  refine ⟨G.mapHomotopy h, ?_⟩
  intro p q q' n m hn hm hq
  have hh : (HomologicalComplex₂.flip K).ιTotal (.up ℤ) p q n hn ≫ h.hom n m =
      ((-1 : ℤˣ) ^ p) • ((S.map (s.hom q q')).f p) ≫
        (HomologicalComplex₂.flip L).ιTotal (.up ℤ) p q' m hm := by
    exact totalHomotopy_ι (S.mapHomotopy s) p q q' n m hn hm hq
  change G.map _ ≫ G.map _ = G.map _
  exact (G.map_comp _ _).symm.trans (congrArg G.map hh)


omit [HasDerivedCategory.{v} (Modules X R)]
  [HasDerivedCategory.{w} AddCommGrpCat.{u + 1}] in
private theorem liftRow_laws
    {B A D : Type*} [Category* B] [Category* A] [Category* D]
    [HasZeroMorphisms B] [HasZeroMorphisms A]
    {S S' S'' : B ⥤ CochainComplex A ℤ}
    [S.PreservesZeroMorphisms] [S'.PreservesZeroMorphisms] [S''.PreservesZeroMorphisms]
    (r₀ : S ⟶ S) (r : S ⟶ S') (s : S' ⟶ S'') (t : S ⟶ S'')
    (h₀ : r₀ = 𝟙 S) (ht : t = r ≫ s)
    (T : HomologicalComplex (CochainComplex A ℤ) (.up ℤ) ⥤ D) :
    Functor.whiskerRight (NatTrans.mapHomologicalComplex r₀ (.up ℤ)) T =
        𝟙 (S.mapHomologicalComplex (.up ℤ) ⋙ T) ∧
      Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) T =
        Functor.whiskerRight (NatTrans.mapHomologicalComplex r (.up ℤ)) T ≫
          Functor.whiskerRight (NatTrans.mapHomologicalComplex s (.up ℤ)) T := by
  subst r₀ t
  constructor
  · rw [NatTrans.mapHomologicalComplex_id]
    exact Functor.whiskerRight_id' T
  · rw [NatTrans.mapHomologicalComplex_comp, Functor.whiskerRight_comp]

set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true

/-- Restriction of section rows as a functor of the opposite simplicial object.
Source: Stacks Project, Tag 09A2; functoriality of presheaf restriction
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def rowRestrictionFunctor : (SimplicialObject (Over W))ᵒᵖ ⥤
    Modules X R ⥤ CochainComplex (ModuleCat.{u + 1}
      (((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W))) ℤ :=
  let S := SheafOfModules.forget.{u + 1}
      ((sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
    PresheafOfModules.pushforward₀ (Over.forget W) _ ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 W)))
      Over.mkIdTerminal.op
  let C := AlgebraicTopology.alternatingCofaceMapComplex
    (ModuleCat.{u + 1} (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor _
  (Functor.leftOpRightOpEquiv SimplexCategory (Over W)).functor ⋙
    Functor.whiskeringLeft SimplexCategory (Over W)ᵒᵖ _ ⋙
    (Functor.whiskeringLeft (Modules X R) _ _).obj S ⋙
    (Functor.whiskeringRight (Modules X R) _ _).obj C

/-- Restriction on section rows along a simplicial refinement, using the actual
presheaf restriction maps, alternating cofaces, and extension by zero.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def rowRefinement (V : SimplicialObject (Over W)) (r : V ⟶ U) (M : Modules X R) :
    (hypercoverSectionRows X R W U).obj M ⟶ (hypercoverSectionRows X R W V).obj M :=
  (ComplexShape.embeddingUpNat.extendFunctor _).map
    ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      (Functor.whiskerRight r.rightOp
        ((PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 W)))
          Over.mkIdTerminal.op).obj
            ((PresheafOfModules.pushforward₀ (Over.forget W) _).obj M.val))))

set_option linter.unusedSectionVars false in
/-- Refinement restrictions commute with every coefficient morphism.
Source: Stacks, Tag 09A2, restriction functoriality
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: sheaf morphism naturality says that restriction along r_p commutes with
every coefficient component. Alternating cofaces and extension by zero preserve
that equation in each degree. -/
theorem rowRefinement_naturality (V : SimplicialObject (Over W)) (r : V ⟶ U)
    (M N : Modules X R) (f : M ⟶ N) :
    (hypercoverSectionRows X R W U).map f ≫ rowRefinement X R W U V r N =
      rowRefinement X R W U V r M ≫ (hypercoverSectionRows X R W V).map f := by
  exact ((rowRestrictionFunctor X R W).map r.op).naturality f

/-- Row restriction as a natural transformation of coefficient functors.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def rowRefinementNat (V : SimplicialObject (Over W)) (r : V ⟶ U) :
    hypercoverSectionRows X R W U ⟶ hypercoverSectionRows X R W V :=
  (rowRestrictionFunctor X R W).map r.op

/-- Total refinement restriction, formed termwise from row restriction before
the same flip, signed coproduct total, and forgetting of scalars as in T_U.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent). -/
def refinement (V : SimplicialObject (Over W)) (r : V ⟶ U) :
    total X R W U ⟶ total X R W V :=
  Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (rowRefinementNat X R W U V r) (.up ℤ))
    (HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor _ _ _ (.up ℤ) ⋙
        (forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ))

set_option linter.unusedSectionVars false in
/-- Refinements preserve the restriction augmentation and coefficient-resolution square.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: both augmentation composites restrict along U_0 to V_0 over W, hence agree.
In the second identity coefficient maps commute with restriction on every (p,q)
summand. The total injections jointly detect these equalities of chain maps. -/
theorem refinement_squares (V : SimplicialObject (Over W)) (r : V ⟶ U)
    (E I : CochainComplex (Modules X R) ℤ) (i : E ⟶ I) :
    (augmentation X R W U).app I ≫ (refinement X R W U V r).app I =
        (augmentation X R W V).app I ∧
      (total X R W U).map i ≫ (refinement X R W U V r).app I =
        (refinement X R W U V r).app E ≫ (total X R W V).map i := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    refine ⟨?_, (refinement X R W U V r).naturality i⟩
    have hrow (M : Modules X R) :
        hypercoverRowAugmentation X R W U M ≫ (rowRefinement X R W U V r M).f 0 =
          hypercoverRowAugmentation X R W V M := by
      dsimp only [hypercoverRowAugmentation, rowRefinement]
      erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc]
      congr 1
      ext x
      simp only [ModuleCat.comp_apply, hypercoverRestrictionZero_apply]
      change M.val.map (r.app (op ⦋0⦌)).left.op (M.val.map (U _⦋0⦌).hom.op x) = _
      rw [← PresheafOfModules.map_comp_apply]
      change M.val.map ((U _⦋0⦌).hom.op ≫ (r.app (op ⦋0⦌)).left.op) x =
        (hypercoverRestrictionZero X R W V M).hom x
      rw [hypercoverRestrictionZero_apply]
      simpa only [op_comp] using
        M.val.congr_map_apply (congrArg Quiver.Hom.op (r.app (op ⦋0⦌)).w) x
    apply HomologicalComplex.hom_ext
    intro n
    change (forget₂ (ModuleCat _) AddCommGrpCat).map
        (((hypercoverAugmentation X R W U).app I).f n) ≫
      (forget₂ (ModuleCat _) AddCommGrpCat).map
        ((HomologicalComplex₂.total.map
          ((HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (rowRefinementNat X R W U V r) (.up ℤ)).app I))
          (.up ℤ)).f n) =
        (forget₂ (ModuleCat _) AddCommGrpCat).map
          (((hypercoverAugmentation X R W V).app I).f n)
    rw [← Functor.map_comp]
    congr 1
    change (hypercoverRowAugmentation X R W U (I.X n) ≫ _) ≫ _ =
      hypercoverRowAugmentation X R W V (I.X n) ≫ _
    rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ _) (hrow (I.X n))

attribute [local irreducible] evaluation total augmentation refinement
set_option backward.isDefEq.respectTransparency true

/-- The normalized derived comparison commutes with every refinement.
Source: Stacks, Tag 09A2, augmentation normalization and restriction functoriality
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: apply the two refinement squares to an injective resolution of E. Compose
with A_U and use normalization for U and V. Cancel QT_V(i), which is invertible
by weak contractibility and bounded-below column comparison. -/
theorem comparison_refinement (hcover : IsHypercover X W U)
    (hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (U _⦋p⦌).left)
    (V : SimplicialObject (Over W)) (hcoverV : IsHypercover X W V)
    (hweakV : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u + 1} (V _⦋p⦌).left)
    (r : V ⟶ U) (E : CochainComplex (Modules X R) ℤ) (NE : ℤ) [E.IsStrictlyGE NE] :
    (comparison X R W U hcover hweak E NE).hom ≫
        DerivedCategory.Q.map ((refinement X R W U V r).app E) =
      (comparison X R W V hcoverV hweakV E NE).hom := by
  obtain ⟨I, i, hi, hI, hIN⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective E NE
  have := hi
  have := hI
  have := hIN
  have := total_quasiIso X R W V hweakV E I NE NE i
  apply (cancel_mono (DerivedCategory.Q.map ((total X R W V).map i))).mp
  obtain ⟨hα, ht⟩ := refinement_squares X R W U V r E I i
  have ht' := congrArg DerivedCategory.Q.map ht
  have hα' := congrArg DerivedCategory.Q.map hα
  simp only [Functor.map_comp] at ht' hα'
  rw [Category.assoc, ← ht', ← Category.assoc,
    comparison_normalization X R W U hcover hweak E I NE NE i,
    Category.assoc, hα', comparison_normalization X R W V hcoverV hweakV E I NE NE i]


attribute [local semireducible] evaluation total augmentation refinement
set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false in
/-- Refinement restrictions commute with coefficient chain maps, identity refinements,
and composite refinements, already before localization.
Source: Stacks, Tag 09A2, sheaf restriction functoriality
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: on (p,q) summands use naturality, restriction along the identity, and
restriction along the composite r_p s_p respectively. Alternating cofaces,
extension by zero and totalization preserve each identity. -/
theorem refinement_functoriality (V Z : SimplicialObject (Over W))
    (r : V ⟶ U) (s : Z ⟶ V) (E F : CochainComplex (Modules X R) ℤ) (f : E ⟶ F) :
    (total X R W U).map f ≫ (refinement X R W U V r).app F =
        (refinement X R W U V r).app E ≫ (total X R W V).map f ∧
      refinement X R W U U (𝟙 U) = 𝟙 (total X R W U) ∧
      refinement X R W U Z (s ≫ r) =
        refinement X R W U V r ≫ refinement X R W V Z s := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    let A := (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W))
    let T := HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor _ _ _ (.up ℤ) ⋙
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)
    let F := rowRestrictionFunctor X R W
    have hi : rowRefinementNat X R W U U (𝟙 U) = 𝟙 _ := F.map_id _
    have hc : rowRefinementNat X R W U Z (s ≫ r) =
        rowRefinementNat X R W U V r ≫ rowRefinementNat X R W V Z s := F.map_comp _ _
    exact ⟨(refinement X R W U V r).naturality f,
      liftRow_laws _ _ _ _ hi hc T⟩

set_option linter.unusedSectionVars false in
/-- For a sheaf in degree zero the total is the alternating section complex,
with its identification characterized by the (p,0) total injections.
Source: Stacks, Tag 09A2, displayed section complex
(blueprint: lem-sfb-hypercover-normalized-single-site-descent).
Proof: only coefficient degree zero survives. The single-object identification
and the total coproduct injection therefore give an isomorphism in each degree.
Its differential is the alternating sum of face restrictions; negative degrees
vanish. The resulting chain isomorphism also gives the asserted derived identification. -/
theorem single_sheaf (M : Modules X R) :
    ∃ e : ((forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
        ((hypercoverSectionRows X R W U).obj M) ≅
      (total X R W U).obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M),
      ∀ n : ℤ, e.hom.f n =
        (forget₂ (ModuleCat _) AddCommGrpCat).map
          ((((hypercoverSectionRows X R W U).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv).f n) ≫
              (HomologicalComplex₂.flip
                (((hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj
                  ((HomologicalComplex.single _ (.up ℤ) 0).obj M))).ιTotal
                    (.up ℤ) n 0 n (by simp)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
    obtain ⟨e, he⟩ := singleTotal (hypercoverSectionRows X R W U) M
    refine ⟨((forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).mapIso e,
      ?_⟩
    intro n
    exact congrArg (forget₂ (ModuleCat _) AddCommGrpCat).map (he n)

end AlgebraicGeometry.Scheme.ProEt.NormalizedDescent
