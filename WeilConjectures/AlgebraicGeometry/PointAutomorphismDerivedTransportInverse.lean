/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.InverseImagePullbackComparisonDerived
public import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExact
public import WeilConjectures.AlgebraicGeometry.PointAutomorphismRestrictionNatural
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
public import WeilConjectures.SixFunctors.FrobeniusPointTransport
import WeilConjectures.AlgebraicGeometry.WContractibleAffineEvaluation
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.IsomorphismComparisonNatural
import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus

/-! # Inverse of the specified point-automorphism transport

Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.11), (1.1.14), pp. 150--153;
the unbounded finite/completed coefficient verification is the agent-written proof
of the DAG node (blueprint: lem-weil-point-automorphism-derived-transport-inverse).

The inverse-image colimit insertion is written in its recorded canonical evaluation
coordinates. Positive finite exponents are indexed by `some n` meaning `n + 1`;
`none` means the completed integral coefficient sheaf, not the discrete constant sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit

private theorem derivedSectionsComparison
    {C B : Type*} [Category C] [Category B] [Abelian C] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory B]
    (F : C ⥤ B) (G : C ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G ⋙ F)
    (N : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso G F).hom.app
        (DerivedCategory.Q.obj N) ≫
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app N) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj N) =
      F.mapDerivedCategoryFactors.hom.app N ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app N) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac G F N
  have hn := Functor.mapDerivedCategoryNatIso_fac e N
  have hid : ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F))
      (.up ℤ)).hom.app N) = 𝟙 _ := by
    ext i
    rfl
  erw [hid, DerivedCategory.Q.map_id, Category.comp_id] at hc
  have hh := (congrArg (fun f ↦ (Functor.mapDerivedCategoryNatIso e).hom.app
    (DerivedCategory.Q.obj N) ≫ f) hc).trans hn
  simpa only [Iso.trans_hom, NatTrans.comp_app, Category.assoc] using hh

section ExactSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type t) [Field k] [IsAlgClosed k] (a : Option ℕ)

private theorem point_inverse_evaluation_surjective (k : Type t) [Field k] [IsAlgClosed k]
    (F G : Sheaf (ProEt.topology (Spec (.of k))) (Type (max u (t + 1))))
    (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 (Spec (.of k)))))) := by
  classical
  have : WLocalSpace (PrimeSpectrum k) :=
    { eq_of_specializes := fun _ _ _ _ ↦ Subsingleton.elim _ _
      isClosed_closedPoints := by
        have : closedPoints (PrimeSpectrum k) = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact mem_closedPoints_iff.mpr isClosed_singleton
        rw [this]
        exact isClosed_univ }
  have : IsWLocalRing k := ⟨inferInstance⟩
  have : IsAlgClosed (IsLocalRing.ResidueField k) :=
    IsAlgClosed.of_ringEquiv k _
      (RingEquiv.ofBijective (IsLocalRing.residue k)
        ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩)
  have : IsStrictlyHenselianLocalRing k := ⟨inferInstance⟩
  have hstrict (m : Ideal k) [m.IsMaximal] :
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
    apply IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.atUnits k m.primeCompl (S := Localization.AtPrime m) ?_).toRingEquiv
    intro x hx
    exact isUnit_iff_ne_zero.mpr (fun he ↦ hx (he ▸ m.zero_mem))
  exact ProEt.surjective_app_of_affine_ring_retractions (Spec (.of k)) k (𝟙 _)
    (fun B _ φ hf hw ↦
      RingHom.exists_retraction_of_wlocal_geometric_criterion hstrict φ hf hw) F G f


/-- The recorded scalar sections functor is exact, including coefficients in a universe
independent of the small site's universe.
Source: Stacks 03CW and 04VG
(blueprint: lem-weil-point-automorphism-derived-transport-inverse).

Proof: Spec k is weakly contractible: k is strictly henselian and every faithfully
flat weakly etale affine cover admits a ring retraction. Thus evaluation at its
final object carries sheaf epimorphisms to surjections, for coefficients of every
universe containing the site. Kernels are sectionwise, so evaluation preserves
kernels and cokernels. Restriction along the actual constant-scalar ring homomorphism
preserves both; its underlying additive functor is unchanged. Their composite is
exact and additive. Therefore termwise sections preserve quasi-isomorphisms on
unbounded complexes and yield the recorded exact derived sections functor. -/
theorem pointRestrictionSections_exact :
    PreservesFiniteLimits (pointRestrictionSections l E k a) ∧
      PreservesFiniteColimits (pointRestrictionSections l E k a) := by
  let R := pointRestrictionRing l E (Spec (.of k)) a
  let ev := SheafOfModules.evaluation.{max u (t + 1)} R
    (op (ProEt.mk (𝟙 (Spec (.of k)))))
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf R).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)} g).mpr inferInstance
    let g' := (sheafCompose (ProEt.topology (Spec (.of k)))
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).map g
    have : Epi g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr
      (point_inverse_evaluation_surjective k _ _ g')
  have : ev.Additive := ⟨by intros; rfl⟩
  have : ev.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels ev
  have : PreservesFiniteLimits ev := Functor.preservesFiniteLimits_of_preservesHomology ev
  have : PreservesFiniteColimits ev := Functor.preservesFiniteColimits_of_preservesHomology ev
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let T : ModuleCat.{max u (t + 1)} (R.obj.obj U) ⥤
      ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E a) :=
    ModuleCat.restrictScalars (pointRestrictionScalarAt l E (Spec (.of k)) a U.unop)
  let V := forget₂
    (ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E a))
    AddCommGrpCat.{max u (t + 1)}
  have : PreservesFiniteLimits (T ⋙ V) :=
    inferInstanceAs (PreservesFiniteLimits
      (forget₂ (ModuleCat.{max u (t + 1)} (R.obj.obj U)) AddCommGrpCat.{max u (t + 1)}))
  have : PreservesFiniteColimits (T ⋙ V) := by
    change PreservesFiniteColimits
      (forget₂ (ModuleCat.{max u (t + 1)} (R.obj.obj U)) AddCommGrpCat.{max u (t + 1)})
    infer_instance
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_reflects_of_preserves T V
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_reflects_of_preserves T V
  exact ⟨comp_preservesFiniteLimits ev T, comp_preservesFiniteColimits ev T⟩

/-- Exact point sections preserve kernels. Source: Stacks 03CW
(blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
instance pointRestrictionSections_preservesFiniteLimits :
    PreservesFiniteLimits (pointRestrictionSections l E k a) :=
  (pointRestrictionSections_exact l E k a).1

/-- Exact point sections preserve cokernels. Source: Stacks 03CW
(blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
instance pointRestrictionSections_preservesFiniteColimits :
    PreservesFiniteColimits (pointRestrictionSections l E k a) :=
  (pointRestrictionSections_exact l E k a).2


end ExactSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{t}) (hl : l ≠ D.p)

/-- The recorded exact derived sections functor, obtained by the canonical localization
of termwise sections. Source: Stacks 05RU and the exact-sections clause of the node
(blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
def pointInverseSections (_hl : l ≠ D.p) (a : Option ℕ) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (pointRestrictionSections l E D.k a).mapDerivedCategory

/-- The localization comparison of the recorded sections functor.
Source: Stacks 05RU (blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
def pointInverseSectionsFactors (hl : l ≠ D.p) (a : Option ℕ) :
    DerivedCategory.Q ⋙ pointInverseSections l E D hl a ≅
      (pointRestrictionSections l E D.k a).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (pointRestrictionSections l E D.k a).mapDerivedCategoryFactors

attribute [local irreducible] pointInverseSections pointInverseSectionsFactors

variable (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]

/-- The specified restriction, insertion and sheafification transformation, reused
from the restriction-naturality node. Its values on every section determine it uniquely.
Source: Deligne (1.1.7) and Stacks 00WX
(blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
def pointInverseRestriction (a : Option ℕ) :=
  (point_automorphism_restriction_natural l E D hl g a).2.2.choose

attribute [local irreducible] pointInverseRestriction

/-- The recorded evaluation identification E in the canonical sectionwise model.
Source: Stacks 09A5 and 00WX, and the site-isomorphism evaluation lemma
(blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
def pointInverseEvaluation (a : Option ℕ)
    (M : SheafOfModules.{max u (t + 1)} (pointRestrictionRing l E (Spec (.of D.k)) a)) :
    (((pointRestrictionInverseImage l E g a).obj M).val.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) ≃+
        M.val.obj (op ((proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 (Spec (.of D.k)))))) :=
  AddEquiv.refl _

/-- The actual colimit coprojection followed by sheafification, in the canonical
coordinates of the recorded inverse image. The restriction-naturality lemma
identifies that distinguished coprojection with identity in precisely these coordinates.
Source: Stacks 00VE and 00WX
(blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
def pointInverseInsertion (a : Option ℕ)
    (M : SheafOfModules.{max u (t + 1)} (pointRestrictionRing l E (Spec (.of D.k)) a)) :
    M.val.obj (op ((proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 (Spec (.of D.k)))))) ≃+
      (((pointRestrictionInverseImage l E g a).obj M).val.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :=
  AddEquiv.refl _

/-- The inverse site arrow U to V. This is the scheme inverse of g in the slice.
Source: Stacks 09A5 (blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
def pointInverseRestrictionArrow :
    ProEt.mk (𝟙 (Spec (.of D.k))) ⟶
      (proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 (Spec (.of D.k)))) :=
  MorphismProperty.Over.homMk (inv g) (by
    change inv g ≫ (𝟙 _ ≫ g) = 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp, IsIso.inv_hom_id]) trivial

/-- The actual insertion and evaluation are mutual inverses in the canonical
sectionwise model; restriction has inverse restriction along g inverse. This yields
one natural isomorphism on the entire unbounded derived category.

Source: Deligne (1.1.7), (1.1.10)--(1.1.11), (1.1.14), pp. 150--153 (context);
DAG proof steps 1, 2 and 5
(blueprint: lem-weil-point-automorphism-derived-transport-inverse).

Proof: the site-isomorphism evaluation identifies the distinguished colimit
coprojection followed by sheafification with identity, so E ins = ins E = 1.
The slice arrows g and its inverse compose to identity. Contravariant restriction
therefore gives both inverse identities. Linearity of the inverse follows by
cancelling the transported-linear forward map. Restriction and evaluation commute
with sheaf maps and differentials. Exact point sections preserve quasi-isomorphisms
on unbounded complexes. Localize the two inverse chain maps; fullness of the
localization on natural transformations gives uniqueness and naturality for every
derived morphism. No completeness or finiteness condition is needed. -/
theorem point_automorphism_sections_inverse (a : Option ℕ) :
    ∃ σ : pointRestrictionSections l E D.k a ≅
        pointRestrictionInverseImage l E g a ⋙ pointRestrictionSections l E D.k a,
    (∀ M : SheafOfModules.{max u (t + 1)}
        (pointRestrictionRing l E (Spec (.of D.k)) a),
      (pointInverseInsertion l E D g a M).symm = pointInverseEvaluation l E D g a M) ∧
    (∀ (M : SheafOfModules.{max u (t + 1)}
        (pointRestrictionRing l E (Spec (.of D.k)) a))
      (b : pointRestrictionScalars.{t, u} l E a)
      (x : ((pointRestrictionInverseImage l E g a).obj M).val.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
      pointInverseEvaluation l E D g a M
          (pointRestrictionScalarAt l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b • x) =
        (inv (pointRestrictionCoefficientMap l E g a)).hom.app
            (op (ProEt.mk (𝟙 (Spec (.of D.k)))))
            (pointRestrictionScalarAt l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b) •
          pointInverseEvaluation l E D g a M x) ∧
    σ.hom = pointInverseRestriction l E D hl g a ∧
    (∀ (M : SheafOfModules.{max u (t + 1)}
        (pointRestrictionRing l E (Spec (.of D.k)) a))
      (x : ((pointRestrictionInverseImage l E g a).obj M).val.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
      σ.inv.app M x =
        M.val.map (pointInverseRestrictionArrow D g).op x) ∧
    ∃! sigma : pointInverseSections l E D hl a ≅
        (pointRestrictionInverseImage l E g a).mapDerivedCategory ⋙
          pointInverseSections l E D hl a,
      ∀ N : CochainComplex (SheafOfModules.{max u (t + 1)}
          (pointRestrictionRing l E (Spec (.of D.k)) a)) ℤ,
        sigma.hom.app (DerivedCategory.Q.obj N) ≫
            (pointInverseSections l E D hl a).map
              ((pointRestrictionInverseImage l E g a).mapDerivedCategoryFactors.hom.app N) ≫
            (pointInverseSectionsFactors l E D hl a).hom.app
              (((pointRestrictionInverseImage l E g a).mapHomologicalComplex (.up ℤ)).obj N) =
          (pointInverseSectionsFactors l E D hl a).hom.app N ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (pointInverseRestriction l E D hl g a)
                (.up ℤ)).app N) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  unfold pointInverseSections pointInverseSectionsFactors
  let F := pointRestrictionSections l E D.k a
  let G := pointRestrictionInverseImage l E g a
  let σ := pointInverseRestriction l E D hl g a
  have hσ (M) (x) : σ.app M x = pointRestrictionRaw l E g a M x :=
    by
      dsimp only [σ]
      unfold pointInverseRestriction
      exact (point_automorphism_restriction_natural l E D hl g a).2.2.choose_spec.1 M x
  have h₁ : pointRestrictionArrow g ≫ pointInverseRestrictionArrow D g = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    exact IsIso.hom_inv_id g
  have h₂ : pointInverseRestrictionArrow D g ≫ pointRestrictionArrow g = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    exact IsIso.inv_hom_id g
  let : IsIso (pointRestrictionArrow g) := ⟨⟨pointInverseRestrictionArrow D g, h₁, h₂⟩⟩
  have hbij (M) : Function.Bijective (σ.app M) := by
    have he : (fun x ↦ σ.app M x) =
        (fun x ↦ (M.val.presheaf.map (pointRestrictionArrow g).op) x) :=
      funext (hσ M)
    change Function.Bijective (fun x ↦ σ.app M x)
    rw [he]
    exact ConcreteCategory.bijective_of_isIso _
  let : ∀ M, IsIso (σ.app M) := fun M ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij M)
  let : IsIso σ := NatIso.isIso_of_isIso_app σ
  let σi := asIso σ
  have hinv (M) (x) : σi.inv.app M x =
      M.val.map (pointInverseRestrictionArrow D g).op x := by
    apply (hbij M).1
    have hi := ConcreteCategory.congr_hom (σi.inv_hom_id_app M) x
    change σ.app M (σi.inv.app M x) = x at hi
    rw [hi, hσ]
    change x = (M.val.presheaf.map (pointRestrictionArrow g).op)
      ((M.val.presheaf.map (pointInverseRestrictionArrow D g).op) x)
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, h₁,
      op_id, M.val.presheaf.map_id]
    rfl
  let d := Functor.mapDerivedCategoryNatIso σi ≪≫ Functor.mapDerivedCategoryCompIso G F
  have hd (N) : d.hom.app (DerivedCategory.Q.obj N) ≫
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app N) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj N) =
      F.mapDerivedCategoryFactors.hom.app N ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app N) := by
    exact derivedSectionsComparison F G σi N
  refine ⟨σi, fun _ ↦ rfl, ?_, rfl, hinv, d, hd, ?_⟩
  · intro M b x
    rfl
  · intro d' hd'
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    intro N
    apply (cancel_mono (F.mapDerivedCategory.map
      (G.mapDerivedCategoryFactors.hom.app N) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj N))).1
    exact (hd' N).trans (hd N).symm


/-- Sigma and rho on derived sections, uniquely normalized on all representatives.
The hom is sigma; the inv is res(g inverse) after evaluation, by the preceding theorem.
Source: DAG proof steps 1, 2 and 5
(blueprint: lem-weil-point-automorphism-derived-transport-inverse). -/
def pointInverseSigmaIso (a : Option ℕ) :
    pointInverseSections l E D hl a ≅
      (pointRestrictionInverseImage l E g a).mapDerivedCategory ⋙
        pointInverseSections l E D hl a :=
  (point_automorphism_sections_inverse l E D hl g a).choose_spec.2.2.2.2.choose

attribute [local irreducible] pointInverseSigmaIso

/-- Finite pullback has the explicit inverse on every unbounded complex. The last
natural isomorphism gives the inverse of t = Gamma(kappa) sigma in D(A_n).

Source: Deligne (1.1.7), (1.1.10)--(1.1.11), (1.1.14), pp. 150--153 (context);
DAG proof steps 3, 5 and 6
(blueprint: lem-weil-point-automorphism-derived-transport-inverse).

Proof: use the scalar-extension isomorphism for c_A and each inverse-image term.
Its multiplication map sends x tensor b to c_A inverse(b) x, and its inverse is
x tensor 1, exactly the specified kappa. The formulas commute with differentials
and chain maps. Exactness lets both functors and both inverse maps descend through
quasi-isomorphisms to the entire derived category, without a Tor or boundedness
condition. Compose the descended comparison with sigma. Its inverse is sections
of delta followed by rho; functoriality and the two inverse identities cancel
both composites. The natural isomorphisms express naturality in all derived maps. -/
theorem point_automorphism_finite_transport_inverse (n : ℕ) :
    ∃ δ : ∀ K : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ,
      ((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).obj K ⟶
        ((inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ)).obj K,
    (∀ K, inverseImageFiniteComparisonComplex l E g n K ≫ δ K = 𝟙 _ ∧
      δ K ≫ inverseImageFiniteComparisonComplex l E g n K = 𝟙 _) ∧
    (∀ (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
      (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (b : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U)),
      ((δ K).f i).val.app (op U)
          (b • (((integralOperationsLevelPullback l E g n).obj (K.X i)).val.map
            (proEtaleIsoCommaArrow g U).op
            (integralOperationsPullbackGenerator l E g n (K.X i)
              ((proEtaleIsoPostcompose g).obj U) x))) =
        (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) b • x) ∧
    (∀ (K L : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) (f : K ⟶ L),
      ((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).map f ≫
          δ L = δ K ≫
        ((inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ)).map f) ∧
    ∃ κ : inverseImageFiniteDerived l E g n ⟶
        (integralOperationsLevelPullback l E g n).mapDerivedCategory,
    (∀ K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ,
      κ.app (DerivedCategory.Q.obj K) =
        inverseImagePullbackComparisonFinite l E g (frobeniusPointPrimeUnit D l hl)
          (frobeniusPointPrimeUnit D l hl) n K) ∧
    ∃ Δ : (integralOperationsLevelPullback l E g n).mapDerivedCategory ≅
        inverseImageFiniteDerived l E g n,
    Δ.inv = κ ∧
    (∀ K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ,
      Δ.hom.app (DerivedCategory.Q.obj K) =
        (integralOperationsLevelPullback l E g n).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map (δ K) ≫
            (inverseImageFiniteModules l E g n).mapDerivedCategoryFactors.inv.app K) ∧
    ∃ T : pointInverseSections l E D hl (some n) ≅
        (integralOperationsLevelPullback l E g n).mapDerivedCategory ⋙
          pointInverseSections l E D hl (some n),
      ∀ N : DerivedCategory (integralOperationsFiniteModules l E (Spec (.of D.k)) n),
        T.hom.app N = (pointInverseSigmaIso l E D hl g (some n)).hom.app N ≫
            (pointInverseSections l E D hl (some n)).map (κ.app N) ∧
        T.inv.app N = (pointInverseSections l E D hl (some n)).map (Δ.hom.app N) ≫
            (pointInverseSigmaIso l E D hl g (some n)).inv.app N := by
  let G := (inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ)
  let P := (integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)
  have hv (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :=
    (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose_spec
  let τ : G ⟶ P :=
    { app := inverseImageFiniteComparisonComplex l E g n
      naturality := by
        intro K L f
        ext i U x
        change ((inverseImageFiniteComparisonComplex l E g n L).f i).val.app U
            ((f.f i).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x) =
          (((integralOperationsLevelPullback l E g n).map (f.f i)).val.app U)
            (((inverseImageFiniteComparisonComplex l E g n K).f i).val.app U x)
        dsimp only [inverseImageFiniteComparisonComplex]
        erw [hv L i U.unop, hv K i U.unop]
        let A := AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction g
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        have hu := congrArg (fun z ↦ z.val.app
          (op ((proEtaleIsoPostcompose g).obj U.unop)) x) (A.unit.naturality (f.f i))
        have hr := congrArg (fun z ↦ z
          (integralOperationsPullbackGenerator l E g n (K.X i)
            ((proEtaleIsoPostcompose g).obj U.unop) x))
          (((integralOperationsLevelPullback l E g n).map (f.f i)).val.naturality
            (proEtaleIsoCommaArrow g U.unop).op)
        exact (congrArg
          (((integralOperationsLevelPullback l E g n).obj (L.X i)).val.map
            (proEtaleIsoCommaArrow g U.unop).op) hu).trans hr.symm }
  let : ∀ K, IsIso (τ.app K) := fun K ↦
    inverseImageFiniteComparisonComplex_isIso l E g n K
  let : IsIso τ := NatIso.isIso_of_isIso_app τ
  let e := asIso τ
  let δ := fun K ↦ e.inv.app K
  let Δ := (Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (G ⋙ DerivedCategory.Q) (P ⋙ DerivedCategory.Q)
    (inverseImageFiniteDerived l E g n)
    (integralOperationsLevelPullback l E g n).mapDerivedCategory
    (Functor.isoWhiskerRight e DerivedCategory.Q)).symm
  let κ := Δ.inv
  let F := pointInverseSections l E D hl (some n)
  let σ := pointInverseSigmaIso l E D hl g (some n)
  let T := σ ≪≫ Functor.isoWhiskerRight Δ.symm F
  refine ⟨δ, ?_, ?_, ?_, κ, ?_, Δ, rfl, ?_, T, ?_⟩
  · intro K
    exact ⟨e.hom_inv_id_app K, e.inv_hom_id_app K⟩
  · intro K i U x b
    have hv := (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose_spec
    have hi : ((δ K).f i).val.app (op U)
        (((inverseImageFiniteComparisonComplex l E g n K).f i).val.app (op U) x) = x := by
      have h := congrArg (fun f ↦ (f.f i).val.app (op U) x) (e.hom_inv_id_app K)
      exact h
    rw [← hv i U x]
    change ((δ K).f i).val.app (op U) (b • _) = _
    rw [map_smul]
    dsimp only [inverseImageFiniteComparisonComplex] at hi
    erw [hi]
    rfl
  · intro K L f
    exact e.inv.naturality f
  · intro K
    exact Localization.liftNatTrans_app ..
  · intro K
    exact Localization.liftNatTrans_app ..
  · intro N
    exact ⟨rfl, rfl⟩


/-- Integral transport has the specified whole-object inverse on every derived-complete
object, and both transport and inverse are natural for all derived morphisms between
such objects. The unit and theta are those of the strict coefficient-system calculus.

Source: Deligne (1.1.7), (1.1.10)--(1.1.11), (1.1.14), pp. 150--153 (context);
DAG proof steps 4, 5 and 6
(blueprint: lem-weil-point-automorphism-derived-transport-inverse).

Proof: apply the recorded comparison-normalization theorem at X = Y = Spec k.
It provides theta on entire ambient objects with kappa followed by theta equal
to G of the actual completion unit, not merely equality on reduction projections.
On a derived-complete object that unit is invertible. Set delta to theta followed
by its inverse. Cancelling theta and the unit gives both inverse identities and
uniquely fixes delta. Naturality follows from their naturality and inverse
cancellation. Compose sections of kappa with sigma; compose sections of delta
with rho for the inverse. Functoriality gives both inverse identities in D(R).
The naturality squares for these composites follow from those of sigma, kappa
and delta. Completeness is used only in inverting the unit; no boundedness,
constructibility, finite Tor amplitude or Weil structure occurs. -/
theorem point_automorphism_integral_transport_inverse :
    ∃ S : CoefficientDerivedSystemCalculus l E (Spec (.of D.k)),
    Nonempty (CoefficientDerivedSystemCoherence l E (Spec (.of D.k)) S) ∧
    ∃ θ : ∀ M : DerivedCategory (integralTowerModules l E (Spec (.of D.k))),
      (integralDerivedPullback l E g).obj M ≅
        (inverseImageIntegralDerived l E g).obj
          ((S.reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj M),
    (∀ M : DerivedCategory (integralTowerModules l E (Spec (.of D.k))),
      inverseImagePullbackComparisonDerived l E g (frobeniusPointPrimeUnit D l hl)
          (frobeniusPointPrimeUnit D l hl) M ≫ (θ M).hom =
        (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app M)) ∧
    (∀ (M M' : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) (f : M ⟶ M'),
      (integralDerivedPullback l E g).map f ≫ (θ M').hom =
        (θ M).hom ≫ (inverseImageIntegralDerived l E g).map
          ((S.reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).map f)) ∧
    ∃ Δ : ∀ N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))),
      IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N →
        ((integralDerivedPullback l E g).obj N ≅ (inverseImageIntegralDerived l E g).obj N),
    (∀ (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
      (hN : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N),
      (Δ N hN).inv = inverseImagePullbackComparisonDerived l E g
          (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) N ∧
      ∃ ε : (inverseImageIntegralDerived l E g).obj N ≅
          (inverseImageIntegralDerived l E g).obj
            ((S.reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj N),
        ε.hom = (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app N) ∧
        (Δ N hN).hom = (θ N).hom ≫ ε.inv) ∧
    (∀ (N N' : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
      (hN : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N)
      (hN' : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N') (v : N ⟶ N'),
      (integralDerivedPullback l E g).map v ≫ (Δ N' hN').hom =
        (Δ N hN).hom ≫ (inverseImageIntegralDerived l E g).map v) ∧
    ∃ T : ∀ N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))),
      IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N →
        ((pointInverseSections l E D hl none).obj N ≅
          (pointInverseSections l E D hl none).obj ((integralDerivedPullback l E g).obj N)),
    (∀ (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
      (hN : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N),
      (T N hN).hom = (pointInverseSigmaIso l E D hl g none).hom.app N ≫
          (pointInverseSections l E D hl none).map
            (inverseImagePullbackComparisonDerived l E g (frobeniusPointPrimeUnit D l hl)
              (frobeniusPointPrimeUnit D l hl) N) ∧
      (T N hN).inv = (pointInverseSections l E D hl none).map (Δ N hN).hom ≫
          (pointInverseSigmaIso l E D hl g none).inv.app N) ∧
    (∀ (N N' : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
      (hN : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N)
      (hN' : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N') (v : N ⟶ N'),
      (pointInverseSections l E D hl none).map v ≫ (T N' hN').hom =
          (T N hN).hom ≫
            (pointInverseSections l E D hl none).map ((integralDerivedPullback l E g).map v) ∧
      (pointInverseSections l E D hl none).map ((integralDerivedPullback l E g).map v) ≫
          (T N' hN').inv = (T N hN).inv ≫ (pointInverseSections l E D hl none).map v) := by
  let W := Spec (.of D.k)
  let G := inverseImageIntegralDerived l E g
  let P := integralDerivedPullback l E g
  let F := pointInverseSections l E D hl none
  let σ := pointInverseSigmaIso l E D hl g none
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  obtain ⟨κ, hk, _, hθ, _⟩ := inverseImagePullbackComparisonIntegral_natural.{t, u, 0, 0} l E g
    (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl)
  obtain ⟨θ, he⟩ := hθ S hS
  have hnormal (N) : κ.app N ≫ θ.hom.app N = G.map (S.adjunction.unit.app N) := by
    change κ.app N ≫ θ.hom.app N =
      (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app N)
    rw [he N, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hu (N) (hN : IsDerivedCompleteUnrestricted l E W N) :
      IsIso (S.adjunction.unit.app N) := by
    have hlW : IsUnit (l : Γ(W, ⊤)) := by
      apply W.toRingedSpace.isUnit_of_isUnit_germ
      intro y hy
      simpa only [map_natCast] using frobeniusPointPrimeUnit D l hl y
    exact (purNormalizedReconstruction l E W hlW S).2 N hN
  have hκ (N) (hN : IsDerivedCompleteUnrestricted l E W N) : IsIso (κ.app N) := by
    let := hu N hN
    rw [he N]
    infer_instance
  let Δ (N) (hN : IsDerivedCompleteUnrestricted l E W N) : P.obj N ≅ G.obj N :=
    letI := hκ N hN
    (asIso (κ.app N)).symm
  have hΔ (N N') (hN : IsDerivedCompleteUnrestricted l E W N)
      (hN' : IsDerivedCompleteUnrestricted l E W N') (v : N ⟶ N') :
      P.map v ≫ (Δ N' hN').hom = (Δ N hN).hom ≫ G.map v := by
    let := hκ N hN
    let := hκ N' hN'
    change P.map v ≫ inv (κ.app N') = inv (κ.app N) ≫ G.map v
    apply (cancel_epi (κ.app N)).1
    rw [← Category.assoc, ← κ.naturality]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
    rfl
  let T (N) (hN : IsDerivedCompleteUnrestricted l E W N) : F.obj N ≅ F.obj (P.obj N) :=
    σ.app N ≪≫ F.mapIso (Δ N hN).symm
  have hT (N N') (hN : IsDerivedCompleteUnrestricted l E W N)
      (hN' : IsDerivedCompleteUnrestricted l E W N') (v : N ⟶ N') :
      F.map v ≫ (T N' hN').hom = (T N hN).hom ≫ F.map (P.map v) := by
    change F.map v ≫ σ.hom.app N' ≫ F.map (κ.app N') =
      (σ.hom.app N ≫ F.map (κ.app N)) ≫ F.map (P.map v)
    have hn : F.map v ≫ σ.hom.app N' = σ.hom.app N ≫ F.map (G.map v) := by
      with_unfolding_all exact σ.hom.naturality v
    rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, κ.naturality,
      F.map_comp, Category.assoc]
  refine ⟨S, hS, fun N ↦ θ.app N, ?_, ?_, Δ, ?_, hΔ, T, ?_, ?_⟩
  · intro N
    rw [← hk N]
    exact hnormal N
  · intro M M' v
    exact θ.hom.naturality v
  · intro N hN
    refine ⟨hk N, ?_⟩
    let := hu N hN
    let ε := G.mapIso (asIso (S.adjunction.unit.app N))
    refine ⟨ε, rfl, ?_⟩
    apply (cancel_epi (Δ N hN).inv).1
    rw [Iso.inv_hom_id]
    change 𝟙 _ = κ.app N ≫ θ.hom.app N ≫ ε.inv
    rw [← Category.assoc, hnormal]
    exact ε.hom_inv_id.symm
  · intro N hN
    exact ⟨congrArg (fun f ↦ σ.hom.app N ≫ F.map f) (hk N), rfl⟩
  · intro N N' hN hN' v
    refine ⟨hT N N' hN hN' v, ?_⟩
    apply (cancel_epi (T N hN).hom).1
    rw [← Category.assoc, ← hT N N' hN hN' v]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
    rfl


end AlgebraicGeometry.ProEtale
