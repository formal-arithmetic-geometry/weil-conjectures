/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Sheaf.Paper.CoefficientDiagramUncurrying
import Sheaf.Paper.SystemCoefficientReductions
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Sheaf.CategoryTheory.DiagramSiteTopology

/-!
# The abelian category of smooth-purity coefficient towers

Source: blueprint main-20261015, sec-smooth-purity, sk-def-sp-coefficient-towers,
`sk-def-sp-coefficient-towers-abelian.md`, clauses (1)--(3); Bhatt--Scholze,
The pro-etale topology for schemes, Definition 3.5.3
(blueprint: det-sp-coefficient-towers-abelian).

The input category is the recorded `spCoefficientTowers`, not a tower of modules
with one fixed coefficient ring. The equivalence below only uncurries its product-site
module presheaves into the already defined strict semilinear systems. Its four
normalizations fix every section module, restriction, transition and morphism.
The existing scalar models and their normalized associators specify the derived
scalar extensions. All positive levels are represented: index n means level n+1.

## Main statements

- `sp_coefficient_towers_abelian`: Grothendieck abelianness, levelwise kernels,
  cokernels and filtered colimits, exact derived evaluation, and natural reduction
  maps induced by the strict transitions, with identity and composition compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

-- Use the existing larger-coefficient transport while elaborating these declarations.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- Retain commutativity in the existing coefficient ring tower. Forgetting commutativity
recovers `spCoefficientRings`: the same constant quotient sheaves and the same reduction
ring homomorphisms are used. This is a change of bundled target category only.
Source: blueprint, coefficient-tower lemma, clause (3)
(blueprint: det-sp-coefficient-towers-abelian). -/
def spCoefficientCommRings :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)} :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ (constantSheaf (Scheme.ProEt.topology T)
      CommRingCat.{max u (t + 1)}).obj (CommRingCat.of
        (ULift.{t + 1}
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)))))
    (fun n ↦ (constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
            ULift.ringEquiv.toRingHom))))

/-- The abelian axioms for the existing componentwise preadditive structure.
Source: blueprint, coefficient-tower lemma, clause (1); Stacks 03DA and 03DB
(blueprint: det-sp-coefficient-towers-abelian).
Proof: give ℕ × T.ProEt the vertical topology, whose sheaf condition is exactly the
recorded levelwise condition. The actual varying coefficient presheaf is a ring sheaf:
its restriction to level n is naturally isomorphic to the recorded ring sheaf R_n.
Rebundle each tower as a sheaf of modules over this ring sheaf. The inverse forgets
only the global sheaf proof and retains its levelwise form; the two functors fix all
presheaf modules and all maps, so their unit and counit are identities. Transfer finite
products along this equivalence and use Mathlib's abelianOfEquivalence, which uses the
existing componentwise preadditive structure. Extract normality, finite products,
kernels and cokernels from this abelian structure. -/
theorem sp_coefficient_towers_abelian_axioms :
    IsNormalMonoCategory (spCoefficientTowers l E T) ∧
      IsNormalEpiCategory (spCoefficientTowers l E T) ∧
      HasFiniteProducts (spCoefficientTowers l E T) ∧
      HasKernels (spCoefficientTowers l E T) ∧
      HasCokernels (spCoefficientTowers l E T) := by
  let K := verticalDiagramSiteTopology ℕ T.ProEt (Scheme.ProEt.topology T)
  have hs (M : PresheafOfModules.{max u (t + 1)} (spCoefficientPresheaf l E T)) :
      Presheaf.IsSheaf K M.presheaf ↔ spCoefficientTowerSheafCondition l E T M := by
    exact verticalDiagramSite_isSheaf_iff ℕ T.ProEt (Scheme.ProEt.topology T) M.presheaf
  let R : Sheaf K RingCat.{max u (t + 1)} :=
    ⟨spCoefficientPresheaf l E T, by
      apply (verticalDiagramSite_isSheaf_iff ℕ T.ProEt (Scheme.ProEt.topology T) _).2
      intro n
      let i : (Prod.sectR n T.ProEt).op ⋙ spCoefficientPresheaf l E T ≅
          (spCoefficientRing l E T n).obj :=
        NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
          intro U V f
          simp [spCoefficientPresheaf, spCoefficientRings, spCoefficientRing,
            Prod.sectR]
          rfl)
      exact (Presheaf.isSheaf_of_iso_iff i).2 (spCoefficientRing l E T n).property⟩
  let F : spCoefficientTowers l E T ⥤ SheafOfModules.{max u (t + 1)} R :=
    { obj := fun M ↦ ⟨M.obj, (hs M.obj).2 M.property⟩
      map := fun f ↦ ⟨f.hom⟩ }
  let G : SheafOfModules.{max u (t + 1)} R ⥤ spCoefficientTowers l E T :=
    { obj := fun M ↦ ⟨M.val, (hs M.val).1 M.isSheaf⟩
      map := fun f ↦ ObjectProperty.homMk f.val }
  let e : spCoefficientTowers l E T ≌ SheafOfModules.{max u (t + 1)} R :=
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
      counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) }
  have : e.functor.IsEquivalence := e.isEquivalence_functor
  have : HasFiniteProducts (spCoefficientTowers l E T) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  let a : Abelian (spCoefficientTowers l E T) := abelianOfEquivalence e.functor
  exact ⟨a.toIsNormalMonoCategory, a.toIsNormalEpiCategory,
    a.has_finite_products, a.has_kernels, a.has_cokernels⟩

/-- The abelian structure extends the existing componentwise addition of tower maps;
all remaining fields are proofs of the preceding named axioms.
Source: blueprint, coefficient-tower lemma, clause (1)
(blueprint: det-sp-coefficient-towers-abelian). -/
instance spCoefficientTowersAbelian : Abelian (spCoefficientTowers l E T) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := (sp_coefficient_towers_abelian_axioms l E T).1
  toIsNormalEpiCategory := (sp_coefficient_towers_abelian_axioms l E T).2.1
  has_finite_products := (sp_coefficient_towers_abelian_axioms l E T).2.2.1
  has_kernels := (sp_coefficient_towers_abelian_axioms l E T).2.2.2.1
  has_cokernels := (sp_coefficient_towers_abelian_axioms l E T).2.2.2.2

/-- Evaluation after the sectionwise specified identification of the recorded tower
category with strict semilinear systems. Source: blueprint, coefficient-tower lemma,
clause (2) (blueprint: det-sp-coefficient-towers-abelian). -/
abbrev spCoefficientEvaluation
    (e : spCoefficientTowers l E T ≌
      StrictRingSystem.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T))
    (n : ℕ) :=
  e.functor ⋙ systemEvaluation.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n

/-- The three clauses of the coefficient-tower lemma, with the actual tower category
and all identifications fixed on sections. The scalar and tensor fields are the
existing canonical derived-change models, not arbitrary maps or isomorphisms.
Source: blueprint, coefficient-tower lemma, clauses (1)--(3); Bhatt--Scholze,
Definition 3.5.3 (blueprint: det-sp-coefficient-towers-abelian). -/
structure SpCoefficientTowersAbelian where
  /-- Uncurrying into the existing varying-coefficient strict systems. -/
  equivalence : spCoefficientTowers l E T ≌
    StrictRingSystem.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T)
  /-- Uncurrying fixes the module of sections, including its scalar action. -/
  sections : ∀ (M : spCoefficientTowers l E T) (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq (((equivalence.functor.obj M).level n).val.obj U) (M.obj.obj (op (n, U.unop)))
  /-- Uncurrying fixes vertical restriction maps. -/
  restrictions : ∀ (M : spCoefficientTowers l E T) (n : ℕ)
    {U V : T.ProEtᵒᵖ} (f : U ⟶ V),
    HEq (((equivalence.functor.obj M).level n).val.map f)
      (M.obj.map (Prod.mkHom (𝟙 n) f.unop).op)
  /-- Uncurrying fixes every iterated transition, including the identity. -/
  transitions : ∀ (M : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ),
    HEq (((equivalence.functor.obj M).transition h).val.app U)
      (M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
  /-- Uncurrying fixes all components of every linear tower map. -/
  morphisms : ∀ {M N : spCoefficientTowers l E T} (f : M ⟶ N) (n : ℕ)
    (U : T.ProEtᵒᵖ),
    HEq (((equivalence.functor.map f).app n).val.app U) (f.hom.app (op (n, U.unop)))
  /-- Addition is the componentwise addition of linear maps. -/
  [equivalenceAdditive : equivalence.functor.Additive]
  /-- Grothendieck abelianness includes a generator, colimits and exact filtered colimits. -/
  grothendieck : IsGrothendieckAbelian.{max u (t + 1)} (spCoefficientTowers l E T)
  /-- Evaluation preserves finite limits, in particular kernels. -/
  [evaluationLimits : ∀ n : ℕ,
    PreservesFiniteLimits (spCoefficientEvaluation l E T equivalence n)]
  /-- Evaluation preserves finite colimits, in particular cokernels. -/
  [evaluationColimits : ∀ n : ℕ,
    PreservesFiniteColimits (spCoefficientEvaluation l E T equivalence n)]
  /-- Filtered colimits are computed at each coefficient level. -/
  filteredColimits : ∀ (I : Type (max u (t + 1))) [SmallCategory I] [IsFiltered I]
    (n : ℕ), PreservesColimitsOfShape I (spCoefficientEvaluation l E T equivalence n)
  /-- The ordinary unbounded localization of tower complexes, in the standard universe. -/
  [hasDerived : HasDerivedCategory.{max u (t + 1) + 1} (spCoefficientTowers l E T)]
  /-- Existing universal derived scalar extensions, with their normalized adjunctions. -/
  scalar : SystemScalarAssignment.{t + 1, t, max u (t + 1)} (J := Scheme.ProEt.topology T)
  /-- Existing ordinary tensor associators and their canonical K-flat derived comparisons. -/
  tensor : SystemTensorCoherence.{t + 1, t, max u (t + 1)} scalar
  /-- Underived reduction along an actual coefficient transition. -/
  ordinaryReduction : ∀ {m n : ℕ} (h : m ≤ n),
    spCoefficientEvaluation l E T equivalence n ⋙
      systemTensor.{t + 1, t, max u (t + 1)} scalar (spCoefficientCommRings l E T) h ⟶
    spCoefficientEvaluation l E T equivalence m
  /-- It is the tensor adjunct of the specified strict semilinear transition;
  on local pure tensors it sends c tensor x to c times t(x). -/
  ordinaryReduction_eq : ∀ {m n : ℕ} (h : m ≤ n) (M : spCoefficientTowers l E T),
    (ordinaryReduction h).app M =
      ((systemTensorAdj.{t + 1, t, max u (t + 1)} scalar
        (spCoefficientCommRings l E T) h).homEquiv _ _).symm
        ((equivalence.functor.obj M).transition h)
  /-- Reduction is a natural transformation on the ordinary derived tower category. -/
  reduction : ∀ {m n : ℕ} (h : m ≤ n),
    (spCoefficientEvaluation l E T equivalence n).mapDerivedCategory ⋙
      systemDerivedTensor.{t + 1, t, max u (t + 1)} scalar (spCoefficientCommRings l E T) h ⟶
    (spCoefficientEvaluation l E T equivalence m).mapDerivedCategory
  /-- The derived comparison followed by the actual termwise reduction induces reduction.
  This holds for all complexes, so in particular it fixes every K-flat computation. -/
  reduction_rep : ∀ {m n : ℕ} (h : m ≤ n)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ),
    (reduction h).app (DerivedCategory.Q.obj P) =
      (systemDerivedTensor.{t + 1, t, max u (t + 1)} scalar (spCoefficientCommRings l E T) h).map
        ((spCoefficientEvaluation l E T equivalence n).mapDerivedCategoryFactors.hom.app P) ≫
      (scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.ε.app
        (((spCoefficientEvaluation l E T equivalence n).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinaryReduction h)
        (.up ℤ)).app P) ≫
      (spCoefficientEvaluation l E T equivalence m).mapDerivedCategoryFactors.inv.app P
  /-- Equal levels give the canonical tensor unitor, including the first positive level. -/
  reduction_identity : ∀ (n : ℕ) (M : DerivedCategory (spCoefficientTowers l E T)),
    (reduction (Nat.le_refl n)).app M =
      (tensor.derivedUnit (spCoefficientCommRings l E T) n).hom.app
        ((spCoefficientEvaluation l E T equivalence n).mapDerivedCategory.obj M)
  /-- Successive reductions equal direct reduction under the canonical tensor associator. -/
  reduction_comp : ∀ {r m n : ℕ} (h : r ≤ m) (k : m ≤ n)
    (M : DerivedCategory (spCoefficientTowers l E T)),
    (systemDerivedTensor.{t + 1, t, max u (t + 1)} scalar (spCoefficientCommRings l E T) h).map
        ((reduction k).app M) ≫ (reduction h).app M =
      (tensor.derivedAssoc (spCoefficientCommRings l E T) h k).hom.app
        ((spCoefficientEvaluation l E T equivalence n).mapDerivedCategory.obj M) ≫
      (reduction (h.trans k)).app M

/-- The category of coefficient towers is Grothendieck abelian with levelwise kernels,
cokernels and filtered colimits. Evaluation is exact and induces the indicated ordinary
unbounded derived functor. The actual strict transitions induce natural derived
reduction maps compatible with identities and composition.
Source: blueprint main-20261015, coefficient-tower lemma, clauses (1)--(3);
Bhatt--Scholze, Definition 3.5.3 (blueprint: det-sp-coefficient-towers-abelian).

Proof:
1. Uncurry the coefficient diagram into strict semilinear systems. The equality
between the commutative coefficient diagram after forgetting commutativity and the
recorded ring diagram follows from their identical adjacent quotient maps. The
uncurrying equivalence fixes section modules, restrictions, transitions and maps.
2. The existing system-level theory gives Grothendieck abelianness, finite-limit and
finite-colimit preservation by evaluation, and coproduct preservation. The equivalence
is additive because it preserves binary products. Transport Grothendieck abelianness
along it. Coproduct and coequalizer preservation give all small colimits, hence the
required filtered colimits. Use the standard ordinary unbounded derived category.
3. Take the scalar assignment and normalized tensor coherence from the same
system-level theory. Ordinary reduction is the tensor adjunct of the actual strict
transition; adjunction naturality proves that it is a natural transformation.
Compose the evaluation localization comparison, the scalar comparison, the ordinary
reduction on complexes, and the inverse evaluation comparison. Both endpoints factor
through derived localization, so this natural transformation descends uniquely. Its
formula on every complex follows from the localization lifting formula.
4. The ordinary identity and composition equations follow by transposing under the
scalar adjunctions, evaluating on unit tensors, and using the strict transition laws.
To extend the normalized derived tensor comparisons from flat-term K-flat complexes
to every complex, choose a flat-term K-flat resolution of a single coefficient-level
complex. Naturality and cancellation of the image of its quasi-isomorphism extend
equality. This uses no simultaneous tower resolution. Localization extensionality
then reduces the derived identity and composition equations to complexes. Cancel the
evaluation comparison isomorphisms, use naturality of the scalar comparison and
derived associator, and apply the ordinary equations. -/
theorem sp_coefficient_towers_abelian : Nonempty (SpCoefficientTowersAbelian l E T) := by
  let B := spCoefficientCommRings l E T
  have hR : spCoefficientPresheaf l E T = CoefficientDiagram.ring B := by
    have hB : spCoefficientRings l E T =
        B ⋙ sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat) := by
      let i : spCoefficientRings l E T ⟶
          B ⋙ sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat) :=
        NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
          simp only [Functor.comp_map, spCoefficientRings, B, spCoefficientCommRings,
            Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp]
          rfl)
      refine CategoryTheory.Functor.ext (F := spCoefficientRings l E T)
        (G := B ⋙ sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat))
        (fun _ ↦ rfl) ?_
      intro X Y f
      have hi := i.naturality f
      change (spCoefficientRings l E T).map f ≫ 𝟙 _ =
        𝟙 _ ≫ (B ⋙ sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat RingCat)).map f at hi
      simpa only [Category.comp_id, Category.id_comp, eqToHom_refl] using hi
    unfold spCoefficientPresheaf CoefficientDiagram.ring
    rw [hB]
    rfl
  obtain ⟨e, hn⟩ :=
    CoefficientDiagram.exists_uncurrying_of_eq B (spCoefficientPresheaf l E T) hR
  let e' : spCoefficientTowers l E T ≌
      StrictRingSystem.{t + 1, t, max u (t + 1)} B := e
  obtain ⟨H⟩ := systemLevelLeftExtensionTheory.{t + 1, t, max u (t + 1)}
    (J := Scheme.ProEt.topology T)
  let : IsGrothendieckAbelian.{max u (t + 1)} (StrictRingSystem.{t + 1, t, max u (t + 1)} B) :=
    H.grothendieck B
  let : PreservesFiniteLimits e'.functor := inferInstance
  let : PreservesFiniteColimits e'.functor := inferInstance
  let : e'.functor.Additive := Functor.additive_of_preserves_binary_products e'.functor
  let : HasDerivedCategory.{max u (t + 1) + 1} (spCoefficientTowers l E T) :=
    HasDerivedCategory.standard (spCoefficientTowers l E T)
  refine ⟨{ equivalence := e'
            sections := hn.sections
            restrictions := hn.restrictions
            transitions := hn.transitions
            morphisms := hn.morphisms
            equivalenceAdditive := inferInstance
            grothendieck := IsGrothendieckAbelian.of_equivalence e'.symm
            evaluationLimits := fun n ↦ inferInstance
            evaluationColimits := fun n ↦ inferInstance
            filteredColimits := ?_
            hasDerived := inferInstance
            scalar := H.scalar
            tensor := H.tensor
            ordinaryReduction := fun h ↦
              presentedOrdinaryReduction H.scalar B e'.functor h
            ordinaryReduction_eq := fun _ _ ↦ rfl
            reduction := fun h ↦ presentedDerivedReduction H.scalar B e'.functor h
            reduction_rep := fun h P ↦
              presentedDerivedReduction_rep H.scalar B e'.functor h P
            reduction_identity := fun n M ↦
              presentedDerivedReduction_identity H.scalar B H.tensor e'.functor n M
            reduction_comp := fun h k M ↦
              presentedDerivedReduction_comp H.scalar B H.tensor e'.functor h k M }⟩
  intro I _ _ n
  let : HasCoproducts.{max u (t + 1)} (StrictRingSystem.{t + 1, t, max u (t + 1)} B) :=
    H.coproducts B
  let (I : Type (max u (t + 1))) :
      PreservesColimitsOfShape (Discrete I) (systemEvaluation B n) :=
    H.evaluationCoproducts B n I
  let : PreservesColimitsOfSize.{max u (t + 1), max u (t + 1)}
      (systemEvaluation B n) :=
    preservesColimits_of_preservesCoequalizers_and_coproducts (systemEvaluation B n)
  exact inferInstance

end AlgebraicGeometry.ProEtale

-- Preserve the inherited instance environment for importing modules.
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
