/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.FiniteModelTopologyComparisonMaps
public import Sheaf.Paper.NormAlgclCohomologyTopologyComparison
public import Sheaf.Paper.InternalScalarTensorComparison
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Paper.QlbarInternalHomCoefficientComparison
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite-model derived global Hom and coefficient topology

Source: blueprint main-20261015, stability direct-images proof, paragraph (3),
agent topology-comparison obligation, with the eight-step DAG proof
(blueprint: lem-sfb-finite-model-topology-derived-hom).

All scalar extensions below are the existing total left derived functors. The tensor
comparison uses the scalar-unit normalized ordinary comparison and its K-flat derived
lift. In particular no flatness assumption is made on the coefficient inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u a₀ b₀ a₁ b₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteModelTopologyHom

section ScalarMate
variable {C : Type a₀} [Category.{b₀} C] {D : Type a₁} [Category.{b₁} D]
variable (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
  (S : D ⥤ D ⥤ D) (J : Dᵒᵖ ⥤ D ⥤ D)
  (adj : T ⊣₂ H) (adj' : S ⊣₂ J) (F : C ⥤ D)
  (μ : (Functor.postcompose₂.obj F).obj T ≅
    (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S)
private def scalarMate (K L : C) :
    F.obj ((H.obj (op K)).obj L) ⟶ (J.obj (op (F.obj K))).obj (F.obj L) :=
  adj'.homEquiv ((μ.inv.app K).app ((H.obj (op K)).obj L) ≫
    F.map ((adj.adj K).counit.app L))
private theorem scalarMate_naturality (K K' L L' : C) (f : K' ⟶ K) (g : L ⟶ L') :
    F.map (((H.map f.op).app L) ≫ (H.obj (op K')).map g) ≫
      scalarMate T H S J adj adj' F μ K' L' =
    scalarMate T H S J adj adj' F μ K L ≫
      (J.map (F.map f).op).app (F.obj L) ≫ (J.obj (op (F.obj K'))).map (F.map g) := by
  unfold scalarMate
  rw [← adj'.homEquiv_naturality_two,
    ← adj'.homEquiv_naturality_one_assoc, ← adj'.homEquiv_naturality_three]
  apply congrArg adj'.homEquiv
  let A := (H.obj (op K)).obj L
  let A' := (H.obj (op K')).obj L'
  let h : A ⟶ A' := (H.map f.op).app L ≫ (H.obj (op K')).map g
  have hn : (S.obj (F.obj K')).map (F.map h) ≫ (μ.inv.app K').app A' =
      (μ.inv.app K').app A ≫ F.map ((T.obj K').map h) :=
    (μ.inv.app K').naturality h
  have hf : (S.map (F.map f)).app (F.obj A) ≫ (μ.inv.app K).app A =
      (μ.inv.app K').app A ≫ F.map ((T.map f).app A) :=
    NatTrans.congr_app (μ.inv.naturality f) A
  have hc : (T.obj K').map h ≫ (adj.adj K').counit.app L' =
      (T.map f).app A ≫ (adj.adj K).counit.app L ≫ g := by
    dsimp only [h]
    have hg := (adj.adj K').counit.naturality g
    change (T.obj K').map ((H.obj (op K')).map g) ≫
      (adj.adj K').counit.app L' = (adj.adj K').counit.app L ≫ g at hg
    rw [Functor.map_comp, Category.assoc, hg, ← Category.assoc]
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      A, Category.assoc] using
      congrArg (fun k ↦ k ≫ g)
      (NatTrans.congr_app (adj.whiskerLeft_map_counit f) L).symm
  change (S.obj (F.obj K')).map (F.map h) ≫
      (μ.inv.app K').app A' ≫ F.map ((adj.adj K').counit.app L') =
    ((S.map (F.map f)).app (F.obj A) ≫
      (μ.inv.app K).app A ≫ F.map ((adj.adj K).counit.app L)) ≫ F.map g
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, hc,
    F.map_comp, F.map_comp]
  rw [← Category.assoc, ← Category.assoc, ← hf]
  simp only [Category.assoc]

end ScalarMate

variable (X : Scheme.{u})

/-- Naturality of the specified evaluation transpose in both inputs.
Source: DAG proof steps 7--8, Stacks 08J9
(blueprint: lem-sfb-finite-model-topology-derived-hom).
Proof: naturality of the tensor comparison and evaluation makes the two evaluation
transposes identical. The tensor-Hom adjunction is a bijection, giving the equality. -/
theorem homComparison_naturality
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (K K' N N' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (f : K' ⟶ K) (g : N ⟶ N') :
    (CondensedRing.internalScalarExtension a X).map (homArrow X Λ f g) ≫
        homComparison X a K' N' =
      homComparison X a K N ≫ homArrow X Λ'
        ((CondensedRing.internalScalarExtension a X).map f)
        ((CondensedRing.internalScalarExtension a X).map g) := by
  simpa only [homComparison, homArrow, scalarMate, ParametrizedAdjunction.homEquiv,
    CondensedRing.derivedTensorHomAdjunction, Category.assoc] using
    scalarMate_naturality
      (CondensedRing.derivedTensor Λ X) (CondensedRing.derivedHom Λ X)
      (CondensedRing.derivedTensor Λ' X) (CondensedRing.derivedHom Λ' X)
      (CondensedRing.derivedTensorHomAdjunction₂ Λ X)
      (CondensedRing.derivedTensorHomAdjunction₂ Λ' X)
      (CondensedRing.internalScalarExtension a X)
      (CondensedRing.internalScalarTensorIso a X) K K' N N' f g

private theorem homArrow_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D F G : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (f : B ⟶ A) (g : C ⟶ D) (h : F ⟶ B) (i : D ⟶ G) :
    homArrow X Λ f g ≫ homArrow X Λ h i = homArrow X Λ (h ≫ f) (g ≫ i) := by
  exact ((Functor.uncurry.obj (CondensedRing.derivedHom Λ X)).map_comp
    (Prod.mkHom f.op g) (Prod.mkHom h.op i)).symm

private theorem globalize_naturality
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    {V V' : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    {W W' : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))}
    (f : V ⟶ V') (g : W ⟶ W')
    (t : (CondensedRing.internalScalarExtension a X).obj V ⟶ W)
    (t' : (CondensedRing.internalScalarExtension a X).obj V' ⟶ W')
    (h : (CondensedRing.internalScalarExtension a X).map f ≫ t' = t ≫ g) :
    (sections X (condensedRingObj Λ X)).map f ≫ globalize X a V' W' t' =
      globalize X a V W t ≫ (sections X (condensedRingObj Λ' X)).map g := by
  have hm := (scalarAdjunction X a).homEquiv_naturality_left_square f t' t g h
  dsimp only [globalize, restrictionMate]
  rw [← Functor.map_comp_assoc, hm, Functor.map_comp, Category.assoc]
  have hn := (restrictionSections X (coefficientMap a X)).hom.naturality g
  change (sections X (condensedRingObj Λ X)).map
      ((Mod.comap (coefficientMap a X)).mapDerivedCategory.map g) ≫ _ = _ at hn
  simpa only [Category.assoc] using congrArg
    (fun z ↦ (sections X (condensedRingObj Λ X)).map
      ((scalarAdjunction X a).homEquiv V W t) ≫ z) hn

private theorem towerHomComparison_naturality
    {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    [MonObj Λ''] [IsCommMonObj Λ'']
    (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
    (K K' N N' : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (f : K' ⟶ K) (g : N ⟶ N') :
    (CondensedRing.internalScalarExtension b X).map
        (homArrow X Λ' ((CondensedRing.internalScalarExtension a X).map f)
          ((CondensedRing.internalScalarExtension a X).map g)) ≫
        towerHomComparison X a b K' N' =
      towerHomComparison X a b K N ≫
        homArrow X Λ'' ((CondensedRing.internalScalarExtension (a ≫ b) X).map f)
          ((CondensedRing.internalScalarExtension (a ≫ b) X).map g) := by
  dsimp only [towerHomComparison]
  rw [← Category.assoc, homComparison_naturality, Category.assoc,
    homArrow_comp, Category.assoc, homArrow_comp]
  congr 2
  · exact ((coefficientComposition X a b).inv.naturality f).symm
  · exact (coefficientComposition X a b).hom.naturality g

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (K N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj E) X)))

/-- Derived global Hom topology comparison for bounded finite-field models, including
continuity and the equality of the actual comparison maps.

Source: blueprint main-20261015, stability direct-images proof, paragraph (3), the
agent-created obligation extracted from the supported finite-stage topology defect
(blueprint: lem-sfb-finite-model-topology-derived-hom).

Proof plan, following the eight steps of the DAG:
1. Use lem-pe-internal-section-tensor-comparison and
   lem-sfb-module-object-ringed-site-derived-comparison. The section-action equivalence
   preserves underlying sheaves, balanced tensor relations, K-flat total complexes,
   internal Hom and evaluation. Scalar extension and restriction therefore retain
   their specified maps in either presentation.
2. X is Noetherian by lem-weil-pbc-finite-type-over-noetherian. Apply
   lem-sfb-adic-constructibility-predicate-comparison to E, then
   lem-sfb-dc-hom-small-coefficients to K,N, then the predicate comparison backwards.
   This makes D bounded constructible in both senses.
3. Apply lem-sfb-constructible-internal-hom-continuity to E and K. Exact termwise
   colimits of the functorial Hom representatives give the specified quasi-isomorphism
   for every filtered diagram with a common termwise lower bound.
4. Apply lem-sfb-qlbar-internal-hom-coefficient-comparison to A to C_X. Step 3 is its
   continuity assumption; boundedness of N supplies the lower cohomological bound.
   It makes phi_C invertible, with the prescribed evaluation transpose and naturality.
5. Apply lem-sfb-norm-algcl-internal-hom-base-change to make phi_B invertible with
   exactly the same scalar-extended evaluation normalization. C and B remain distinct.
6. Apply lem-sfb-norm-algcl-cohomology-topology-comparison to D from step 2.
   lem-coef-derived-sections-scalar-coherence identifies sections after restriction;
   hence the actual global coefficient comparison is invertible.
7. Use lem-sfb-ringed-derived-monoidal-comparisons and
   lem-sfb-dc-hom-scalar-adjunction. The transposes of chi composed with J(phi_C)
   and phi_B coincide under JS_C to S_B: each is B tensor_A evaluation.
   Tensor-Hom adjunction gives their equality. Naturality of the scalar unit then
   gives theta composed with phi_C equals Res(phi_B) composed with m_D.
8. Apply derived sections and its scalar coherence to step 7. By definition Psi is
   R Gamma(theta), so the displayed square commutes and its other three sides are
   invertible by steps 4--6. Hence Psi is invertible. Evaluation, transposition,
   scalar units and the monoidal comparisons are natural in both inputs. Step 1
   transports these same maps and their equalities to the section-ring presentation.
No site-perfectness, flatness of c_X, completeness or cohomological dimension is used. -/
theorem finiteModelTopologyDerivedHom
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (a : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (hK : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X K)
    (hN : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X N) :
    constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
        (finiteHom X ℓ E K N) ∧
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X)
        (finiteHom X ℓ E K N) ∧
    QlbarInternalHom.Continuous X ℓ E K ∧
    IsIso (homComparison X (finiteToUnion ℓ E) K N) ∧
    IsIso (homComparison X (finiteToNorm ℓ E) K N) ∧
    IsIso (globalCoefficientComparison X ℓ E
      (finiteHom X ℓ E K N)) ∧
    IsIso ((sections X (condensedRingObj (Profinite.continuousMapRingObj E) X)).map
      (finiteCoefficientComparison X ℓ E
        (finiteHom X ℓ E K N))) ∧
    ((sections X (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).map
        (homComparison X (finiteToUnion ℓ E) K N) ≫ globalHomComparison X ℓ E K N =
      globalCoefficientComparison X ℓ E
          (finiteHom X ℓ E K N) ≫
        (sections X
          (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X)).map
          (homComparison X (finiteToNorm ℓ E) K N)) ∧
    IsIso (globalHomComparison X ℓ E K N) := by
  sorry

/-- Both scalar-extended evaluation transposes are B tensor_A evaluation. This is the
internal Hom equality before inserting the scalar unit and taking sections.
Source: DAG proof step 7, normalized monoidal comparisons and scalar-Hom adjunction
(blueprint: lem-sfb-finite-model-topology-derived-hom).
Proof: transpose both sides. The canonical monoidal composition comparison takes the
scalar extension of C tensor_A evaluation to B tensor_A evaluation. The two transposes
are equal, so uniqueness in the tensor-Hom adjunction gives this equation. -/
theorem scalarExtendedEvaluation :
    evaluationRoute X (finiteToUnion ℓ E) (NormAlgclComparison.coefficientInclusion ℓ) K N =
      homComparison X (finiteToNorm ℓ E) K N := by
  sorry

/-- Sections computed after restriction to A identify the actual A-linear m_V with
its C-linear presentation. These comparisons are natural, and do not use flatness.
Source: DAG scalar-forgetting convention and proof step 6 (Stacks 0D6E)
(blueprint: lem-sfb-finite-model-topology-derived-hom).
Proof: composition coherence for exact scalar restriction identifies its underlying
sheaf functor with the identity on underlying sheaves. Apply the canonical localization
composition isomorphisms, then derived sections. Their naturality gives the equation. -/
theorem finiteCoefficientComparison_sections :
    (sections X (condensedRingObj (Profinite.continuousMapRingObj E) X)).map
        (finiteCoefficientComparison X ℓ E K) =
      (restrictionSections X (coefficientMap (finiteToUnion ℓ E) X)).hom.app
          ((toUnion X ℓ E).obj K) ≫
        globalCoefficientComparison X ℓ E K ≫
        (restrictionSections X (coefficientMap (finiteToNorm ℓ E) X)).inv.app
          ((toNorm X ℓ E).obj K) := by
  sorry

/-- Naturality of the actual coefficient and global Hom maps for every arrow of K,N.
Source: DAG final naturality clause, proof steps 7--8
(blueprint: lem-sfb-finite-model-topology-derived-hom).
Proof: evaluation is natural contravariantly and covariantly. Transpose through the
natural scalar tensor comparisons, use naturality of the scalar unit and composition
comparisons, and apply the derived sections functor and scalar coherence. -/
theorem globalComparison_naturality
    (K' N' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) (f : K' ⟶ K) (g : N ⟶ N') :
    ((sections X (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).map
        (homArrow X (Profinite.padicAlgClRingObj ℓ)
          ((toUnion X ℓ E).map f) ((toUnion X ℓ E).map g)) ≫
        globalHomComparison X ℓ E K' N' =
      globalHomComparison X ℓ E K N ≫
        (sections X (condensedRingObj
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X)).map
            (homArrow X (Profinite.continuousMapRingObj (PadicAlgCl ℓ))
              ((toNorm X ℓ E).map f) ((toNorm X ℓ E).map g))) ∧
    ((sections X (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).map
        ((toUnion X ℓ E).map f) ≫ globalCoefficientComparison X ℓ E K =
      globalCoefficientComparison X ℓ E K' ≫
        (sections X (condensedRingObj
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X)).map ((toNorm X ℓ E).map f)) := by
  constructor
  · exact globalize_naturality X (NormAlgclComparison.coefficientInclusion ℓ)
      _ _ _ _ (towerHomComparison_naturality X (finiteToUnion ℓ E)
        (NormAlgclComparison.coefficientInclusion ℓ) K K' N N' f g)
  · exact globalize_naturality X (NormAlgclComparison.coefficientInclusion ℓ)
      _ _ _ _ ((reassociation X ℓ E).hom.naturality f)

/-- The same scalar-Hom comparisons and the equality of their actual maps in the
section-ring presentation, via the recorded underlying-sheaf-preserving equivalence.
Source: DAG final section-ring clause and proof steps 1, 8, Stacks 08J9--08JA
(blueprint: lem-sfb-finite-model-topology-derived-hom).
Proof: step 1 identifies balanced coequalizers, flat-term K-flat total complexes,
restriction, Hom and evaluation under this exact equivalence. Apply its derived
functor to the two scalar comparisons and to the equality of step 7. Equivalences
preserve isomorphisms, so the identifications are those of the section-ring model.
Since the equivalence fixes underlying abelian sheaves, derived sections and the
scalar-forgetting square of step 8 are the same under their canonical comparisons. -/
theorem sectionRingComparisons
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (a : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (hK : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X K)
    (hN : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X N) :
    IsIso ((ModuleObjectRingedComparison.forward (Profinite.padicAlgClRingObj ℓ) X).map
      (homComparison X (finiteToUnion ℓ E) K N)) ∧
    IsIso ((ModuleObjectRingedComparison.forward
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X).map
        (homComparison X (finiteToNorm ℓ E) K N)) ∧
    ((ModuleObjectRingedComparison.forward
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X).map
        (evaluationRoute X (finiteToUnion ℓ E)
          (NormAlgclComparison.coefficientInclusion ℓ) K N) =
      (ModuleObjectRingedComparison.forward
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X).map
          (homComparison X (finiteToNorm ℓ E) K N)) := by
  have h := finiteModelTopologyDerivedHom X ℓ E K N p hpℓ a hK hN
  have := h.2.2.2.1
  have := h.2.2.2.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact congrArg
    ((ModuleObjectRingedComparison.forward
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X).map)
    (scalarExtendedEvaluation X ℓ E K N)

end AlgebraicGeometry.ProEtale.FiniteModelTopologyHom
