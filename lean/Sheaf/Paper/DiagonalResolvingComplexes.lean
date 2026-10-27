/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.CategoryTheory.DiagramSiteModuleEquivalence
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.RingedTopoiTensorSections
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.DiagramSiteSheafEquivalence
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import Sheaf.Paper.RingedTopoiInverseImagePairing
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Constant diagrams of resolving complexes

Source: Stacks Project, Cohomology on Sites, Tags 06YN, 06YS and 06YU;
Modules on Sites, Tags 03DB, 03EL and 03ER; explicit diagram-evaluation argument
(blueprint: lem-sf-cbc-diagonal-resolving-complexes).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedTensor
open MonoidalCategory

namespace CategoryTheory.DiagonalResolving

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J C : Type u} [SmallCategory J] [SmallCategory C]
  (K : GrothendieckTopology C) (R : Sheaf K CommRingCat.{u})

/-- The commutative coefficient sheaf on the existing vertical product site.
Source: Stacks 03DB, product-site realization
(blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
def coefficient : Sheaf (diagramSiteTopology J C K) CommRingCat.{u} where
  obj := (Prod.snd Jᵒᵖ C).op ⋙ R.obj
  property := (diagramSite_isSheaf_iff J C K _).2 (fun _ ↦ R.property)

/-- The evaluation in the recorded module equivalence, with its actual section maps.
Source: Stacks 03DB, product-site realization
(blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev evaluate (j : J) :=
  (diagramSiteModuleEquivalence J C K (ringSheaf R)).functor ⋙
    (evaluation J (ringedSiteModules.{u} (ringSheaf R))).obj j

/-- The constant diagram transported by the inverse of the recorded module equivalence.
Source: Stacks 03DB, product-site realization
(blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev diagonal :=
  (Functor.const J : ringedSiteModules.{u} (ringSheaf R) ⥤ _) ⋙
    (diagramSiteModuleEquivalence J C K (ringSheaf R)).inverse

/-- Additivity of evaluation, inherited from its finite-product preservation.
Source: Stacks 03DB (blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable instance evaluate_additive (j : J) : (evaluate K R j).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of the constant-diagram functor, inherited from product preservation.
Source: Stacks 03DB (blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable instance diagonal_additive : (diagonal (J := J) K R).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The existing signed coproduct total tensor, with the specified sheaf monoidal structure.
Source: Stacks 06YL and 012Z
(blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev totalTensor
    (A P : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ) :=
  let := SheafOfModules.monoidalCategory R
  CochainComplex.mapBifunctor A P (MonoidalCategory.curriedTensor _)

/-- The existing total-tensor map, with no permutation of the two complex degrees.
Source: Stacks 012Z (blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev totalTensorMap
    {A A' P P' : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ}
    (a : A ⟶ A') (p : P ⟶ P') :=
  let := SheafOfModules.monoidalCategory R
  HomologicalComplex.mapBifunctorMap a p (MonoidalCategory.curriedTensor _) (ComplexShape.up ℤ)

/-- The existing inclusion of a tensor summand in its coproduct total degree.
Source: Stacks 012Z (blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev totalInclusion
    (A P : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ)
    (r s n : ℤ) (h : r + s = n) :=
  let := SheafOfModules.monoidalCategory R
  CochainComplex.ιMapBifunctor A P (MonoidalCategory.curriedTensor _) r s n h

/-- The constant complex is formed termwise, using the recorded diagram equivalence.
Source: Stacks 06YN, explicit diagram argument
(blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev diagonalComplex :=
  (diagonal (J := J) K R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Evaluation of complexes is termwise evaluation, with the original differentials.
Source: Stacks 010N (blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev evaluateComplex (j : J) :=
  (evaluate K R j).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Tensor with a fixed right module using the recorded monoidal structure.
Source: Stacks 03EK (blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev tensor (M Q : ringedSiteModules.{u} (ringSheaf R)) :=
  (SheafOfModules.monoidalCategory R).tensorObj M Q

/-- Tensor a pair of module maps with the recorded monoidal structure.
Source: Stacks 03EK (blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev tensorMap
    {M M' Q Q' : ringedSiteModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : Q ⟶ Q') :=
  (SheafOfModules.monoidalCategory R).tensorHom f g

/-- The standard localization into the derived category; no smallness choice is assumed.
Source: Stacks 06YU (blueprint: lem-sf-cbc-diagonal-resolving-complexes). -/
noncomputable abbrev derivedQ :=
  @DerivedCategory.Q (ringedSiteModules.{u} (ringSheaf R)) _ _
    (HasDerivedCategory.standard _)

-- Evaluation on sheaves of sets, with the same section-level normalization.
private abbrev evaluateSets (j : J) :=
  (diagramSiteSheafEquivalence J C K).functor ⋙
    (evaluation J (Sheaf K (Type u))).obj j

-- Ring and module operations are evaluated componentwise.
private noncomputable def evaluationAlgebraic (j : J) :
    SheafOfModules.AlgebraicInverseImage (evaluateSets K j) (coefficient K R) R where
  ringUnderlying := ObjectProperty.isoMk _ (Iso.refl _)
  ringAdd := fun _ _ _ _ h V x ↦ h (op (op j, V.unop)) x
  ringMul := fun _ _ _ _ h V x ↦ h (op (op j, V.unop)) x
  ringZero := fun _ _ h V x ↦ h (op (op j, V.unop)) x
  ringOne := fun _ _ h V x ↦ h (op (op j, V.unop)) x
  modules := evaluate K R j
  moduleUnderlying := NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _))
    (by intros; rfl)
  moduleAdd := fun _ _ _ _ _ h V x ↦ h (op (op j, V.unop)) x
  moduleZero := fun _ _ _ h V x ↦ h (op (op j, V.unop)) x
  moduleSMul := fun _ _ _ _ _ h V x ↦ h (op (op j, V.unop)) x

-- Apply the normalized inverse-image tensor comparison to evaluation.
private theorem evaluation_tensor (j : J) :
    ∃ μ : ∀ M N : ringedSiteModules.{u} (ringSheaf (coefficient (J := J) K R)),
        (evaluate K R j).obj (tensor _ (coefficient K R) M N) ≅
          tensor K R ((evaluate K R j).obj M) ((evaluate K R j).obj N),
      (∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
        (evaluate K R j).map (tensorMap _ (coefficient K R) f g) ≫ (μ M' N').hom =
          (μ M N).hom ≫ tensorMap K R ((evaluate K R j).map f)
            ((evaluate K R j).map g)) ∧
      ∀ M N (U : Cᵒᵖ) (x : M.val.obj (op (op j, U.unop)))
        (y : N.val.obj (op (op j, U.unop))),
        (μ M N).hom.val.app U (pure (coefficient K R) M N (op (op j, U.unop)) x y) =
          pure R ((evaluate K R j).obj M) ((evaluate K R j).obj N) U x y := by
  let E := diagramSiteSheafEquivalence J C K
  let adj := E.toAdjunction.comp (evaluationAdjunctionLeft (Sheaf K (Type u)) j)
  obtain ⟨μ, hn, hp⟩ := exists_inverseImageTensorComparison
    (coefficient K R) R (evaluateSets K j) (evaluationAlgebraic K R j) _ adj
  refine ⟨μ, hn, ?_⟩
  intro M N U x y
  let X := (underlying (coefficient K R)).obj M
  let Y := (underlying (coefficient K R)).obj N
  exact hp M N (X ⊗ Y) (CartesianMonoidalCategory.fst X Y)
    (CartesianMonoidalCategory.snd X Y) (pureSheaf (coefficient K R) M N)
    (fun _ _ ↦ rfl) U (x, y)

private noncomputable def diagonalEvaluation (j : J)
    (Q : ringedSiteModules.{u} (ringSheaf R)) :
    (evaluate K R j).obj ((diagonal K R).obj Q) ≅ Q :=
  ((diagramSiteModuleEquivalence J C K (ringSheaf R)).counitIso.app
    ((Functor.const J).obj Q)).app j

private theorem diagonalEvaluation_naturality (j : J)
    {Q Q' : ringedSiteModules.{u} (ringSheaf R)} (f : Q ⟶ Q') :
    (evaluate K R j).map ((diagonal K R).map f) ≫ (diagonalEvaluation K R j Q').hom =
      (diagonalEvaluation K R j Q).hom ≫ f := by
  ext U x
  rfl

private theorem evaluation_jointlyReflects :
    JointlyReflectIsomorphisms (evaluate (J := J) K R) := by
  apply JointlyFaithful.jointlyReflectsIsomorphisms
  constructor
  intro M N f g h
  apply (diagramSiteModuleEquivalence J C K (ringSheaf R)).functor.map_injective
  exact NatTrans.ext (funext h)

-- This criterion also covers the empty diagram category.
private theorem evaluation_acyclic_iff
    (A : CochainComplex (ringedSiteModules.{u}
      (ringSheaf (coefficient (J := J) K R))) ℤ) :
    A.Acyclic ↔ ∀ j : J, ((evaluateComplex K R j).obj A).Acyclic := by
  constructor
  · intro h j n
    exact ((evaluation_jointlyReflects K R).exactAt_iff A n).1 (h n) j
  · intro h n
    exact ((evaluation_jointlyReflects K R).exactAt_iff A n).2 (fun j ↦ h j n)

private theorem specialized_tensor :
    ∃ τ : ∀ (j : J)
        (M : ringedSiteModules.{u} (ringSheaf (coefficient (J := J) K R)))
        (Q : ringedSiteModules.{u} (ringSheaf R)),
        (evaluate K R j).obj (tensor _ (coefficient K R) M ((diagonal K R).obj Q)) ≅
          tensor K R ((evaluate K R j).obj M) Q,
      (∀ (j : J) M Q (U : Cᵒᵖ) (x : M.val.obj (op (op j, U.unop)))
        (q : Q.val.obj U),
        (τ j M Q).hom.val.app U
          (pure (coefficient K R) M ((diagonal K R).obj Q) (op (op j, U.unop)) x q) =
            pure R ((evaluate K R j).obj M) Q U x q) ∧
      (∀ (j : J) {M M' : ringedSiteModules.{u}
          (ringSheaf (coefficient (J := J) K R))}
        {Q Q' : ringedSiteModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : Q ⟶ Q'),
        (evaluate K R j).map (tensorMap _ (coefficient K R) f ((diagonal K R).map g)) ≫
            (τ j M' Q').hom =
          (τ j M Q).hom ≫ tensorMap K R ((evaluate K R j).map f) g) := by
  classical
  let := SheafOfModules.monoidalCategory R
  choose μ hn hp using evaluation_tensor (J := J) K R
  let τ := fun j M Q ↦ μ j M ((diagonal K R).obj Q) ≪≫
    tensorIso (Iso.refl _) (diagonalEvaluation K R j Q)
  refine ⟨τ, ?_, ?_⟩
  · intro j M Q U x q
    change (tensorMap K R (𝟙 _) (diagonalEvaluation K R j Q).hom).val.app U
      ((μ j M ((diagonal K R).obj Q)).hom.val.app U
        (pure (coefficient K R) M ((diagonal K R).obj Q)
          (op (op j, U.unop)) x q)) = _
    rw [hp, pure_map]
    rfl
  · intro j M M' Q Q' f g
    dsimp only [τ, Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, hn, Category.assoc]
    change _ ≫ ((evaluate K R j).map f ⊗ₘ
      (evaluate K R j).map ((diagonal K R).map g)) ≫
        (𝟙 _ ⊗ₘ (diagonalEvaluation K R j Q').hom) =
      (_ ≫ (𝟙 _ ⊗ₘ (diagonalEvaluation K R j Q).hom)) ≫
        ((evaluate K R j).map f ⊗ₘ g)
    simp only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, diagonalEvaluation_naturality]

-- Detect preservation of short exact sequences through every evaluation.
private theorem diagonal_flat (Q : ringedSiteModules.{u} (ringSheaf R))
    (hQ : SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := R) Q) :
    SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := coefficient (J := J) K R)
      ((diagonal K R).obj Q) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory (coefficient (J := J) K R)
  obtain ⟨τ, _, hn⟩ := specialized_tensor (J := J) K R
  have hQ' : exactFunctor _ _ (tensorRight Q) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R Q) hQ
  have : PreservesFiniteLimits (tensorRight Q) := hQ'.1
  have : PreservesFiniteColimits (tensorRight Q) := hQ'.2
  let T := tensorRight (C := ringedSiteModules.{u} (ringSheaf (coefficient K R)))
    ((diagonal (J := J) K R).obj Q)
  have hT : exactFunctor _ _ T := by
    apply ((Functor.exact_tfae T).out 0 3).1
    intro S hS
    apply ((evaluation_jointlyReflects K R).shortExact_iff (S.map T)).2
    intro j
    let t : T ⋙ evaluate K R j ≅ evaluate K R j ⋙ tensorRight Q :=
      NatIso.ofComponents (fun M ↦ τ j M Q) (by
        intro M M' f
        simpa [T] using hn j f (𝟙 Q))
    have : PreservesFiniteLimits (evaluate K R j) := by
      dsimp only [evaluate]
      infer_instance
    have : PreservesFiniteLimits (evaluate K R j ⋙ tensorRight Q) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteLimits (T ⋙ evaluate K R j) :=
      preservesFiniteLimits_of_natIso t.symm
    have : PreservesFiniteColimits (T ⋙ evaluate K R j) :=
      preservesFiniteColimits_of_natIso t.symm
    exact hS.map_of_exact (T ⋙ evaluate K R j)
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (coefficient K R)
      ((diagonal K R).obj Q)).symm hT

/-- Constant diagrams preserve flat-term K-flat complexes, with the actual normalized
cochain comparison, its derived form, and simultaneous naturality in both complexes.
The module comparison applies to every arrow, hence to both arrows of every exact sequence.

Source: Stacks Project, Cohomology on Sites, Tags 06YN, 06YS and 06YU, and
Modules on Sites, Tags 03DB, 03EL and 03ER; explicit diagram-evaluation argument
(blueprint: lem-sf-cbc-diagonal-resolving-complexes).

Proof:
1. Use lem-weil-pbc-diagram-site-realization. Evaluation is additive and exact.
Zero objects and exact sequences are detected componentwise, even for an empty J.
The homology comparison of lem-weil-pbc-exact-functor-complex-cohomology therefore
shows that acyclicity is detected by evaluation.
2. Construct arbitrary coproducts componentwise: the structure maps and the universal
map out of a coproduct are uniquely determined on its inclusions. Evaluation preserves
all these inclusions, including the infinite sum over r + s = n.
3. Apply lem-weil-pbc-algebraic-inverse-image-tensor-comparison to evaluation with its
identity algebraic presentation (def-weil-pbc-algebraic-inverse-image). Its comparison
sends pure sections to pure sections, using def-weil-pbc-ringed-tensor-section-calculus.
Specialize the second module to a constant diagram.
4. Sum these comparisons over r + s = n. Naturality identifies the two differential
terms d_A tensor 1 and (-1)^r 1 tensor d_P. Thus they give a cochain isomorphism for
the exact signed total of def-pc-tensor-complex-sheaves. Apply localization for the
derived comparison.
5. On each inclusion the naturality square is the module comparison square for a^r
and b^s. Equality on all coproduct inclusions proves simultaneous naturality. The
same module naturality identifies the evaluated tensor of every exact sequence.
6. Evaluate an arbitrary short exact sequence and tensor by each flat P^i. The module
comparison and detection of exactness imply that every constant term is flat, exactly
as in def-pc-flat-sheaf-modules.
7. For arbitrary acyclic A, exact evaluation makes e_j A acyclic. K-flatness of P
(def-pc-kflat-complex) makes its total tensor acyclic. The cochain comparison and
detection of acyclicity give acyclicity of the diagram total and K-flatness of Delta P.
No boundedness or constant coefficient-ring hypothesis was used; the same argument
works on any localized site and any extended complex satisfying the two assumptions. -/
theorem exists_diagonal_resolving_comparisons :
    ∃ (τ : ∀ (j : J)
        (M : ringedSiteModules.{u} (ringSheaf (coefficient (J := J) K R)))
        (Q : ringedSiteModules.{u} (ringSheaf R)),
        (evaluate K R j).obj
            (tensor _ (coefficient K R) M ((diagonal K R).obj Q)) ≅
          tensor K R ((evaluate K R j).obj M) Q)
      (e : ∀ (j : J)
        (A : CochainComplex (ringedSiteModules.{u}
          (ringSheaf (coefficient (J := J) K R))) ℤ)
        (P : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ),
        (evaluateComplex K R j).obj
            (totalTensor _ (coefficient K R) A ((diagonalComplex K R).obj P)) ≅
          totalTensor K R ((evaluateComplex K R j).obj A) P),
      (∀ (j : J) (M : ringedSiteModules.{u}
          (ringSheaf (coefficient (J := J) K R)))
        (Q : ringedSiteModules.{u} (ringSheaf R)) (U : Cᵒᵖ)
        (x : M.val.obj (op (op j, U.unop))) (q : Q.val.obj U),
        (τ j M Q).hom.val.app U
            (pure (coefficient K R) M ((diagonal K R).obj Q)
              (op (op j, U.unop)) x q) =
          pure R ((evaluate K R j).obj M) Q U x q) ∧
      (∀ (j : J) {M M' : ringedSiteModules.{u}
          (ringSheaf (coefficient (J := J) K R))}
        {Q Q' : ringedSiteModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : Q ⟶ Q'),
        (evaluate K R j).map
            (tensorMap _ (coefficient K R) f ((diagonal K R).map g)) ≫
              (τ j M' Q').hom =
          (τ j M Q).hom ≫ tensorMap K R ((evaluate K R j).map f) g) ∧
      (∀ (j : J)
        (A : CochainComplex (ringedSiteModules.{u}
          (ringSheaf (coefficient (J := J) K R))) ℤ)
        (P : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ)
        (r s n : ℤ) (h : r + s = n),
        (evaluate K R j).map
            (totalInclusion _ (coefficient K R) A ((diagonalComplex K R).obj P) r s n h) ≫
              (e j A P).hom.f n =
          (τ j (A.X r) (P.X s)).hom ≫
            totalInclusion K R ((evaluateComplex K R j).obj A) P r s n h) ∧
      (∀ (j : J)
        {A A' : CochainComplex (ringedSiteModules.{u}
          (ringSheaf (coefficient (J := J) K R))) ℤ}
        {P P' : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ}
        (a : A ⟶ A') (b : P ⟶ P'),
        (evaluateComplex K R j).map
            (totalTensorMap _ (coefficient K R) a ((diagonalComplex K R).map b)) ≫
              (e j A' P').hom =
          (e j A P).hom ≫ totalTensorMap K R ((evaluateComplex K R j).map a) b) ∧
      (∀ (P : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := R) (P.X i)) →
        CochainComplex.IsKFlatIndependentCoefficients (R := coefficient (J := J) K R)
          ((diagonalComplex K R).obj P) ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := coefficient (J := J) K R)
          (((diagonalComplex (J := J) K R).obj P).X i)) ∧
        (∀ (A : CochainComplex (ringedSiteModules.{u}
            (ringSheaf (coefficient (J := J) K R))) ℤ),
          A.Acyclic →
          (totalTensor _ (coefficient K R) A ((diagonalComplex K R).obj P)).Acyclic ∧
          ∀ j : J,
            ((evaluateComplex K R j).obj
              (totalTensor _ (coefficient K R) A ((diagonalComplex K R).obj P))).Acyclic ∧
            (totalTensor K R ((evaluateComplex K R j).obj A) P).Acyclic)) ∧
      (∀ (j : J)
        (A : CochainComplex (ringedSiteModules.{u}
          (ringSheaf (coefficient (J := J) K R))) ℤ)
        (P : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ),
        Nonempty ((derivedQ K R).obj ((evaluateComplex K R j).obj
            (totalTensor _ (coefficient K R) A ((diagonalComplex K R).obj P))) ≅
          (derivedQ K R).obj (totalTensor K R ((evaluateComplex K R j).obj A) P))) := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory (coefficient (J := J) K R)
  obtain ⟨τ, hτp, hτn⟩ := specialized_tensor (J := J) K R
  -- Regard tensor with a diagonal module as a bifunctor of the original variables.
  let F := curriedTensor (ringedSiteModules.{u} (ringSheaf (coefficient K R))) ⋙
    (Functor.whiskeringLeft _ _ _).obj (diagonal (J := J) K R)
  have : F.PreservesZeroMorphisms := by
    refine ⟨fun M N ↦ ?_⟩
    apply NatTrans.ext
    funext Q
    change (0 : M ⟶ N) ▷ ((diagonal K R).obj Q) = 0
    simp
  have : ∀ M, (F.obj M).PreservesZeroMorphisms := fun M ↦ by
    change ((diagonal K R) ⋙ tensorLeft
      (C := ringedSiteModules.{u} (ringSheaf (coefficient K R))) M).PreservesZeroMorphisms
    refine ⟨fun Q Q' ↦ ?_⟩
    change M ◁ (diagonal K R).map (0 : Q ⟶ Q') = 0
    rw [Functor.map_zero]
    simp
  let θ (j : J) : (Functor.postcompose₂.obj (evaluate K R j)).obj F ⟶
      (((Functor.whiskeringLeft₂ _).obj (evaluate K R j)).obj
        (𝟭 (ringedSiteModules.{u} (ringSheaf R)))).obj (curriedTensor _) :=
    { app M :=
        { app Q := (τ j M Q).hom
          naturality := by
            intro Q Q' g
            simpa [F] using hτn j (𝟙 M) g }
      naturality := by
        intro M M' f
        apply NatTrans.ext
        funext Q
        simpa [F] using hτn j f (𝟙 Q) }
  have hi (j : J) (M : ringedSiteModules.{u} (ringSheaf (coefficient K R)))
      (Q : ringedSiteModules.{u} (ringSheaf R)) : IsIso ((θ j).app M |>.app Q) :=
    inferInstanceAs (IsIso (τ j M Q).hom)
  -- The generic comparison retains the signed differential and every summand inclusion.
  let e := fun (j : J)
      (A : CochainComplex (ringedSiteModules.{u}
        (ringSheaf (coefficient (J := J) K R))) ℤ)
      (P : CochainComplex (ringedSiteModules.{u} (ringSheaf R)) ℤ) ↦ asIso
    (HomologicalComplex.mapBifunctorComparison (θ j) (ComplexShape.up ℤ) A P)
  refine ⟨τ, e, hτp, hτn, ?_, ?_, ?_, ?_⟩
  · intro j A P r s n h
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (θ j) (ComplexShape.up ℤ) A P r s n h
  · intro j A A' P P' a b
    exact HomologicalComplex.mapBifunctorComparison_naturality
      (θ j) (ComplexShape.up ℤ) a b
  · intro P hP hflat
    have ht (A : CochainComplex (ringedSiteModules.{u}
        (ringSheaf (coefficient (J := J) K R))) ℤ) (hA : A.Acyclic) (j : J) :
        (totalTensor K R ((evaluateComplex K R j).obj A) P).Acyclic :=
      hP _ ((evaluation_acyclic_iff K R A).1 hA j)
    have heval (A : CochainComplex (ringedSiteModules.{u}
        (ringSheaf (coefficient (J := J) K R))) ℤ) (hA : A.Acyclic) (j : J) :
        ((evaluateComplex K R j).obj (totalTensor _ (coefficient K R) A
          ((diagonalComplex K R).obj P))).Acyclic :=
      fun n ↦ (ht A hA j n).of_iso (e j A P).symm
    have htotal (A : CochainComplex (ringedSiteModules.{u}
        (ringSheaf (coefficient (J := J) K R))) ℤ) (hA : A.Acyclic) :
        (totalTensor _ (coefficient K R) A ((diagonalComplex K R).obj P)).Acyclic :=
      (evaluation_acyclic_iff K R _).2 (heval A hA)
    exact ⟨htotal, fun i ↦ diagonal_flat K R (P.X i) (hflat i),
      fun A hA ↦ ⟨htotal A hA, fun j ↦ ⟨heval A hA j, ht A hA j⟩⟩⟩
  · intro j A P
    exact ⟨(derivedQ K R).mapIso (e j A P)⟩

end CategoryTheory.DiagonalResolving
