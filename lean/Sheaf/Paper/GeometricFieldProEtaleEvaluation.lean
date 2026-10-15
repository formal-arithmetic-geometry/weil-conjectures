/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Sheaf.RingTheory.WeaklyEtaleField

/-!
# Pro-etale evaluation over an algebraically closed field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Examples 4.1.10 and 4.2.11
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Continuity of the relative test-object functor, by composition of the published
continuous functors. Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable instance geometricFieldTest_isContinuous (X : Scheme.{u}) :
    (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology X) :=
  Functor.isContinuous_comp profiniteToProEt (Scheme.proEtaleBaseChange (toSpecZ X))
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
    (Scheme.ProEt.topology X)

/-- Restriction along the specified relative profinite test objects, on objects and
arrows. Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable abbrev geometricFieldRestriction (X : Scheme.{u})
    (D : Type v) [Category.{u + 1} D] :=
  (profiniteToProEtOf X).sheafPushforwardContinuous D
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X)

/-- The canonical structural map from the singleton test object to the final scheme.
Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable def geometricFieldTestFinalMap (X : Scheme.{u}) :
    (profiniteToProEtOf X).obj (Profinite.of (ULift.{u, 0} PUnit.{1})) ⟶
      Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk
    (((profiniteToProEtOf X).obj (Profinite.of (ULift.{u, 0} PUnit.{1}))).hom)

/-- The point adjunction, with restriction as its actual right adjoint.
Source: Bhatt--Scholze, Example 4.2.11
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable def geometricFieldPointAdjunction (X : Scheme.{u}) :
    profinitePointSetSchemeInverseImage X ⊣ geometricFieldRestriction X (Type (u + 1)) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
      (Scheme.proEtaleSheafAdjunction (toSpecZ X) (Type (u + 1)))

/-- The same specified adjunction for abelian sheaves.
Source: Bhatt--Scholze, Example 4.2.11
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable def geometricFieldAbelianPointAdjunction (X : Scheme.{u}) :
    upperStarFromPoint X ⊣ geometricFieldRestriction X Ab.{u + 1} :=
  pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- Canonical base change of relative profinite test objects, fixed by the fibre-product
composition comparison. Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable def geometricFieldTestBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    profiniteToProEtOf Y ⋙ Scheme.proEtaleBaseChange f ≅ profiniteToProEtOf X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft profiniteToProEt
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
      f (toSpecZ Y) (toSpecZ X) (comp_toSpecZ f).symm).symm

/-- The canonical comparison from restriction to restriction after inverse image:
apply the adjunction unit and then the specified test-object base-change isomorphism.
Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable def geometricFieldRestrictionComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D] :
    geometricFieldRestriction Y D ⟶
      Scheme.proEtaleSheafInverseImage f D ⋙ geometricFieldRestriction X D :=
  Functor.whiskerRight (Scheme.proEtaleSheafAdjunction f D).unit
    (geometricFieldRestriction Y D) ≫
  Functor.whiskerLeft (Scheme.proEtaleSheafInverseImage f D)
    (Functor.sheafPushforwardContinuousComp'
      (eFG := geometricFieldTestBaseChange f) D
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)).hom

/-- The canonical evaluation comparison, not an unrelated isomorphism: the scheme
adjunction unit followed by restriction along the final-object base-change isomorphism.
It is defined for any coefficient category for which inverse image exists, hence its
components for rings are ring maps. Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable def geometricFieldEvaluationComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D] :
    (sheafSections (Scheme.ProEt.topology Y) D).obj (op (Scheme.ProEt.mk (𝟙 Y))) ⟶
      Scheme.proEtaleSheafInverseImage f D ⋙
        (sheafSections (Scheme.ProEt.topology X) D).obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  Functor.whiskerRight (Scheme.proEtaleSheafAdjunction f D).unit
    ((sheafSections (Scheme.ProEt.topology Y) D).obj (op (Scheme.ProEt.mk (𝟙 Y)))) ≫
  Functor.whiskerLeft (Scheme.proEtaleSheafInverseImage f D)
    ((sheafSections (Scheme.ProEt.topology X) D).mapIso
      (MorphismProperty.Over.isoMk
        (asIso (pullback.snd (𝟙 Y) f)) (Category.comp_id _)).op).inv

/-- Composition of arbitrary coefficient inverse images, obtained by conjugating the
canonical fibre-product comparison of direct images.
Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable def geometricFieldInverseImageComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D]
    [HasWeakSheafify (Scheme.ProEt.topology Y) D] :
    Scheme.proEtaleSheafInverseImage (f ≫ g) D ≅
      Scheme.proEtaleSheafInverseImage g D ⋙ Scheme.proEtaleSheafInverseImage f D :=
  ((conjugateIsoEquiv (Scheme.proEtaleSheafAdjunction (f ≫ g) D)
    ((Scheme.proEtaleSheafAdjunction g D).comp
      (Scheme.proEtaleSheafAdjunction f D))).symm
    (Functor.sheafPushforwardContinuousComp'
      (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm)
      D (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)).symm).symm

/-- The identity inverse-image comparison, as the adjunction conjugate of the canonical
identity direct-image comparison. Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable def geometricFieldInverseImageIdentity (X : Scheme.{u})
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D] :
    Scheme.proEtaleSheafInverseImage (𝟙 X) D ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (Scheme.proEtaleSheafAdjunction (𝟙 X) D)).symm
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X)
      D (Scheme.ProEt.topology X)).symm

/-- Restriction of modules uses the same profinite test objects and the identity scalar
map, so it is restriction of both the sections and their ring action.
Source: Bhatt--Scholze, Example 4.2.11
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation). -/
noncomputable abbrev geometricFieldModuleRestriction (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :=
  SheafOfModules.pushforward.{u + 1} (F := profiniteToProEtOf X)
    (J := coherentTopology Profinite.{u}) (K := Scheme.ProEt.topology X)
    (R := R) (𝟙 ((geometricFieldRestriction X RingCat.{u + 1}).obj R))

/-- Over an algebraically closed field, the specified restriction is the profinite-site
identification, its left adjoint is the specified point inverse image, and evaluation
at the scheme is evaluation at the singleton. This includes ring and module structures.

Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation).

Proof: (1) On the ind-etale affine basis, finitely generated subalgebras are finite etale
and therefore finite products of K; coordinate idempotents identify their maps with maps
of finite sets. Treat the zero algebra separately. (2) Take the inverse limit of the finite
sets. Compactness and the finite intersection property give surjective projections.
Locally constant function factorization identifies the algebra with LC(S,K), and Spec
turns its filtered colimit into the test scheme. (3) Evaluation at each point identifies
all algebra maps with precomposition, proving full faithfulness. The induced topology is
finite joint surjectivity, so dense-subsite comparison gives the restriction equivalence.
(4) The finite-partition tensor formula identifies K tensor LC(S,Z) with LC(S,K).
The right adjoint of the specified point inverse image is therefore exactly restriction.
Adjoint uniqueness identifies the left adjoint with its inverse. Restriction preserves
operations and their equations, giving the ring and module versions. The singleton test
scheme is terminal, giving the evaluation identification. -/
theorem geometric_field_proetale_evaluation (K : Type u) [Field K] [IsAlgClosed K] :
    (geometricFieldRestriction (Spec (.of K)) (Type (u + 1))).IsEquivalence ∧
    (geometricFieldRestriction (Spec (.of K)) Ab.{u + 1}).IsEquivalence ∧
    (geometricFieldRestriction (Spec (.of K)) RingCat.{u + 1}).IsEquivalence ∧
    IsIso (geometricFieldPointAdjunction (Spec (.of K))).unit ∧
    IsIso (geometricFieldPointAdjunction (Spec (.of K))).counit ∧
    IsIso (geometricFieldAbelianPointAdjunction (Spec (.of K))).unit ∧
    IsIso (geometricFieldAbelianPointAdjunction (Spec (.of K))).counit ∧
    IsIso (geometricFieldTestFinalMap (Spec (.of K))) ∧
    (∀ R : Sheaf (Scheme.ProEt.topology (Spec (.of K))) RingCat.{u + 1},
      (geometricFieldModuleRestriction (Spec (.of K)) R).IsEquivalence) := by
  sorry

/-- Covers of the final object split through a member; abelian evaluation is exact,
and evaluation of arbitrary ring-sheaf modules preserves cokernels and finite free modules.
The latter are the colimits of finite families of copies of the coefficient sheaf.

Source: Bhatt--Scholze, Example 4.1.10; Stacks Project, Tag 03CN
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation).

Proof: (5) Refine a cover by finitely many profinite test objects. One of their profinite
sets is nonempty, and a point supplies a section through that member of the original
cover. (6) Epimorphisms are locally surjective; restrict a local lift along that section
to lift any global section. Kernels are sectionwise, proving exactness. Forgetting module
actions creates kernels and cokernels, so module evaluation preserves cokernels.
The finite free module is the finite product of copies of the ring, including rank zero;
evaluation preserves its coordinate injections, projections and biproduct identities. -/
theorem geometric_field_proetale_evaluation_exact (K : Type u) [Field K] [IsAlgClosed K] :
    (∀ (S : Presieve (Scheme.ProEt.mk (𝟙 (Spec (.of K))))),
      Sieve.generate S ∈ Scheme.ProEt.topology (Spec (.of K)) _ →
      ∃ (U : (Spec (.of K)).ProEt)
        (f : U ⟶ Scheme.ProEt.mk (𝟙 (Spec (.of K))))
        (s : Scheme.ProEt.mk (𝟙 (Spec (.of K))) ⟶ U), S f ∧ s ≫ f = 𝟙 _) ∧
    PreservesFiniteLimits
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) ∧
    PreservesFiniteColimits
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) ∧
    (∀ (R : Sheaf (Scheme.ProEt.topology (Spec (.of K))) RingCat.{u + 1}),
      PreservesColimitsOfShape WalkingParallelPair
        (SheafOfModules.evaluation.{u + 1} R
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) ∧
      ∀ n : ℕ, PreservesColimit
        (Discrete.functor (fun _ : Fin n ↦ SheafOfModules.unit R))
        (SheafOfModules.evaluation.{u + 1} R
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K))))))) := by
  sorry

/-- Algebraically closed extensions induce the identity under the specified profinite
identifications and preserve evaluation by the canonical unit-normalized comparisons.
This includes arbitrary, nonalgebraic extensions and identities. Ring components are
ring homomorphisms, and the restriction comparison for modules respects their action.

Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation).

Proof: (7) On each finite clopen partition, the scalar extension comparison sends
k' tensor b to the function s ↦ k' b(s), with inverse the sum of value tensors times
characteristic functions. Refinement leaves this inverse unchanged. Thus base change
identifies the test objects naturally; their direct-image restrictions agree. Conjugating
this comparison gives exactly the unit-normalized inverse-image comparison above.
At the singleton this gives the displayed evaluation comparison. (8) On a common
partition two successive scalar extensions both send k'' tensor k' tensor b to
s ↦ k'' k' b(s); identity is equally direct. Adjoint uniqueness transports these equations
to inverse images. Naturality with respect to each ring operation and module action
makes the comparisons compatible with those operations and equations. -/
theorem geometric_field_proetale_evaluation_extension
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K'] (i : K →+* K') :
    IsIso (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i))
      (Type (u + 1))) ∧
    IsIso (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i))
      Ab.{u + 1}) ∧
    IsIso (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i))
      RingCat.{u + 1}) ∧
    IsIso (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
      (Type (u + 1))) ∧
    IsIso (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
      Ab.{u + 1}) ∧
    IsIso (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
      RingCat.{u + 1}) := by
  sorry

/-- The evaluation and restriction comparisons have the same singleton component and
respect composition. This formulation is uniform in the coefficient category, so the
same equations hold for sets, abelian groups and rings, and for their operation maps.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation).

Proof: (8) The singleton base-change isomorphism commutes with the structural maps to
terminal objects, proving the evaluation square. On finite clopen partitions the two
iterated scalar-extension maps are both multiplication on the scalar factors. The
fibre-product composition maps therefore commute. Conjugation under the given
adjunctions gives the displayed composition equations, with their specified units.
No choice of an unrelated equivalence or comparison is involved. -/
theorem geometric_field_proetale_evaluation_coherence
    (K K' K'' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    [Field K''] [IsAlgClosed K''] (i : K →+* K') (j : K' →+* K'')
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology (Spec (.of K))) D]
    [HasWeakSheafify (Scheme.ProEt.topology (Spec (.of K'))) D]
    [HasWeakSheafify (Scheme.ProEt.topology (Spec (.of K''))) D] :
    (∀ F : Sheaf (Scheme.ProEt.topology (Spec (.of K))) D,
      F.obj.map (geometricFieldTestFinalMap (Spec (.of K))).op ≫
          ((geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i)) D).app F).hom.app
            (op (Profinite.of (ULift.{u, 0} PUnit.{1}))) =
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) D).app F ≫
          ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) D).obj F).obj.map
            (geometricFieldTestFinalMap (Spec (.of K'))).op) ∧
    (∀ F : Sheaf (Scheme.ProEt.topology (Spec (.of K))) D,
      (geometricFieldEvaluationComparison
        (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom i)) D).app F =
      (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) D).app F ≫
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom j)) D).app
          ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) D).obj F) ≫
        ((sheafSections (Scheme.ProEt.topology (Spec (.of K''))) D).obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K'')))))).map
            ((geometricFieldInverseImageComp (Spec.map (CommRingCat.ofHom j))
              (Spec.map (CommRingCat.ofHom i)) D).inv.app F)) ∧
    (∀ F : Sheaf (Scheme.ProEt.topology (Spec (.of K))) D,
      (geometricFieldRestrictionComparison
        (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom i)) D).app F =
      (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i)) D).app F ≫
        (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom j)) D).app
          ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) D).obj F) ≫
        (geometricFieldRestriction (Spec (.of K'')) D).map
          ((geometricFieldInverseImageComp (Spec.map (CommRingCat.ofHom j))
            (Spec.map (CommRingCat.ofHom i)) D).inv.app F)) := by
  sorry

/-- Identity compatibility, including the actual inverse-image identity comparison.
Source: Bhatt--Scholze, Example 4.1.10
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation).

Proof: (8) Base change along the identity has its canonical projection to the original
test object. The unit triangle identity makes its conjugate the identity inverse-image
comparison. Evaluate at the singleton for the first equation; retain every test object
for the second. -/
theorem geometric_field_proetale_evaluation_identity
    (K : Type u) [Field K] [IsAlgClosed K]
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology (Spec (.of K))) D]
    (F : Sheaf (Scheme.ProEt.topology (Spec (.of K))) D) :
    (geometricFieldEvaluationComparison (𝟙 (Spec (.of K))) D).app F ≫
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) D).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).map
          ((geometricFieldInverseImageIdentity (Spec (.of K)) D).hom.app F) = 𝟙 _ ∧
    (geometricFieldRestrictionComparison (𝟙 (Spec (.of K))) D).app F ≫
      (geometricFieldRestriction (Spec (.of K)) D).map
        ((geometricFieldInverseImageIdentity (Spec (.of K)) D).hom.app F) = 𝟙 _ := by
  sorry

/-- Compatibility with every finite-arity operation on sheaves of sets. In particular,
apply this to addition, multiplication, units and an arbitrary ring-sheaf module action.
The inverse-image operation is its image under the specified scheme inverse image;
the product comparisons specify the product identification rather than choosing one.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11
(blueprint: lem-weil-pbc-geometric-field-proetale-evaluation).

Proof: (8) The restriction comparison is natural at all operation morphisms, since it
is built from an adjunction unit and a test-object isomorphism. Inverse image preserves
finite products. The naturality equations for product projections identify the comparison
on a finite product with the product of its components; naturality at the operation
then gives the equation. The empty family is the nullary case and includes zero and one.
The same equations apply to the action R times M to M, without requiring commutativity
or a nonzero ring. Thus the evaluation comparison is linear over its coefficient-ring
comparison for every ring-sheaf module, not only constant coefficient modules. -/
theorem geometric_field_proetale_evaluation_operations
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K') (I : Type u) [Finite I]
    (F : I → Sheaf (Scheme.ProEt.topology (Spec (.of K))) (Type (u + 1)))
    (H : Sheaf (Scheme.ProEt.topology (Spec (.of K))) (Type (u + 1)))
    (a : (∏ᶜ F) ⟶ H) :
    PreservesFiniteProducts
      (Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) (Type (u + 1))) ∧
    ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) (Type (u + 1))).obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).map a ≫
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
          (Type (u + 1))).app H =
      (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
        (Type (u + 1))).app (∏ᶜ F) ≫
        ((sheafSections (Scheme.ProEt.topology (Spec (.of K'))) (Type (u + 1))).obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K')))))).map
            ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i))
              (Type (u + 1))).map a) ∧
    (∀ k : I,
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) (Type (u + 1))).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).map (Pi.π F k) ≫
          (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
            (Type (u + 1))).app (F k) =
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
          (Type (u + 1))).app (∏ᶜ F) ≫
          ((sheafSections (Scheme.ProEt.topology (Spec (.of K'))) (Type (u + 1))).obj
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of K')))))).map
              ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i))
                (Type (u + 1))).map (Pi.π F k))) := by
  sorry

end AlgebraicGeometry.ProEtale
