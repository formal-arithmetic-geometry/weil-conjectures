/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Module.FiniteDimension

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Topology.ContinuousMapCondensedRing
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.CategoryTheory.SheafTensor

/-! # Continuous profinite functions and ordinary derived internal Hom

Source: main-20261015 six-functors direct-images proof, paragraph (3), finite complete
coefficient branch; Bhatt--Scholze, The pro-etale topology for schemes, Lemma 4.3.9.
(blueprint: lem-sfb-normed-scalar-profinite-hom-acyclic).

The internal function object is the actual tensor right adjoint on the actual free
module. Its evaluation on S is constructed on S x P, using the universal generator
and the tensor-Hom counit. The assertion identifies this object with all continuous
functions and states invertibility of its canonical ordinary resolution comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction

namespace Profinite.NormedScalarHom

variable (F : Type u) [TopologicalSpace F] [CommRing F] [IsTopologicalRing F]

/-- The actual internal Hom from the recorded free module A_F[P].
Source: Stacks 03EO and the free-generator calculation in the node, step 2
(blueprint: lem-sfb-normed-scalar-profinite-hom-acyclic). -/
abbrev homFunctor (P : Profinite.{u}) :
    Modules (continuousScalarRing F) ⥤ Modules (continuousScalarRing F) :=
  Mod.ihom (freeParameter (continuousScalarRing F) P)

/-- The universal generator associated to a continuous map S to P, from the unit
of the existing free-forgetful adjunction.
Source: node proof, step 2 (blueprint: lem-sfb-normed-scalar-profinite-hom-acyclic). -/
def generator (P S : Profinite.{u}) (g : S ⟶ P) :
    sections (continuousScalarRing F) (freeParameter (continuousScalarRing F) P) S :=
  (((InternalBar.freeAdjunction (continuousScalarRing F).toMon).unit.app
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj P)).hom.app
      (op S)) (ULift.up g)

/-- Evaluation is the tensor-Hom counit on the tautological generator over S x P.
The section x is restricted along the first projection. The result is already a
continuous function, since the regular coefficient sheaf has all-continuous sections.
Source: node proof, step 2 (blueprint: lem-sfb-normed-scalar-profinite-hom-acyclic). -/
def evaluation (P S : Profinite.{u})
    (x : sections (continuousScalarRing F)
      ((homFunctor F P).obj (Mod.regular (continuousScalarRing F).X)) S) : C(S × P, F) :=
  (((colimit.ι ((Mod.tensorLeftDiagram (continuousScalarRing F).X
      (freeParameter (continuousScalarRing F) P)).flip.obj
        ((homFunctor F P).obj (Mod.regular (continuousScalarRing F).X)))
      WalkingParallelPair.one ≫
    (Mod.ihomAdjunction (freeParameter (continuousScalarRing F) P)).counit.app
      (Mod.regular (continuousScalarRing F).X)).hom.hom.app (op (Profinite.of (S × P))))
    (((Functor.LaxMonoidal.μ
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
      ((homFunctor F P).obj (Mod.regular (continuousScalarRing F).X)).X
      (freeParameter (continuousScalarRing F) P).X).app (op (Profinite.of (S × P))))
        (TensorProduct.tmul ℤ
          (((homFunctor F P).obj (Mod.regular (continuousScalarRing F).X)).X.obj.map
            (CompHausLike.ofHom _ (ContinuousMap.fst : C(S × P, S))).op x)
          (generator F P (Profinite.of (S × P))
            (CompHausLike.ofHom _ (ContinuousMap.snd : C(S × P, P))))))).down

/-- Contravariance in a continuous parameter map is precomposition with its free
module map, using the recorded tensor-adjunction mate, not an unspecified map.
Source: node proof, steps 2 and 5
(blueprint: lem-sfb-normed-scalar-profinite-hom-acyclic). -/
def parameterMap {P P' : Profinite.{u}} (v : P' ⟶ P) :
    homFunctor F P ⟶ homFunctor F P' :=
  Mod.ihomMap ((InternalBar.free (continuousScalarRing F).toMon).map
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).map v))

/-- The comparison before localization, on any nonnegative injective resolution:
apply the internal-Hom functor to the resolution augmentation.
Source: node proof, step 2, Stacks 08J7
(blueprint: lem-sfb-normed-scalar-profinite-hom-acyclic). -/
def resolutionAugmentation (P : Profinite.{u})
    (I : InjectiveResolution (Mod.regular (continuousScalarRing F).X)) :
    (CochainComplex.single₀ (Modules (continuousScalarRing F))).obj
        ((homFunctor F P).obj (Mod.regular (continuousScalarRing F).X)) ⟶
      ((homFunctor F P).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  (HomologicalComplex.singleMapHomologicalComplex (homFunctor F P) (.up ℕ) 0).inv.app
      (Mod.regular (continuousScalarRing F).X) ≫
    ((homFunctor F P).mapHomologicalComplex (.up ℕ)).map I.ι

end Profinite.NormedScalarHom

namespace Profinite.NormedScalarHom

variable (F : Type u) [TopologicalSpace F] [CommRing F] [IsTopologicalRing F]

/-- The full comparison, including all-continuous evaluation, the S-coordinate scalar
action, both restriction laws, the specified derived unit, its nonnegative resolution
model, parameter naturality before localization, and its canonical degree-zero map.
The standard unbounded localization is taken in the larger universe.
Source: node statement and proof, steps 2 and 5, Stacks 08J7
(blueprint: lem-sfb-normed-scalar-profinite-hom-acyclic). -/
def Assertion : Prop := by
  letI : HasDerivedCategory.{u + 2} (Modules (continuousScalarRing F)) :=
    HasDerivedCategory.standard (Modules (continuousScalarRing F))
  letI (P : Profinite.{u}) : PreservesLimits (homFunctor F P) :=
    (Mod.ihomAdjunction (freeParameter (continuousScalarRing F) P)).rightAdjoint_preservesLimits
  exact
    (∀ P S : Profinite.{u}, Function.Bijective (evaluation F P S)) ∧
    (∀ (P S : Profinite.{u}) (x y),
      evaluation F P S (x + y) = evaluation F P S x + evaluation F P S y) ∧
    (∀ (P S : Profinite.{u}) (r : sectionRing (continuousScalarRing F) S) (x)
      (s : S) (p : P),
      evaluation F P S (r • x) (s, p) = r.down s * evaluation F P S x (s, p)) ∧
    (∀ (P S S' : Profinite.{u}) (v : S' ⟶ S) (x) (s : S') (p : P),
      evaluation F P S'
        (((homFunctor F P).obj (Mod.regular (continuousScalarRing F).X)).X.obj.map v.op x)
        (s, p) = evaluation F P S x (v s, p)) ∧
    (∀ (P P' : Profinite.{u}) (v : P' ⟶ P) (S : Profinite.{u}) (x) (s : S) (p : P'),
      evaluation F P' S
        (((parameterMap F v).app (Mod.regular (continuousScalarRing F).X)).hom.hom.app
          (op S) x) (s, p) = evaluation F P S x (s, v p)) ∧
    (∀ P : Profinite.{u},
      IsIso ((homFunctor F P).rightDerivedSingleUnit
        (Mod.regular (continuousScalarRing F).X))) ∧
    (∀ (P : Profinite.{u})
      (I : InjectiveResolution (Mod.regular (continuousScalarRing F).X)),
      IsIso (DerivedCategory.Q.{u + 2}.map
        (HomologicalComplex.extendMap (resolutionAugmentation F P I)
          ComplexShape.embeddingUpNat))) ∧
    (∀ (P P' : Profinite.{u}) (v : P' ⟶ P)
      (I : InjectiveResolution (Mod.regular (continuousScalarRing F).X)),
      resolutionAugmentation F P I ≫
        (NatTrans.mapHomologicalComplex (parameterMap F v) (.up ℕ)).app I.cocomplex =
      (CochainComplex.single₀ (Modules (continuousScalarRing F))).map
        ((parameterMap F v).app (Mod.regular (continuousScalarRing F).X)) ≫
          resolutionAugmentation F P' I) ∧
    (∀ P : Profinite.{u},
      (DerivedCategory.homologyFunctor (Modules (continuousScalarRing F)) 0).map
          ((homFunctor F P).rightDerivedSingleUnit
            (Mod.regular (continuousScalarRing F).X)) ≫
        ((homFunctor F P).homologyRightDerivedFunctorObjSingleFunctorIso
            (Mod.regular (continuousScalarRing F).X) 0 ≪≫
          (homFunctor F P).rightDerivedZeroIsoSelf.app
            (Mod.regular (continuousScalarRing F).X)).hom =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Modules (continuousScalarRing F)) 0).hom.app
          ((homFunctor F P).obj (Mod.regular (continuousScalarRing F).X)))

/-- For every finite norm-topological extension E of Q_ell, ordinary continuous
functions compute derived internal functions of every profinite parameter set.
Source: main-20261015 direct-images proof, paragraph (3), finite E analytic input;
Bhatt--Scholze, The pro-etale topology for schemes, Lemma 4.3.9(2)--(4).
(blueprint: lem-sfb-normed-scalar-profinite-hom-acyclic).

Proof:
1. Transport internal modules to sectionwise module sheaves by
   def-weil-pbc-internal-abelian-sheaf-module-equivalence. The equivalence is exact
   and preserves tensor by lem-pe-internal-section-tensor-comparison. The closed
   tensor of lem-pc-sheaf-modules-tensor-closed identifies its right adjoint with
   def-pur-sheaf-hom. The sheaf category is Grothendieck by
   lem-weil-pbc-sheaf-tensor-closed, and its module category by
   lem-sfb-modobj-grothendieck. Apply lem-sp-grothendieck-enough-injectives and take
   any nonnegative resolution A to I. Exact equivalences preserve injectives.
2. On the slice over S, a map from A[P] is uniquely determined by its universal
   generator, which is a section over S x P. Conversely pull that section back
   along (U to S, U to P) and extend A-linearly. These mutually inverse operations
   give precisely evaluation above. Thus internal Hom applied to I has sections
   I^n(S x P), and resolutionAugmentation is the original resolution inclusion.
3. For each finite jointly surjective cover, replace the cover by its disjoint
   union. Its fibre powers are the finite disjoint unions of the fibre products
   indexed by tuples. Continuous functions on these disjoint unions are the
   products of continuous function groups. Under this identification the analytic
   input lem-sfb-normed-scalar-profinite-cech-exact is exactness of the positive
   Cech complex of def-weil-pbc-site-cech-complex. Completeness of E is used here;
   it also follows from finite dimensionality over the complete field Q_ell.
4. Apply lem-weil-pbc-site-cech-vanishing-criterion with all profinite objects and
   all defining finite covering families. Fibre products stay profinite, these
   families are cofinal in covering sieves, and step 3 supplies Cech vanishing.
   The arbitrary-ring comparison
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison then identifies
   the evaluated module resolution cohomology with this zero abelian-sheaf
   cohomology. Degree zero is A(S x P).
5. The augmentation is therefore a quasi-isomorphism on every section complex,
   hence on the sheaf complexes. Derived localization makes the specified map
   invertible; the ordinary right-derived resolution comparison identifies it
   with rightDerivedSingleUnit. For v:P' to P the chain map is restriction along
   1_S x v. Free-generator evaluation identifies it with parameterMap, so the
   naturality square commutes already before localization. On zeroth cohomology
   the ordinary unit is the identity under its canonical left-exact comparison.
   Evaluation carries it to the stated all-continuous identification. Empty
   parameters and empty test objects give the zero function group; a singleton
   parameter gives the identity. No locally constant restriction is introduced.
-/
theorem normed_scalar_profinite_hom_acyclic (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E] :
    CompleteSpace E ∧ Assertion E := by
  sorry

end Profinite.NormedScalarHom
