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
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Sites.Abelian
import Sheaf.CategoryTheory.ProfiniteActualFreeHomEvaluation
import Sheaf.Topology.FiniteNormedScalarSectionAcyclicity

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

private theorem single_unit_isIso_of_resolution
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [Abelian.HasKInjectiveResolutions C]
    (G : C ⥤ D) [G.Additive] (M : C) (I : InjectiveResolution M)
    (hi : QuasiIso ((G.mapHomologicalComplex (.up ℕ)).map I.ι)) :
    IsIso (G.rightDerivedSingleUnit M) := by
  have hext : (G.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat) =
      (HomologicalComplex.mapExtendIso _ ComplexShape.embeddingUpNat G).hom ≫
        HomologicalComplex.extendMap ((G.mapHomologicalComplex (.up ℕ)).map I.ι)
          ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapExtendIso _ ComplexShape.embeddingUpNat G).inv := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
      ← HomologicalComplex.mapExtensIso_hom_f_naturality_assoc]
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    exact (Category.comp_id _).symm
  have : QuasiIso (HomologicalComplex.extendMap
      ((G.mapHomologicalComplex (.up ℕ)).map I.ι) ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 hi
  have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map I.ι') := by
    erw [InjectiveResolution.ι', Functor.map_comp, hext]
    infer_instance
  have : IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map I.ι')) :=
    inferInstance
  have hF : IsIso ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient C (.up ℤ)).map I.ι')) := by
    dsimp only [Functor.comp_map]
    rw [Functor.mapHomotopyCategory_map]
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso D) _).2 inferInstance
  have hq : IsIso ((DerivedCategory.Qh ⋙ G.rightDerivedFunctor).map
      ((HomotopyCategory.quotient C (.up ℤ)).map I.ι')) := by
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (.up ℤ)).map I.ι')) :=
      (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) _).2 inferInstance
    change IsIso (G.rightDerivedFunctor.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (.up ℤ)).map I.ι')))
    infer_instance
  have : I.cochainComplex.IsKInjective := by
    change CochainComplex.IsKInjective (I.cocomplex.extend ComplexShape.embeddingUpNat)
    infer_instance
  have hu : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I.cochainComplex)) := inferInstance
  have hn := G.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map I.ι')
  have hleft : IsIso
      ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
        ((HomotopyCategory.quotient C (.up ℤ)).map I.ι') ≫
      G.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj I.cochainComplex)) := by
    infer_instance
  rw [hn] at hleft
  have : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj M))) :=
    IsIso.of_isIso_comp_right _
      ((DerivedCategory.Qh ⋙ G.rightDerivedFunctor).map
        ((HomotopyCategory.quotient C (.up ℤ)).map I.ι'))
  unfold Functor.rightDerivedSingleUnit
  infer_instance

private theorem quasiIso_of_sections {A : Ring.{u}}
    {K L : CochainComplex (Modules A) ℕ} (f : K ⟶ L)
    (h : ∀ S : Profinite.{u},
      QuasiIso (((ProfiniteHom.eval A S).mapHomologicalComplex (.up ℕ)).map f)) :
    QuasiIso f := by
  let U : Modules A ⥤ Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
    Mod.forget A.X
  let P := sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}
  let T := presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}
  have hp : QuasiIso (((U ⋙ P).mapHomologicalComplex (.up ℕ)).map f) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro S
    exact h S.unop
  have ht : QuasiIso (((U ⋙ P ⋙ T).mapHomologicalComplex (.up ℕ)).map f) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      (((U ⋙ P).mapHomologicalComplex (.up ℕ)).map f) T
  let e := NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft U
    (sheafificationNatIso (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})) (.up ℕ)
  have hu : QuasiIso ((U.mapHomologicalComplex (.up ℕ)).map f) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoOfNatIso e (Arrow.mk f))).2 ht
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f U).1 hu

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
  have hc : CompleteSpace E := FiniteDimensional.complete ℚ_[ell] E
  refine ⟨hc, ?_⟩
  let : HasDerivedCategory.{u + 2} (Modules (continuousScalarRing E)) :=
    HasDerivedCategory.standard (Modules (continuousScalarRing E))
  let (P : Profinite.{u}) : PreservesLimits (homFunctor E P) :=
    (Mod.ihomAdjunction (freeParameter (continuousScalarRing E) P)).rightAdjoint_preservesLimits
  obtain ⟨ev⟩ := ProfiniteHom.actual_free_hom_evaluation (continuousScalarRing E)
    (Classical.choice (ProfiniteHom.exists_evaluation (continuousScalarRing E)))
  have he (P S : Profinite.{u}) (x) :
      evaluation E P S x =
        ((ev.evaluate P S).hom.app (Mod.regular (continuousScalarRing E).X) x).down := by
    rw [ev.tautological]
    rfl
  have hs := (Profinite.finiteNormedScalar_section_acyclicity ell E).2.2.2
  have hsection (I : InjectiveResolution (Mod.regular (continuousScalarRing E).X))
      (V : Profinite.{u}) :
      QuasiIso (((ProfiniteHom.eval (continuousScalarRing E) V).mapHomologicalComplex
        (.up ℕ)).map I.ι) := by
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    cases q with
    | zero => exact (hs I V).2.2.2.1
    | succ q =>
        have hz := HomologicalComplex.isZero_single_obj_homology
          (.up ℕ) 0 ((ProfiniteHom.eval (continuousScalarRing E) V).obj
            (Mod.regular (continuousScalarRing E).X)) (q + 1) (Nat.succ_ne_zero q)
        let e := (HomologicalComplex.singleMapHomologicalComplex
          (ProfiniteHom.eval (continuousScalarRing E) V) (.up ℕ) 0).app
            (Mod.regular (continuousScalarRing E).X)
        exact (hz.of_iso ((HomologicalComplex.homologyFunctor _ (.up ℕ)
          (q + 1)).mapIso e)).isIso ((hs I V).2.2.2.2 (q + 1) (Nat.zero_lt_succ q)) _
  have haug (P : Profinite.{u})
      (I : InjectiveResolution (Mod.regular (continuousScalarRing E).X)) :
      QuasiIso (resolutionAugmentation E P I) := by
    apply quasiIso_of_sections
    intro S
    have hi : QuasiIso
        (((homFunctor E P ⋙ ProfiniteHom.eval (continuousScalarRing E) S).mapHomologicalComplex
          (.up ℕ)).map I.ι) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex (ev.evaluate P S) (.up ℕ))
          (Arrow.mk I.ι))).2 (hsection I (Profinite.of (S × P)))
    dsimp only [resolutionAugmentation]
    rw [Functor.map_comp]
    let t := (HomologicalComplex.singleMapHomologicalComplex
      (homFunctor E P) (.up ℕ) 0).app (Mod.regular (continuousScalarRing E).X)
    have ht : IsIso (((ProfiniteHom.eval (continuousScalarRing E) S).mapHomologicalComplex
        (.up ℕ)).map t.inv) := inferInstance
    change QuasiIso
      (((ProfiniteHom.eval (continuousScalarRing E) S).mapHomologicalComplex (.up ℕ)).map
          t.inv ≫
        ((ProfiniteHom.eval (continuousScalarRing E) S).mapHomologicalComplex (.up ℕ)).map
          (((homFunctor E P).mapHomologicalComplex (.up ℕ)).map I.ι))
    have : QuasiIso
        (((ProfiniteHom.eval (continuousScalarRing E) S).mapHomologicalComplex (.up ℕ)).map
          t.inv) := quasiIso_of_isIso _
    exact (quasiIso_iff_comp_left _ _).2 hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P S
    have hb := ConcreteCategory.bijective_of_isIso
      ((ev.evaluate P S).hom.app (Mod.regular (continuousScalarRing E).X))
    rw [show evaluation E P S = fun x ↦
      ((ev.evaluate P S).hom.app (Mod.regular (continuousScalarRing E).X) x).down from
        funext (he P S)]
    exact (Equiv.ulift : ULift.{u + 1} C(S × P, E) ≃ C(S × P, E)).bijective.comp hb
  · intro P S x y
    simp only [he, map_add]
    rfl
  · intro P S r x s p
    simp only [he, ev.scalar]
    let a := (InternalAbelianSheafModule.sectionRingSheaf
      (coherentTopology Profinite.{u}) (continuousScalarRing E).X).obj.map
        (CompHausLike.ofHom _ (ContinuousMap.fst : C(S × P, S))).op r
    let y : sections (continuousScalarRing E) (Mod.regular (continuousScalarRing E).X)
        (Profinite.of (S × P)) :=
      (ev.evaluate P S).hom.app (Mod.regular (continuousScalarRing E).X) x
    let : MonObj (Profinite.continuousMapRingObjOfUniverse E).obj :=
      (Profinite.continuousMapRingPresheafOfUniverse E).monObjCompForget₂
    have hm := Sheaf.μ_comp_map_mul (Profinite.continuousMapRingObjOfUniverse E)
    have hmul := ConcreteCategory.congr_hom (congr_app hm (op (Profinite.of (S × P))))
      (TensorProduct.tmul ℤ a y)
    change ((a • y).down (s, p)) = _
    change (((Functor.LaxMonoidal.μ
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
      (continuousScalarRing E).X (continuousScalarRing E).X).app
        (op (Profinite.of (S × P)))) (TensorProduct.tmul ℤ a y) |>
      ((MonObj.mul (X := (continuousScalarRing E).X)).hom.app
        (op (Profinite.of (S × P))))).down (s, p) = _
    exact congrArg (fun z ↦ z.down (s, p)) hmul
  · intro P S S' v x s p
    simp only [he, ev.restriction]
    rfl
  · intro P P' v S x s p
    simp only [he, parameterMap]
    exact congrArg (fun z ↦ z.down (s, p))
      (ev.parameter P P' S v (Mod.regular (continuousScalarRing E).X) x)
  · intro P
    let I := injectiveResolution (Mod.regular (continuousScalarRing E).X)
    have hi : QuasiIso (((homFunctor E P).mapHomologicalComplex (.up ℕ)).map I.ι) :=
      (quasiIso_iff_comp_left
        ((HomologicalComplex.singleMapHomologicalComplex (homFunctor E P) (.up ℕ) 0).inv.app
          (Mod.regular (continuousScalarRing E).X)) _).1 (haug P I)
    exact single_unit_isIso_of_resolution (homFunctor E P) _ I hi
  · intro P I
    have := haug P I
    have : QuasiIso (HomologicalComplex.extendMap (resolutionAugmentation E P I)
        ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance
    infer_instance
  · intro P P' v I
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
        simp [resolutionAugmentation]
    | succ n =>
        apply (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 _ (n + 1)
          (Nat.succ_ne_zero n)).eq_of_src
  · intro P
    exact (homFunctor E P).rightDerivedSingleUnit_zero _

end Profinite.NormedScalarHom
