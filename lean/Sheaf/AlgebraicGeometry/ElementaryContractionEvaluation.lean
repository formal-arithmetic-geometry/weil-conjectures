/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.TraceFormula.NodalContractionNormalizationBranches
import Sheaf.TraceFormula.NodalSubcurveBoundary
import Sheaf.TraceFormula.SmoothCurveSectionCartier
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Equalizer

/-! # Evaluation under an elementary pointed-curve contraction

Source: Knudsen, The projectivity of the moduli space of stable curves II (1983),
Section 2, Lemma 2.5, pp.178--179, and Section 1, Corollary 1.5 and Lemma 1.6
(blueprint: lem-sfb-elementary-contraction-evaluation).

The input and conclusion records below expand this node's hypotheses and clauses.
All modules are actual kernels, divisor ideals, tensor products and cokernels.
The four identifications retain the negative old-marking twist. Their normalization
uses pullback of functions, multiplication and the diagonal/difference exact row.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ElementaryContraction

/-- A contraction diagram of two ordered stable families with the same base and genus.
The last label of Y is the extra marking; `base_eq` only identifies the two presentations
of the common base. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
structure Diagram where
  S : Scheme.{u}
  g : ℕ
  r : ℕ
  X : StablePointedModuli S g r
  Y : StablePointedModuli S g (r + 1)
  base_eq : Y.base = X.base
  q : Y.curve ⟶ X.curve
  over_base : q ≫ X.projection =
    Y.projection ≫ eqToHom (congrArg Over.left base_eq)
  markings : ∀ i : Fin r, Y.sections i.castSucc ≫ q =
    eqToHom (congrArg Over.left base_eq) ≫ X.sections i

namespace Diagram

variable (D : Diagram.{u})

/-- The projection of Y to the common base. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def projection : D.Y.curve ⟶ D.X.base.left :=
  D.Y.projection ≫ eqToHom (congrArg Over.left D.base_eq)

/-- All markings of Y as sections over the common base. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def marking (i : Fin (D.r + 1)) : D.X.base.left ⟶ D.Y.curve :=
  eqToHom (congrArg Over.left D.base_eq.symm) ≫ D.Y.sections i

/-- The extra section, retaining its ordered label. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def last : D.X.base.left ⟶ D.Y.curve := D.marking (Fin.last D.r)

/-- The possibly nodal or old-marking image of the extra section.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def delta : D.X.base.left ⟶ D.X.curve := D.last ≫ D.q

/-- The contraction after a geometric base change. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def fiberMap {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ D.X.base.left) :
    pullback (C := Scheme.{u}) D.projection a ⟶ pullback (C := Scheme.{u}) D.X.projection a :=
  pullback.map D.projection a D.X.projection a D.q (𝟙 _) (𝟙 _)
    (by simpa only [projection, Category.comp_id] using D.over_base.symm) (by simp)

/-- One smooth rational component is the fibre over x, contains the last marking,
has exactly three normalized special points, and the map is an isomorphism off x.
Smoothness is imposed on the reduced component itself, not just its normalization.
Source: Knudsen II, Lemma 2.5, geometric tail/bridge cases
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def Exceptional {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ D.X.base.left)
    (Z : irreducibleComponents (pullback (C := Scheme.{u}) D.projection a))
    (x : pullback (C := Scheme.{u}) D.X.projection a) : Prop :=
  ∃ hx : IsClosed ({x} : Set (pullback (C := Scheme.{u}) D.X.projection a)),
    Smooth ((Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫
        pullback.snd D.projection a) ∧
    (pullback (C := Scheme.{u}) D.projection a).normalizedComponentGenus
      (pullback.snd D.projection a) Z = 0 ∧
    Set.range (pullback.lift (f := D.projection) (g := a) (a ≫ D.last) (𝟙 _) (by
      simp only [last, marking, projection, Category.assoc]
      rw [← Category.assoc (D.Y.sections (Fin.last D.r)) D.Y.projection,
        D.Y.section_projection]
      simp)) ⊆ Z.1 ∧
    ((pullback (C := Scheme.{u}) D.projection a).normalizedComponentMap Z ⁻¹'
      ({y | ¬ ∃ U : (pullback (C := Scheme.{u}) D.projection a).Opens,
          y ∈ U ∧ Smooth (U.ι ≫ pullback.snd D.projection a)} ∪
        ⋃ i : Fin (D.r + 1), Set.range (pullback.lift (f := D.projection) (g := a)
          (a ≫ D.marking i) (𝟙 _) (by
          simp only [marking, projection, Category.assoc]
          rw [← Category.assoc (D.Y.sections i) D.Y.projection, D.Y.section_projection]
          simp)))).encard = 3 ∧
    D.fiberMap a ⁻¹' {x} = Z.1 ∧
    IsIso (pullback.snd (D.fiberMap a)
      (Scheme.Opens.ι (X := pullback (C := Scheme.{u}) D.X.projection a) ⟨{x}ᶜ, hx.isOpen_compl⟩))

/-- The geometric-fibre hypothesis permits identity fibres as well as one exceptional
rational component. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def IsElementary : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ D.X.base.left),
    IsIso (D.fiberMap a) ∨
      ∃ (Z : irreducibleComponents (pullback (C := Scheme.{u}) D.projection a))
        (x : pullback (C := Scheme.{u}) D.X.projection a), D.Exceptional a Z x

/-- The old-marking effective divisor, represented by the product of its section ideals.
For no old markings the product is the unit ideal. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def oldIdealX : D.X.curve.IdealSheafData := ∏ i : Fin D.r, (D.X.sections i).ker

/-- The old-marking divisor on Y. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def oldIdealY : D.Y.curve.IdealSheafData := ∏ i : Fin D.r, (D.marking i.castSucc).ker

/-- The exact kernel defining J; no smoothness of delta is assumed.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def ideal : D.X.curve.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit D.delta.toRingCatSheafHom)

/-- The kernel inclusion of J into the structure sheaf. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def idealι : D.ideal ⟶ Scheme.Modules.unit D.X.curve := kernel.ι _

/-- Multiplication by functions into the dual of an ideal, obtained by tensor-Hom curry.
Source: Knudsen II, Lemma 2.5, multiplication map
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def multiplication {W : Scheme.{u}} {I : W.Modules}
    (ι : I ⟶ Scheme.Modules.unit W) : Scheme.Modules.unit W ⟶ I.dual :=
  MonoidalClosed.curry ((ρ_ I).hom ≫ ι)

/-- The specified diagonal (multiplication, divisor inclusion) defining K.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def diagonal : Scheme.Modules.unit D.X.curve ⟶
    D.ideal.dual ⊞ D.oldIdealX.toModules.dual :=
  biprod.lift (multiplication D.idealι) (multiplication D.oldIdealX.toModulesι)

/-- The actual cokernel K of the specified diagonal. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def expansionModule : D.X.curve.Modules := cokernel D.diagonal

/-- The four modules on Y, ordered as O, O(-E), O(t-E), O(t).
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def line : Fin 4 → D.Y.curve.Modules :=
  ![Scheme.Modules.unit D.Y.curve, D.oldIdealY.toModules,
    D.last.ker.toModules.dual ⊗ D.oldIdealY.toModules, D.last.ker.toModules.dual]

/-- The four predicted direct images, including both occurrences of the minus-D twist.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def image : Fin 4 → D.X.curve.Modules :=
  ![Scheme.Modules.unit D.X.curve, D.oldIdealX.toModules,
    D.ideal.dual ⊗ D.oldIdealX.toModules, D.expansionModule ⊗ D.oldIdealX.toModules]

/-- Inclusion O(t-E) into O(t). Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def includeOld : D.line 2 ⟶ D.line 3 :=
  D.last.ker.toModules.dual ◁ D.oldIdealY.toModulesι ≫ (ρ_ _).hom

/-- Multiplication O(-t) tensor O(t-E) into O(-E).
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def pair : D.last.ker.toModules ⊗ D.line 2 ⟶ D.line 1 :=
  (α_ _ _ _).inv ≫ Scheme.Modules.dualEvaluation D.last.ker.toModules ▷ _ ≫ (λ_ _).hom

/-- The four isomorphisms, normalized by functions, multiplication, and the cokernel
of the diagonal/difference row; the auxiliary minus-t isomorphism is the kernel map.
These equations determine the specified comparisons without choosing exceptional coordinates.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
structure Comparisons where
  iso : ∀ i : Fin 4, D.image i ≅ (Scheme.Modules.pushforward D.q).obj (D.line i)
  minus : D.ideal ≅ (Scheme.Modules.pushforward D.q).obj D.last.ker.toModules
  functions : (iso 0).hom = SheafOfModules.unitToPushforwardObjUnit D.q.toRingCatSheafHom
  old : (iso 1).hom ≫ (Scheme.Modules.pushforward D.q).map D.oldIdealY.toModulesι =
    D.oldIdealX.toModulesι ≫ (iso 0).hom
  kernel : minus.hom ≫ (Scheme.Modules.pushforward D.q).map D.last.ker.toModulesι =
    D.idealι ≫ (iso 0).hom
  multiplier : ∀ (U : D.X.curve.Opens) (a : Γ(D.ideal, U)) (b : Γ(D.image 2, U)),
    (iso 1).inv.app U (D.pair.app (D.q ⁻¹ᵁ U)
      (Scheme.Modules.tmulSection (minus.hom.app U a) ((iso 2).hom.app U b))) =
      ((Scheme.Modules.dualTensorHom D.ideal D.oldIdealX.toModules).app U b).app
        (op (Over.mk (𝟙 U))) a
  cokernel_left :
    (biprod.inl ▷ D.oldIdealX.toModules ≫
      cokernel.π D.diagonal ▷ D.oldIdealX.toModules) ≫ (iso 3).hom =
        (iso 2).hom ≫ (Scheme.Modules.pushforward D.q).map D.includeOld
  cokernel_right :
    (biprod.inr ▷ D.oldIdealX.toModules ≫
      cokernel.π D.diagonal ▷ D.oldIdealX.toModules) ≫ (iso 3).hom =
        -((β_ _ _).hom ≫ Scheme.Modules.dualEvaluation D.oldIdealX.toModules ≫
          (iso 0).hom ≫ (Scheme.Modules.pushforward D.q).map
            (multiplication D.last.ker.toModulesι))

/-- Evaluation transported by the fourth normalized comparison, using the canonical
section-normalized pullback/direct-image adjunction. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def evaluation (C : D.Comparisons) :
    (Scheme.Modules.tensorPullback D.q).obj (D.image 3) ⟶ D.line 3 :=
  (Scheme.Modules.tensorPullback D.q).map (C.iso 3).hom ≫
    (Scheme.Modules.tensorPullbackSectionAdjunction D.q).counit.app (D.line 3)


/-- The section-normalized tensor comparison already supplied by the module-pullback API.
Its pure-tensor formula uniquely determines it, so only a universal-property proof is chosen.
Source: Stacks, Tag 01CD (blueprint: lem-sfb-elementary-contraction-evaluation). -/
def pullTensor {A B : Scheme.{u}} (f : A ⟶ B) (M N : B.Modules) :
    (Scheme.Modules.tensorPullback f).obj (M ⊗ N) ≅
      (Scheme.Modules.tensorPullback f).obj M ⊗ (Scheme.Modules.tensorPullback f).obj N :=
  Classical.choose (Scheme.Modules.module_pullback_tensor f) M N

/-- Pullback of the evaluation pairing of an invertible ideal and its dual.
Source: Knudsen II, Lemma 2.5, tensoring away the old divisor
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def pullPair {A B : Scheme.{u}} (f : A ⟶ B) (I : B.Modules) [I.IsInvertible] :
    (Scheme.Modules.tensorPullback f).obj I ⊗
      (Scheme.Modules.tensorPullback f).obj I.dual ≅ Scheme.Modules.unit A :=
  letI := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f).1
  (pullTensor f I I.dual).symm ≪≫
    (Scheme.Modules.tensorPullback f).mapIso (asIso (Scheme.Modules.dualEvaluation I)) ≪≫
      asIso (Scheme.Modules.tensorPullbackObjUnitToUnit f)

/-- The equivalent invertible quotient, obtained from evaluation by cancelling the
negative old-divisor twist. This is an explicit tensor construction.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def quotient (C : D.Comparisons) (hD : D.oldIdealX.IsInvertible) :
    (Scheme.Modules.tensorPullback D.q).obj D.expansionModule ⟶
      D.line 3 ⊗ (Scheme.Modules.tensorPullback D.q).obj D.oldIdealX.toModules.dual :=
  letI := hD.isInvertible_toModules
  (ρ_ _).inv ≫
    _ ◁ (pullPair D.q D.oldIdealX.toModules).inv ≫
      (α_ _ _ _).inv ≫
        (pullTensor D.q D.expansionModule D.oldIdealX.toModules).inv ▷ _ ≫
          D.evaluation C ▷ _

/-- The target line of the untwisted quotient. Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def quotientLine : D.Y.curve.Modules :=
  D.line 3 ⊗ (Scheme.Modules.tensorPullback D.q).obj D.oldIdealX.toModules.dual

/-- The induced fibre map into the projective bundle over the target fibre.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def projectiveFiberMap [D.expansionModule.IsQuasicoherent]
    (b : D.Y.curve ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData D.expansionModule).relProj)
    (hb : b ≫ (SymmetricAlgebraSheaf.gradedAlgebraData D.expansionModule).relProjHom = D.q)
    {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ D.X.base.left) :
    pullback (C := Scheme.{u}) D.projection a ⟶
      pullback (SymmetricAlgebraSheaf.gradedAlgebraData D.expansionModule).relProjHom
        (pullback.fst D.X.projection a) :=
  pullback.lift (pullback.fst D.projection a ≫ b) (D.fiberMap a) (by
    simp [Category.assoc, hb, fiberMap, pullback.map])

/-- The Proj map, ordered quotient lifts, and geometric-fibre descriptions.
Old lifts kill the J-dual summand; the last lift kills the O(D) summand.
The complete degree-one condition is expressed by an isomorphism of the exceptional
component with the target exceptional projective line, preserving O(1).
Source: Knudsen II, Lemma 2.5, pp.178--179
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
structure Geometry (C : D.Comparisons) (hD : D.oldIdealX.IsInvertible)
    [D.expansionModule.IsQuasicoherent] where
  tautological : ProjectiveBundleQuotientGeometry.TautologicalQuotient D.expansionModule
  map : D.Y.curve ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData D.expansionModule).relProj
  over_X : map ≫ (SymmetricAlgebraSheaf.gradedAlgebraData D.expansionModule).relProjHom = D.q
  classifies : ProjectiveBundleQuotientGeometry.Classifies tautological D.q D.quotientLine
    (D.quotient C hD) map
  old_lifts : ∀ i : Fin D.r,
    (Scheme.Modules.tensorPullback (D.marking i.castSucc)).map
      ((Scheme.Modules.tensorPullback D.q).map
        (biprod.inl ≫ cokernel.π D.diagonal) ≫ D.quotient C hD) = 0
  last_lift : (Scheme.Modules.tensorPullback D.last).map
    ((Scheme.Modules.tensorPullback D.q).map
      (biprod.inr ≫ cokernel.π D.diagonal) ≫ D.quotient C hD) = 0
  identity_fibers : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ D.X.base.left), IsIso (D.fiberMap a) →
      IsIso (D.projectiveFiberMap map over_X a)
  exceptional_fibers : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ D.X.base.left)
    (Z : irreducibleComponents (pullback (C := Scheme.{u}) D.projection a))
    (x : pullback (C := Scheme.{u}) D.X.projection a), D.Exceptional a Z x →
      ∃ (hx : IsClosed ({x} : Set (pullback (C := Scheme.{u}) D.X.projection a)))
        (point : Spec (.of Ω) ⟶ pullback (C := Scheme.{u}) D.X.projection a),
        Set.range point = {x} ∧
        IsIso (pullback.snd
          (pullback.snd
            (SymmetricAlgebraSheaf.gradedAlgebraData D.expansionModule).relProjHom
            (pullback.fst D.X.projection a))
          (Scheme.Opens.ι (X := pullback (C := Scheme.{u}) D.X.projection a)
            ⟨{x}ᶜ, hx.isOpen_compl⟩)) ∧
        ∃ e : (pullback (C := Scheme.{u}) D.projection a).reducedNormalizationComponent Z ≅
            pullback
              (pullback.snd
                (SymmetricAlgebraSheaf.gradedAlgebraData D.expansionModule).relProjHom
                (pullback.fst D.X.projection a)) point,
          e.hom ≫ pullback.fst _ _ =
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫
                D.projectiveFiberMap map over_X a ∧
          ∃ eP : ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of Ω)) ≅
              (pullback (C := Scheme.{u}) D.projection a).reducedNormalizationComponent Z,
            eP.hom ≫ e.hom ≫ pullback.snd _ _ =
              (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of Ω)) ↘ Spec (.of Ω)) ∧
            Nonempty ((Scheme.Modules.tensorPullback
              (eP.hom ≫ (Scheme.IdealSheafData.vanishingIdeal
                ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫
                  pullback.fst D.projection a)).obj D.quotientLine ≅
              ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of Ω)) 1)

/-- All the pointwise conclusions, with actual divisor invertibility and surjectivity.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
structure Result (C : D.Comparisons) where
  oldCartierX : D.oldIdealX.IsInvertible
  oldCartierY : D.oldIdealY.IsInvertible
  lastCartier : D.last.ker.IsInvertible
  quasicoherent : D.expansionModule.IsQuasicoherent
  evaluation_surjective : Epi (D.evaluation C)
  quotient_invertible : D.quotientLine.IsInvertible
  quotient_surjective : Epi (D.quotient C oldCartierX)
  geometry : @Geometry D C oldCartierX quasicoherent


/-- An arbitrary cartesian base change of labelled contraction diagrams. Every isomorphism
of diagrams is such a change; base identities do not force either curve map to be the identity.
Source: Knudsen II, Lemma 2.5, functoriality
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
structure Change (D' : Diagram.{u}) where
  base : D'.X.base.left ⟶ D.X.base.left
  x : D'.X.curve ⟶ D.X.curve
  y : D'.Y.curve ⟶ D.Y.curve
  genus_eq : D'.g = D.g
  labels_eq : D'.r = D.r
  squareX : IsPullback x D'.X.projection D.X.projection base
  squareY : IsPullback y D'.projection D.projection base
  squareQ : IsPullback y D'.q D.q x
  old_labels : ∀ i : Fin D'.r,
    D'.X.sections i ≫ x = base ≫ D.X.sections (Fin.cast labels_eq i)
  all_labels : ∀ i : Fin (D'.r + 1),
    D'.marking i ≫ y = base ≫ D.marking (Fin.cast (congrArg (· + 1) labels_eq) i)

variable {D} {D' : Diagram.{u}}

/-- The canonical interchange of pullbacks in the contraction square.
Source: Stacks, Tag 0097; Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def Change.interchange (A : D.Change D') (M : D.X.curve.Modules) :
    (Scheme.Modules.tensorPullback A.y).obj ((Scheme.Modules.tensorPullback D.q).obj M) ≅
      (Scheme.Modules.tensorPullback D'.q).obj ((Scheme.Modules.tensorPullback A.x).obj M) :=
  ((Scheme.Modules.tensorPullbackSectionComp A.y D.q).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj M) A.squareQ.w) ≪≫
      (Scheme.Modules.tensorPullbackSectionComp D'.q A.x).app M

/-- Canonical pullback identifications for the divisor ideals, their duals, the section
ideal and K. Inclusion, evaluation-pairing and cokernel equations fix all these maps.
They are conclusions of compatibility, not extra assumptions on the contraction.
Source: Knudsen II, Lemma 2.5, final functoriality paragraph
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
structure Change.Modules (A : D.Change D') where
  oldX : (Scheme.Modules.tensorPullback A.x).obj D.oldIdealX.toModules ≅
    D'.oldIdealX.toModules
  oldY : (Scheme.Modules.tensorPullback A.y).obj D.oldIdealY.toModules ≅
    D'.oldIdealY.toModules
  last : (Scheme.Modules.tensorPullback A.y).obj D.last.ker.toModules ≅
    D'.last.ker.toModules
  ideal : (Scheme.Modules.tensorPullback A.x).obj D.ideal ≅ D'.ideal
  dualOld : (Scheme.Modules.tensorPullback A.x).obj D.oldIdealX.toModules.dual ≅
    D'.oldIdealX.toModules.dual
  dualLast : (Scheme.Modules.tensorPullback A.y).obj D.last.ker.toModules.dual ≅
    D'.last.ker.toModules.dual
  dualIdeal : (Scheme.Modules.tensorPullback A.x).obj D.ideal.dual ≅ D'.ideal.dual
  expansion : (Scheme.Modules.tensorPullback A.x).obj D.expansionModule ≅ D'.expansionModule
  oldX_inclusion : oldX.hom ≫ D'.oldIdealX.toModulesι =
    (Scheme.Modules.tensorPullback A.x).map D.oldIdealX.toModulesι ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit A.x
  oldY_inclusion : oldY.hom ≫ D'.oldIdealY.toModulesι =
    (Scheme.Modules.tensorPullback A.y).map D.oldIdealY.toModulesι ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit A.y
  last_inclusion : last.hom ≫ D'.last.ker.toModulesι =
    (Scheme.Modules.tensorPullback A.y).map D.last.ker.toModulesι ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit A.y
  ideal_inclusion : ideal.hom ≫ D'.idealι =
    (Scheme.Modules.tensorPullback A.x).map D.idealι ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit A.x
  old_pairing : (oldX.hom ⊗ₘ dualOld.hom) ≫
      Scheme.Modules.dualEvaluation D'.oldIdealX.toModules =
    (pullTensor A.x D.oldIdealX.toModules D.oldIdealX.toModules.dual).inv ≫
      (Scheme.Modules.tensorPullback A.x).map
        (Scheme.Modules.dualEvaluation D.oldIdealX.toModules) ≫
          Scheme.Modules.tensorPullbackObjUnitToUnit A.x
  last_pairing : (last.hom ⊗ₘ dualLast.hom) ≫
      Scheme.Modules.dualEvaluation D'.last.ker.toModules =
    (pullTensor A.y D.last.ker.toModules D.last.ker.toModules.dual).inv ≫
      (Scheme.Modules.tensorPullback A.y).map
        (Scheme.Modules.dualEvaluation D.last.ker.toModules) ≫
          Scheme.Modules.tensorPullbackObjUnitToUnit A.y
  ideal_pairing : (ideal.hom ⊗ₘ dualIdeal.hom) ≫ Scheme.Modules.dualEvaluation D'.ideal =
    (pullTensor A.x D.ideal D.ideal.dual).inv ≫
      (Scheme.Modules.tensorPullback A.x).map (Scheme.Modules.dualEvaluation D.ideal) ≫
        Scheme.Modules.tensorPullbackObjUnitToUnit A.x
  expansion_left :
    (Scheme.Modules.tensorPullback A.x).map (biprod.inl ≫ cokernel.π D.diagonal) ≫
      expansion.hom = dualIdeal.hom ≫ biprod.inl ≫ cokernel.π D'.diagonal
  expansion_right :
    (Scheme.Modules.tensorPullback A.x).map (biprod.inr ≫ cokernel.π D.diagonal) ≫
      expansion.hom = dualOld.hom ≫ biprod.inr ≫ cokernel.π D'.diagonal

/-- The canonical comparison of the four proposed direct images.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def Change.Modules.image {A : D.Change D'} (M : A.Modules) :
    ∀ i : Fin 4, (Scheme.Modules.tensorPullback A.x).obj (D.image i) ⟶ D'.image i :=
  Fin.cases (Scheme.Modules.tensorPullbackObjUnitToUnit A.x)
    (Fin.cases M.oldX.hom (Fin.cases
      ((pullTensor A.x D.ideal.dual D.oldIdealX.toModules).hom ≫
        (M.dualIdeal.hom ⊗ₘ M.oldX.hom)) (Fin.cases
          ((pullTensor A.x D.expansionModule D.oldIdealX.toModules).hom ≫
            (M.expansion.hom ⊗ₘ M.oldX.hom)) (fun i ↦ Fin.elim0 i))))

/-- The canonical comparison of the four divisor modules on Y.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def Change.Modules.line {A : D.Change D'} (M : A.Modules) :
    ∀ i : Fin 4, (Scheme.Modules.tensorPullback A.y).obj (D.line i) ⟶ D'.line i :=
  Fin.cases (Scheme.Modules.tensorPullbackObjUnitToUnit A.y)
    (Fin.cases M.oldY.hom (Fin.cases
      ((pullTensor A.y D.last.ker.toModules.dual D.oldIdealY.toModules).hom ≫
        (M.dualLast.hom ⊗ₘ M.oldY.hom)) (Fin.cases M.dualLast.hom (fun i ↦ Fin.elim0 i))))

/-- Transport of the line targeted by the untwisted evaluation quotient.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def Change.Modules.quotientLine {A : D.Change D'} (M : A.Modules) :
    (Scheme.Modules.tensorPullback A.y).obj D.quotientLine ⟶ D'.quotientLine :=
  (pullTensor A.y (D.line 3)
    ((Scheme.Modules.tensorPullback D.q).obj D.oldIdealX.toModules.dual)).hom ≫
      (M.dualLast.hom ⊗ₘ
        ((A.interchange D.oldIdealX.toModules.dual).hom ≫
          (Scheme.Modules.tensorPullback D'.q).map M.dualOld.hom))

/-- Every direct-image comparison and both evaluation quotients commute with the actual
cartesian base-change map. These squares also express equivariance for every labelled
isomorphism, including automorphisms with identity map on X.
Source: Knudsen II, Lemma 2.5
(blueprint: lem-sfb-elementary-contraction-evaluation). -/
def Change.Compatible (A : D.Change D') (M : A.Modules)
    (C : D.Comparisons) (C' : D'.Comparisons)
    (hD : D.oldIdealX.IsInvertible) (hD' : D'.oldIdealX.IsInvertible) : Prop :=
  (∀ i : Fin 4,
    IsIso (Scheme.Modules.moduleBaseChangeMap D.q D'.q A.x A.y A.squareQ.w (D.line i)) ∧
    (Scheme.Modules.tensorPullback A.x).map (C.iso i).hom ≫
      Scheme.Modules.moduleBaseChangeMap D.q D'.q A.x A.y A.squareQ.w (D.line i) ≫
        (Scheme.Modules.pushforward D'.q).map (M.line i) =
          M.image i ≫ (C'.iso i).hom) ∧
  (Scheme.Modules.tensorPullback A.y).map (D.evaluation C) ≫ M.line 3 =
    (A.interchange (D.image 3)).hom ≫
      (Scheme.Modules.tensorPullback D'.q).map (M.image 3) ≫ D'.evaluation C' ∧
  (Scheme.Modules.tensorPullback A.y).map (D.quotient C hD) ≫ M.quotientLine =
    (A.interchange D.expansionModule).hom ≫
      (Scheme.Modules.tensorPullback D'.q).map M.expansion.hom ≫ D'.quotient C' hD'

variable (D)

/-- Evaluation under an elementary rational-component contraction, including all four
normalized direct-image isomorphisms, the invertible quotient, its ordered Proj lifts,
its complete degree-one exceptional map, and arbitrary cartesian base-change naturality.
Source: Knudsen II, Lemma 2.5, pp.178--179, using Corollary 1.5 and Lemma 1.6
(blueprint: lem-sfb-elementary-contraction-evaluation).

Proof, with every step and dependency of the DAG node:

1. The stable-family definitions give proper, flat finitely presented nodal families; projectivity
implies properness, and properness of $Y/T$ with separatedness of $X/T$ makes $q$ proper. Work on a
geometric fibre. The branch lemma identifies the complement's normalized branches with those of $X$
at $x=q(A)$, so $A$ has one or two attachments, all transverse and distinct. Its other old special
points are old markings. Since it has three special points including $t$, the possibilities are a
tail with one attachment and exactly one $t_i$, or a bridge with two attachments and no $t_i$. The
tail image is smooth and equals $s_i$; the bridge image is a node. The same branch lemma identifies
the remaining curve with $X$ in the tail case and with its partial normalization at $x$ in the
bridge case. The exceptional component cannot be the whole connected fibre, because its genus would
be zero instead of $g\geq2$.
Uses: def-sfb-stable-pointed-curve, def-sfb-stable-pointed-moduli-groupoids, lem-trf-projective-
bundle-proper, lem-weil-pbc-proper-to-separated, lem-trf-nodal-contraction-normalization-branches.

2. Set $F_0=\mathcal O_Y$, $F_E=\mathcal O_Y(-E)$, $F_{-t}=\mathcal O_Y(-t)$, $F_N=\mathcal
O_Y(t-E)$ and $F_t=\mathcal O_Y(t)$. Each marked section lies in the relative smooth locus. Restrict
the curve to that open locus and apply the smooth-curve-section Cartier lemma; properness makes the
sections closed in the full curve, so being Cartier near their images and having unit ideal
elsewhere proves they are Cartier on the full curve. Thus these are invertible divisor modules. If
$m$ is the number of old markings on a contracted component, then $m\in\{0,1\}$ and their
exceptional degrees are respectively $0,-m,-1,1-m,1$. Apply the line-cohomology lemma to each: all
five direct images are finitely presented and $T$-flat, all first higher direct images vanish, and
their formation commutes with every base change on $T$. For $F_t$ the exceptional degree is one, so
evaluation $q^*q_*F_t\twoheadrightarrow F_t$ is surjective. The degree condition is vacuous on
isomorphism fibres. Apply the dual-section-ideal lemma to $(X/T,\Delta)$: $\mathcal J^\vee(-D)$ is
also finitely presented and $T$-flat and commutes with base change (locally the divisor factor is
free of rank one).
Uses: lem-sfb-rational-contraction-line-cohomology, lem-sfb-nodal-section-dual-flat, def-pc-divisor-
line-bundle, lem-trf-smooth-curve-section-cartier.

3. There are natural maps $\alpha:\mathcal O_X\to q_*F_0$ and $\beta:\mathcal O_X(-D)\to q_*F_E$:
pull back a function, respectively a function vanishing on all $s_i$; it then vanishes on all $t_i$.
Check them on geometric fibres, using the closed-union ring identity to describe functions as
functions on the remaining curve and on $A$ with equal attachment values. For $F_0$, a function on
$A\simeq\mathbf P^1$ is constant. At a tail this is determined by its one boundary value; at a
bridge the two branch values must agree. These are exactly functions on $X$. For $F_E$, a tail has
$F_E|_A=\mathcal O(-1)$ and thus no section on $A$; the remaining function must vanish at the
attachment, giving $\mathcal O_X(-s_i)$ there. At a bridge $E$ avoids $A$, so the same equal-value
rule as for $F_0$ applies. Away from the exceptional image the assertion is the given isomorphism
and the same old divisor; in the isomorphism case it is tautological. Here the polynomial
descriptions $H^0(\mathbf P^1,\mathcal O)=\Omega$ and $H^0(\mathbf P^1,\mathcal O(-1))=0$ follow by
writing sections on its two affine charts and matching on their overlap.
Uses: lem-trf-closed-union-pushout, lem-trf-nodal-subcurve-boundary.

4. The fibre identifications make $\alpha,\beta$ isomorphisms over $T$. Explicitly, at $x\in X$ over
$a\in T$, Nakayama applied to the finite cokernel first gives surjectivity from surjectivity on the
geometric fibre (field extension is faithful). The target is flat over $\mathcal O_{T,a}$ by step 2.
Tensoring a surjection onto a flat module therefore preserves its kernel sequence, so the kernel has
zero fibre. This kernel is finite: choose finitely many source generators; the target's finite
presentation makes the relations among their images finitely generated, and their image generates
the kernel. Nakayama now kills the kernel. Thus $q_*F_0=\mathcal O_X$ and $q_*F_E=\mathcal O_X(-D)$
through these actual maps. The same argument will apply to the comparison in step 7, whose target is
$T$-flat by step 2. Left exactness of direct image applied to $0\to F_{-t}\to F_0\to t_*\mathcal
O_T\to0$ identifies $q_*F_{-t}$ with $\ker(\mathcal O_X\to\Delta_*\mathcal O_T)=\mathcal J$; kernels
are computed sectionwise, and $q t=\Delta$.
Uses: lem-weil-pbc-nakayama-local-generators, lem-weil-pbc-flat-quotient-tensor-injective.

5. Multiplication of divisor modules gives $F_{-t}\otimes F_N\to F_E$. With step 4 it defines a
canonical map $\mu:q_*F_N\to\mathcal Hom(\mathcal J,\mathcal O_X(-D))=\mathcal J^\vee\otimes\mathcal
O_X(-D)$ by $b\mapsto(a\mapsto ab)$. The equality on the right is checked after locally trivializing
$\mathcal O_X(-D)$. This map uses the already constructed identification $q_*F_{-t}=\mathcal J$,
rather than presuming that pulling back $\mathcal J$ is invertible. Away from the exceptional image,
and on an isomorphism fibre, it is the multiplication isomorphism for the Cartier divisor $t$.
Uses: def-pc-divisor-line-bundle.

6. For a geometric tail, write $x=s_i=\Delta$. The remaining curve is $X$, while $F_N|_A=\mathcal
O_A(t-t_i)$ is trivial: choose a rational coordinate with zero at $t_i$ and pole at $t$, whose
divisor is $t_i-t$. A section on $A$ is determined by its boundary value at the attachment, since
that point is disjoint from $t,t_i$. Thus forgetting the exceptional section identifies $q_*F_N$
locally at $x$ with $\mathcal O_X$ through its remaining-curve value. On $X$, $\mathcal J=\mathcal
O_X(-x)$ and locally $D=x$. Multiplication takes that remaining-curve value $b$ to the homomorphism
$a\mapsto ab$ from $\mathcal O_X(-x)$ to itself. This is exactly the isomorphism $\mathcal
O_X\to\mathcal J^\vee(-D)$. All other old markings are disjoint from $x$ and contribute the same
invertible factor on both sides. Hence $\mu$ is an isomorphism on every tail fibre.
Uses: lem-trf-closed-union-pushout, lem-sfb-nodal-section-dual-flat.

7. For a geometric bridge, $E$ avoids $A$, and $F_N|_A=\mathcal O_A(t)$. A section of this line is
uniquely determined by its values at the two attachment points: choose their coordinates $0,\infty$,
so sections have the form $aU+bV$ and the two values give $b,a$. Consequently the closed-union
description identifies $q_*F_N$ with $\nu_*\mathcal O_{\widetilde X}$ near $x$, where $\nu$
separates the two branches of $X$ at $x$. The dual-section-ideal lemma identifies $\mathcal J^\vee$
with precisely this multiplier module, and $D$ avoids $x$. Under these identifications,
multiplication sends a branch function $b$ to $a\mapsto ab$, so $\mu$ is the identity of this
module. Combining with steps 5--6 proves it is an isomorphism on every geometric fibre. Apply the
finite-kernel/Nakayama argument of step 4, using step 2's flat target, to obtain $q_*\mathcal
O_Y(t-E)\cong\mathcal J^\vee(-D)$ on $X$.
Uses: lem-trf-closed-union-pushout, lem-sfb-nodal-section-dual-flat, lem-weil-pbc-nakayama-local-
generators, lem-weil-pbc-flat-quotient-tensor-injective.

8. The disjoint Cartier divisors $t$ and $E$ give the exact sequence $0\to
F_E\xrightarrow{(1,1)}F_N\oplus F_0\xrightarrow{(b,c)\mapsto b-c}F_t\to0$. Check it off $t\cup E$,
near $t$ where $E$ is empty, and near $E$ where $t$ is empty: one of the two summand inclusions is
then an isomorphism, the difference is surjective, and its kernel is the displayed diagonal. The
direct-image long exact sequence and $R^1q_*F_E=0$ from step 2 make its pushforward short exact.
Module sheaves have enough injectives, so the right-derived delta-functor applies to the left exact
direct image. Using steps 4 and 7, its first arrow is $\mathcal O_X(-D)\to\mathcal
J^\vee(-D)\oplus\mathcal O_X$, with components multiplication and the divisor inclusion: on the
first component the image of $f$ acts on $a\in\mathcal J$ as $a\mapsto af$. This is the defining
sequence of $\mathcal K$ tensored by $\mathcal O_X(-D)$, so its cokernel is $\mathcal K(-D)$. Thus
the induced cokernel isomorphism is $q_*F_t\cong\mathcal K(-D)$, retaining the negative $D$ twist.
Uses: def-pc-divisor-line-bundle, lem-weil-pbc-scheme-modules-enough-injectives, lem-weil-pbc-right-
derived-universal-delta-functor.

9. Transport step 2's surjective evaluation along the cokernel isomorphism and tensor with the
invertible module $q^*\mathcal O_X(D)$. This gives $q^*\mathcal K\twoheadrightarrow F_t\otimes
q^*\mathcal O_X(D)$. The quotient-geometry theorem attaches the required $X$-map into
$\operatorname{Proj}_X(\operatorname{Sym}\mathcal K)$. At each old section $t_i$, the $F_N$
inclusion in $F_t$ vanishes because of the factor $-E$; hence the quotient factors through the
cokernel of the $\mathcal J^\vee$ summand. At $t$, the $F_0$ inclusion in $F_t$ vanishes, so it
factors through the cokernel of the $\mathcal O_X(D)$ summand. The expansion lemma states that these
are the invertible quotients defining the ordered lifts. Factorization of the surjective quotient
through these lines gives exactly those quotient classes, including the harmless sign in $b-c$. Thus
every old label and the last label is sent to its prescribed lift.
Uses: lem-trf-projective-bundle-quotient-geometry, lem-sfb-section-ideal-proj-expansion, lem-weil-
pbc-invertible-pullback-tensor.

10. On a geometric fibre the expansion lemma identifies the target with $X$ off the exceptional
image. The constructed map is over $X$, hence is the identity on that open. On $A$, $q^*\mathcal
O_X(D)$ is a constant line, so the quotient line has degree one. The evaluation supplies its
complete two-dimensional space of sections: on a bridge the two attachment values are independent by
step 7; on a tail any section of $\mathcal O_A(t)$ extends near the exceptional image, since its one
boundary value is matched by a regular function on the remaining curve. The closed-union description
gives these extensions explicitly. In coordinates a basis gives $[U:V]\mapsto[U:V]$, after changing
bases by an invertible matrix. Thus $A$ identifies with the target's exceptional projective line by
its complete degree-one system. On an isomorphism fibre, $\Delta$ is smooth and disjoint from $D$;
the expansion lemma says the target is $X$ itself, so the map over $X$ is an isomorphism of the
entire fibre.
Uses: lem-sfb-section-ideal-proj-expansion, lem-trf-closed-union-pushout.

11. Every comparison just used is a specified map: pullback of functions for $\alpha,\beta$, a
kernel for $\mathcal J$, multiplication for $\mu$, the diagonal and difference for the exact
sequence, its induced cokernel map, and adjunction evaluation for the quotient. Direct-image base
change for the five modules is supplied by the line-cohomology lemma; base change of the dual and
its multiplication inclusion is supplied by the dual-section-ideal lemma. Cartier divisor ideals and
their inclusions pull back for these smooth disjoint sections. These facts carry the defining maps
to the same maps after every $T'\to T$, and therefore carry their inverse isomorphisms and the
cokernel identification to the corresponding ones. The expansion lemma and quotient-geometry theorem
give the same compatibility for the target and its lifts. For an isomorphism of contraction diagrams
all function pullbacks and multiplication squares commute, the section ideals are carried to the
same ideals, and the difference map remains $(b,c)\mapsto b-c$. Adjunction evaluation is natural, so
the resulting quotient classes agree. Naturality of the quotient classification then makes the
$X$-maps agree. This also applies to automorphisms over $1_X$; no choice of a coordinate on $A$
entered any construction.
Uses: lem-sfb-rational-contraction-line-cohomology, lem-sfb-nodal-section-dual-flat, lem-sfb-
section-ideal-proj-expansion, lem-trf-projective-bundle-quotient-geometry. -/
theorem elementary_contraction_evaluation (h : D.IsElementary) :
    ∃ (C : D.Comparisons) (R : D.Result C),
      ∀ (D' : Diagram.{u}) (A : D.Change D'),
        ∃ (C' : D'.Comparisons) (R' : D'.Result C') (M : A.Modules),
          A.Compatible M C C' R.oldCartierX R'.oldCartierX := by
  sorry

end Diagram

end AlgebraicGeometry.ElementaryContraction
