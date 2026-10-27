/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleSystemProjectionData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import all Sheaf.Paper.EtaleProperCoefficientTensorUnit
import Sheaf.Paper.EtaleSystemProjectionExistence
import Sheaf.Paper.EtaleSystemProjectionEvaluation
import Sheaf.Paper.EtaleSystemProjectionCoherence
import Sheaf.Paper.EtaleSingleCoefficientProjection

/-! # Constant coefficients and ordinary étale system compact support

Source: Zheng, Theorem 2.18(2), Construction 2.26, Constructions 5.14--5.15,
Lemma 5.16; Stacks Project, Tag 0GL6
(blueprint: lem-pur-etale-system-coefficient-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

private theorem projection_transpose {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} (t : Theory c l)
    {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    (M : Derived X B.rings) :
    (t.scalarY a).adjunction.homEquiv _ _ ((t.q a).app M) =
      (t.support B).F.map ((t.scalarX a).adjunction.unit.app M) ≫
        (t.restriction a).iso.inv.app ((t.scalarX a).model.T.obj M) := by
  exact (unit_mateEquiv_symm (t.scalarX a).adjunction (t.scalarY a).adjunction
    (TwoSquare.mk _ _ _ _ (t.restriction a).iso.inv) M).symm

private theorem level_jointly_reflects (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    JointlyReflectIsomorphisms (level W B) where
  isIso {M N} h hh := by
    have : IsIso
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map h) := by
      apply (NatTrans.isIso_iff_isIso_app _).2
      intro U
      have := hh U.unop.1
      have hs : IsIso (((level W B U.unop.1).map h).hom.app (op U.unop.2)) :=
        inferInstance
      have hb := (ConcreteCategory.isIso_iff_bijective
        (((level W B U.unop.1).map h).hom.app (op U.unop.2))).1 hs
      apply (ConcreteCategory.isIso_iff_bijective _).2
      change Function.Bijective (fun x ↦ h.val.app U x) at hb ⊢
      exact hb
    exact isIso_of_reflects_iso h
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

private theorem compact_scalar_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    IsIso (compactScalarMap a c) := by
  suffices ∀ M, IsIso ((compactScalarMap a c).app M) from
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
  intro M
  have := proper_scalarMate_isIso a c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  change IsIso ((scalarMate a c.g).app _ ≫
    (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((ExceptionalCoefficients.openIso a c.i).hom.app M))
  infer_instance

private theorem projection_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} (t : Theory c l)
    {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings) : IsIso (t.q a) := by
  suffices ∀ M, IsIso ((t.q a).app M) from
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
  intro M
  let : ∀ n, (level Y C.rings n).Additive := fun n ↦ (t.evaluationY C n).additive
  let : ∀ n, PreservesFiniteLimits (level Y C.rings n) :=
    fun n ↦ (t.evaluationY C n).limits
  let : ∀ n, PreservesFiniteColimits (level Y C.rings n) :=
    fun n ↦ (t.evaluationY C n).colimits
  apply (Functor.jointlyReflectIsomorphisms_mapDerivedCategory
    (level_jointly_reflects Y C.rings)).isIso_iff _ |>.2
  intro n
  have := B.finite n
  have := compact_scalar_isIso (a.app (op n)).hom c
  have hi : IsIso
      ((scalarExtension (a.app (op n)).hom Y).map
          ((t.supportEvaluation B n).iso.inv.app M) ≫
        (t.scalarEvaluationY a n).iso.inv.app ((t.support B).F.obj M) ≫
        (t.evaluationY C n).E.map ((t.q a).app M) ≫
        (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj M) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
            ((t.scalarEvaluationX a n).iso.hom.app M)) := by
    rw [etaleSystemProjection_evaluation c l t B C a n M]
    infer_instance
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi

/-- Constant coefficient projection for ordinary, unbounded derived strict systems.
The presentation includes actual geometric and scalar functors, normalized by sections
and adjunctions; q is the explicit mate, not unspecified comparison data. The final
single-ring clause uses the published proper-counit/open-tensor map directly.

Source: Zheng, Theorem 2.18(2), Construction 2.26, Constructions 5.14--5.15 and
Lemma 5.16; Stacks Project, Tag 0GL6
(blueprint: lem-pur-etale-system-coefficient-projection).

Proof: Regard strict systems as module sheaves on the vertical sequence site. Exact
inverse image, exact open extension, scalar extension and evaluation have the recorded
ordinary constructions and normalized adjunctions. Derive proper image on the system
category, giving the presentation t. The ordinary restriction/direct-image comparison
is identity on sections. Its inverse-image mate, after exact localization, gives the
proper restriction comparison; the corresponding open mate is exact already on sheaves.
Paste these to obtain d. Scalar adjunction defines q with transpose F(eta) followed by
d inverse. Geometric transposition and compatibility of composite counits identify
this with proper coefficient projection followed by the open balancing comparison.
Evaluation preserves those normalized transposes, so its level is precisely the
published D_n-linear compactScalarMap. After restriction to C_n, compatibility of the
geometric counits identifies it with the ordinary unbounded tensor projection with
constant D_n coefficients. That projection is invertible. Exact coefficient restriction
reflects isomorphisms, so each D_n-linear map is invertible. Evaluations jointly detect
isomorphisms of derived systems, proving invertibility of q. The identical construction
without the sequence direction proves the single-ring assertion.
For composition, the proper projections obey the geometric-counit cocycle. The two
open comparison words have the same composite-adjunction transpose, hence agree.
The normalized scalar adjunctions give the balanced associator: successive pure tensors
map to the tensor with the product of their scalar factors. Substitute the proper/open
word for q and apply naturality to paste those two cocycles. The scalar triangle identity
proves the displayed unit equation. For a commutative coefficient square, both paths
are thereby the map of its common composite, with the canonical associators. All these
are equalities of natural transformations before evaluation, so no faithfulness of
evaluation on derived morphisms is asserted. No flatness, surjectivity of transitions,
cartesianness of systems, or cohomological bounds enter the argument. -/
theorem etaleSystemCoefficientProjection
    (k : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (hl : l.Prime) (hlp : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) :
    ∃ t : Theory c l,
      (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings), IsIso (t.q a)) ∧
      (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings)
        (M : Derived X.left B.rings),
        (t.scalarY a).adjunction.homEquiv _ _ ((t.q a).app M) =
          (t.support B).F.map ((t.scalarX a).adjunction.unit.app M) ≫
            (t.restriction a).iso.inv.app ((t.scalarX a).model.T.obj M)) ∧
      (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
        (M : Derived X.left B.rings),
        (scalarExtension (a.app (op n)).hom Y.left).map
            ((t.supportEvaluation B n).iso.inv.app M) ≫
          (t.scalarEvaluationY a n).iso.inv.app ((t.support B).F.obj M) ≫
          (t.evaluationY C n).E.map ((t.q a).app M) ≫
          (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj M) ≫
          (rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
              ((t.scalarEvaluationX a n).iso.hom.app M) =
          (compactScalarMap (a.app (op n)).hom c).app ((t.evaluationX B n).E.obj M)) ∧
      (∀ (B C D : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings),
        t.q (a ≫ b) = t.path a b) ∧
      (∀ (B : Coefficients.{u} l) (M : Derived X.left B.rings),
        (t.q (𝟙 B.rings)).app M ≫
          (t.support B).F.map ((unit X.left B.rings (t.scalarX (𝟙 B.rings))).hom.app M) =
        (unit Y.left B.rings (t.scalarY (𝟙 B.rings))).hom.app ((t.support B).F.obj M)) ∧
      (∀ (B C D H : Coefficients.{u} l) (a : B.rings ⟶ C.rings)
        (b : C.rings ⟶ H.rings) (d : B.rings ⟶ D.rings) (e : D.rings ⟶ H.rings),
        a ≫ b = d ≫ e → HEq (t.path a b) (t.path d e)) ∧
      (∀ (A B : CommRingCat.{u + 1}) (_hA : Finite A) (_hB : Finite B)
        (_htA : ∃ m : ℕ, (l ^ m : A) = 0) (_htB : ∃ m : ℕ, (l ^ m : B) = 0)
        (a : A ⟶ B),
        IsIso (compactScalarMap a.hom c) ∧
        ∃ d : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⋙
            Sheaf.derivedRestrictScalars Y.left.smallEtaleTopology a.hom ≅
          Sheaf.derivedRestrictScalars X.left.smallEtaleTopology a.hom ⋙
            rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c,
          d.hom = singleRestriction a c ∧
          ∀ M : DerivedCategoryModule A X.left,
            (Adjunction.ofIsRightAdjoint
              (Sheaf.derivedRestrictScalars Y.left.smallEtaleTopology a.hom)).homEquiv
                _ _ ((compactScalarMap a.hom c).app M) =
              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
                ((Adjunction.ofIsRightAdjoint
                  (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology a.hom)).unit.app M) ≫
                d.inv.app ((scalarExtension a.hom X.left).obj M)) ∧
      (∀ (A B D : CommRingCat.{u + 1}) (_hA : Finite A) (_hB : Finite B)
        (_hD : Finite D) (_htA : ∃ m : ℕ, (l ^ m : A) = 0)
        (_htB : ∃ m : ℕ, (l ^ m : B) = 0) (_htD : ∃ m : ℕ, (l ^ m : D) = 0)
        (a : A ⟶ B) (b : B ⟶ D),
        compactScalarMap (a ≫ b).hom c = singlePath a b c) := by
  have _ := hl
  have _ := hlp
  obtain ⟨t⟩ := etaleSystemProjectionTheory_nonempty c l
  obtain ⟨hcomp, hunit⟩ := etaleSystemProjection_coherence c l t
  obtain ⟨hsingle, hsingleComp⟩ := etaleSingleCoefficientProjection c l
  refine ⟨t, ?_, ?_, etaleSystemProjection_evaluation c l t, hcomp, hunit,
    ?_, ?_, hsingleComp⟩
  · intro B C a
    exact projection_isIso t a
  · intro B C a M
    exact projection_transpose t a M
  · intro B C D H a b d e h
    rw [← hcomp B C H a b, ← hcomp B D H d e]
    exact congr_arg_heq (fun g : B.rings ⟶ H.rings ↦ t.q g) h
  · intro A B hA hB htA htB a
    have := hA
    exact ⟨compact_scalar_isIso a.hom c, hsingle A B hA hB htA htB a⟩

end AlgebraicGeometry.Etale.SystemProjection
