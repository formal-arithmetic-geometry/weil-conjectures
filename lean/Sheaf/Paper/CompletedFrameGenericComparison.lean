/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.NormalGenericLisseCocycle
public import Sheaf.Paper.CompleteGroupTorsorMonodromy
public import Sheaf.GroupTheory.CompleteNonarchimedeanMatrixGroup
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.AlgebraicGeometry.FundamentalGroup.NormalSchemeGaloisInertiaPresentation
import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Completed frame torsors and generic descent

Source: the coefficient-completion/frame comparison in the framework of
Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10, pp. 70--71.
(blueprint: lem-sfb-completed-frame-generic-comparison).

The sectionwise frame identifications below specify both restriction and right action.
The point is the image of an original local frame whose generic columns are the chosen
basis. Thus neither the frame torsor nor its point is an arbitrary torsor with a given
representation. All matrices use the incremental Cech convention of FieldSeparableCech.

## Main definitions and statement

* `Frame`, `column` and `scale` use the recorded internal/sectionwise equivalence.
* `toGeneric` is the actual inverse-image unit evaluated on a generic lift.
* `IsFramePresentation` specifies restriction and the right precomposition action.
* `completed_frame_generic_comparison` states the comparison and continuous descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
open UniformSpace
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CompletedFrameGeneric

variable (X : Scheme.{u}) (A : Type u) [NormedField A]

/-- The existing sectionwise ring of the pulled-back all-continuous internal ring.
Source: HRS, Example 3.1; Bhatt--Scholze 7.4.7, frame construction.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
abbrev ring : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (coefficientRing X (normContinuousRing A)).X)

/-- The recorded internal/sectionwise functor, used without replacing the module object.
Source: HRS, Example 3.1; Bhatt--Scholze 7.4.7, frame construction.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
abbrev sectionModule
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientRing X (normContinuousRing A)).X) :=
  (InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (coefficientRing X (normContinuousRing A)).X).obj M

/-- Actual frames on the slice site, with the free module supplied by Mathlib.
Source: Bhatt--Scholze 7.4.7, N viewed as its frame torsor.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
abbrev Frame
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientRing X (normContinuousRing A)).X) (n : ℕ) (U : X.ProEt) :=
  SheafOfModules.free (R := (ring X A).over U) (ULift.{u + 1} (Fin n)) ≅
    (sectionModule X A M).over U

/-- A column of a frame at an object of the slice, obtained by evaluating its free generator.
Source: Bhatt--Scholze 7.4.7, precomposition action on frames.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
def column
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientRing X (normContinuousRing A)).X}
    {n : ℕ} {U : X.ProEt} (e : Frame X A M n U) (i : Fin n) (V : Over U) :
    M.X.obj.obj (op V.left) :=
  ((SheafOfModules.ιFree (ULift.up i) ≫ e.hom).val.app (op V))
    (1 : (ring X A).obj.obj (op V.left))

/-- The canonical unit for internal modules, with coefficient parameters kept explicit.
Source: the recorded internal-module inverse image; Bhatt--Scholze 7.4.7.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
def restrictionUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    M ⟶ (CondensedRing.lowerStar Λ f).obj ((CondensedRing.upperStar Λ f).obj M) :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M

/-- Restriction to the separable-closure sections is the actual module-adjunction unit,
followed by restriction along the specified lift to the base-changed object.
Source: Bhatt--Scholze 7.4.7; the generic-section normalization.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
def toGeneric [IsIntegral X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ks : Type u) [Field ks] [Algebra X.functionField ks]
    [IsSepClosure X.functionField ks]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U : X.ProEt) (t : Spec (.of ks) ⟶ U.left)
    (ht : t ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap X.functionField ks)) ≫
      NormalGenericLisse.genericMap X) :
    M.X.obj.obj (op U) →
      ((CondensedRing.upperStar Λ (NormalGenericLisse.genericMap X)).obj M).X.obj.obj
        (op (FieldSeparableCech.closureObject X.functionField ks)) :=
  fun s ↦ ((CondensedRing.upperStar Λ (NormalGenericLisse.genericMap X)).obj M).X.obj.map
    (MorphismProperty.Over.homMk
      (pullback.lift t (Spec.map (CommRingCat.ofHom (algebraMap X.functionField ks))) ht)
      (pullback.lift_snd _ _ _)).op
    ((restrictionUnit Λ (NormalGenericLisse.genericMap X) M).hom.hom.app (op U) s)

/-- Ordinary internal scalar extension along the isometric completion inclusion.
Source: the completion specialization of ordinary coefficient change in HRS Example 3.1.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
abbrev completed
    (L : NormContinuousLisse A X) :=
  (normContinuousExtension X (Completion.coeRingHom : A →+* Completion A)
    Completion.continuous_coeRingHom).obj L.obj

/-- The structural group is the usual matrix group, lifted only to the torsor universe.
Completeness is for the two-sided uniformity. Both supplied proofs are conclusions of
complete_nonarchimedean_matrix_group, not additional hypotheses on the coefficient field.
Source: Bhatt--Scholze 7.1.5 and the nonarchimedean matrix-group lemma.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
def group (n : ℕ)
    (hN : NonarchimedeanGroup (ULift.{u + 1} (Matrix.GeneralLinearGroup (Fin n) (Completion A))))
    (hC : @CompleteSpace (ULift.{u + 1} (Matrix.GeneralLinearGroup (Fin n) (Completion A)))
      (IsTopologicalGroup.leftUniformSpace _ ⊓ IsTopologicalGroup.rightUniformSpace _)) :
    TorsorCoefficientGroup.{u} where
  carrier := ULift.{u + 1} (Matrix.GeneralLinearGroup (Fin n) (Completion A))
  group := inferInstance
  topology := inferInstance
  hausdorff := inferInstance
  nonarchimedean := hN
  complete := Or.inr hC

/-- Sectionwise scalar multiplication from the recorded internal/sectionwise equivalence.
Source: HRS Example 3.1, action on frame columns.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
def scale
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientRing X (normContinuousRing A)).X)
    (V : X.ProEt) (a : (ring X A).obj.obj (op V)) (v : M.X.obj.obj (op V)) :
    M.X.obj.obj (op V) :=
  @SMul.smul _ ((sectionModule X A M).val.obj (op V))
    (ModuleCat.isModule ((sectionModule X A M).val.obj (op V))).toSMul a v

/-- Section identifications with actual frames, natural on every further slice object.
The action formula is column multiplication by the continuous matrix on the right.
Its coefficients are tested against the canonical continuous-ring comparison; hence
it uses the original pulled-back coefficient ring, not a newly chosen ring isomorphism.
Source: Bhatt--Scholze 7.4.7, frame action; HRS Example 3.1.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
def IsFramePresentation (n : ℕ)
    (G : TorsorCoefficientGroup.{u})
    (eG : G.carrier ≃ₜ* ULift.{u + 1} (Matrix.GeneralLinearGroup (Fin n) A))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientRing X (normContinuousRing A)).X)
    (P : ContinuousRightTorsor X G)
    (e : ∀ U : X.ProEt, P.sheaf.obj.obj (op U) ≃ Frame X A M n U) : Prop :=
  (∀ (U V : X.ProEt) (f : V ⟶ U) (s : P.sheaf.obj.obj (op U))
      (i : Fin n) (W : Over V),
    column X A (e V (P.sheaf.obj.map f.op s)) i W =
      column X A (e U s) i ((Over.map f).obj W)) ∧
  ∀ (U : X.ProEt) (s : P.sheaf.obj.obj (op U)) (g : C(U.left, G.carrier))
      (V : Over U) (c : Matrix (Fin n) (Fin n) ((ring X A).obj.obj (op V.left))),
    (∀ (i j : Fin n) (z : V.left.left),
      ((ContinuousRingUniverse.comparison X A).hom.app (op V.left) (c i j)).down z =
        ((eG (g (V.hom.left.base z))).down : Matrix (Fin n) (Fin n) A) i j) →
    ∀ j : Fin n,
      column X A (e U (P.act (op U) s g)) j V =
        ∑ i : Fin n, scale X A M V.left (c i j) (column X A (e U s) i V)

/-- The generic cocycle in the chosen basis is the matrix of the normalized actual
Galois action on the section fibre. This is the convention pr2*e = pr1*e c.
Source: FieldSeparableCech and the normalized generic-section functor.
(blueprint: lem-sfb-completed-frame-generic-comparison). -/
abbrev matrix [IsIntegral X] (ks : Type u) [Field ks]
    [Algebra X.functionField ks] [IsSepClosure X.functionField ks]
    (F : NormalGenericLisse.FiberFunctor X A ks) (L : NormContinuousLisse A X)
    (n : ℕ) (b : Module.Basis (Fin n) A (F.functor.obj L).obj.V)
    (g : ks ≃ₐ[X.functionField] ks) : Matrix (Fin n) (Fin n) A :=
  LinearMap.toMatrix b b ((F.functor.obj L).obj.ρ g)

/-- The completed frame torsor has exactly the embedded generic cocycle, without inversion;
the original cocycle therefore descends uniquely and continuously, including on all arrows.
Source: the agent coefficient-completion comparison in the framework of Bhatt--Scholze
7.4.7 and 7.4.10, pp. 70--71.
(blueprint: lem-sfb-completed-frame-generic-comparison).

Proof, following the seven steps of the node:
1. Completion is an injective isometry. The completed matrix group is Hausdorff,
   nonarchimedean and two-sided complete, including in rank zero. Integral X is connected;
   quasi-compact locally Noetherian X is a normal Noetherian torsor base.
2. Apply lem-sfb-generic-lisse-scalar-comparison to the completion inclusion: ordinary
   extension preserves lisseness and rank, and sends every generic matrix entry to its image.
3. The canonical continuous-function realization identifies invertible coefficient matrices
   with continuous GL-valued functions. Locally, frames are e h, and (e h)h'=e(hh').
   This gives the displayed slice-frame identifications, restriction and right action.
4. Lift the chosen generic basis to an original local frame, and extend its columns by
   the scalar-extension unit. In Cech coordinates pr2*p=pr1*p iota(c), with no inverse.
   Its geometric restriction is the point specified by sectionToFibre below.
5. Pullback naturality and the field normalization of complete_group_torsor_monodromy
   identify this Cech cocycle with tau composed with the canonical generic q.
6. The normal integral Galois-presentation theorem makes q surjective. Injectivity of
   completion shows that the generic cocycle kills ker q. Lift elements through q;
   independence of the lift gives its unique multiplicative factor.
7. Entrywise completion is a topological embedding. Thus the cocycle is continuous.
   A continuous surjection from a compact space to a Hausdorff space is a quotient map,
   so its factor is continuous. Surjectivity of q also identifies both intertwiner
   equations for every rectangular matrix. Empty dimensions give the same equations. -/
theorem completed_frame_generic_comparison
    (B : NormalTorsorBase.{u}) [IsIntegral B.X]
    (ks : Type u) [Field ks] [Algebra B.X.functionField ks]
    [IsSepClosure B.X.functionField ks] [Algebra ks B.Ω] [IsAlgClosure ks B.Ω]
    [Algebra B.X.functionField B.Ω] [IsScalarTower B.X.functionField ks B.Ω]
    (hx : B.x = Spec.map (CommRingCat.ofHom (algebraMap B.X.functionField B.Ω)) ≫
      NormalGenericLisse.genericMap B.X)
    (q : (ks ≃ₐ[B.X.functionField] ks) →* B.pi)
    (hq : ∀ (g : ks ≃ₐ[B.X.functionField] ks) (gbar : B.Ω ≃ₐ[B.X.functionField] B.Ω),
      (∀ a : ks, gbar (algebraMap ks B.Ω a) = algebraMap ks B.Ω (g a)) →
        q g = Scheme.FiniteEtale.galoisToFundamentalGroup
          (NormalGenericLisse.genericMap B.X) (eqToIso (congrArg Scheme.FiniteEtale.fiber hx.symm))
            B.pi gbar)
    (A : Type u) [NormedField A]
    (hA : ∀ x y : A, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (F : NormalGenericLisse.FiberFunctor B.X A ks) (hF : F.IsNormalized) :
    ∀ (n : ℕ) (L : NormContinuousLisse A B.X)
      (b : Module.Basis (Fin n) A (F.functor.obj L).obj.V),
    IsLisseCoefficientModule (normContinuousRing (Completion A)).X (completed B.X A L) ∧
    (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage B.X, ∀ i : U.I₀,
      Nonempty ((CondensedRing.upperStar (normContinuousRing (Completion A)).X (U.f i)).obj
        (completed B.X A L) ≅
          Mod.finiteFree (coefficientRing (U.X i) (normContinuousRing (Completion A))).X n)) ∧
    ∃ hN : NonarchimedeanGroup
        (ULift.{u + 1} (Matrix.GeneralLinearGroup (Fin n) (Completion A))),
    ∃ hC : @CompleteSpace (ULift.{u + 1} (Matrix.GeneralLinearGroup (Fin n) (Completion A)))
        (IsTopologicalGroup.leftUniformSpace _ ⊓ IsTopologicalGroup.rightUniformSpace _),
    ∃ (P : ContinuousRightTorsor B.X (group A n hN hC))
      (e : ∀ U : B.X.ProEt, P.sheaf.obj.obj (op U) ≃
        Frame B.X (Completion A) (completed B.X A L) n U),
      IsFramePresentation B.X (Completion A) n (group A n hN hC) (.refl _)
        (completed B.X A L) P e ∧
      ∃ (U : B.X.ProEt) (t : Spec (.of ks) ⟶ U.left)
        (ht : t ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap B.X.functionField ks)) ≫
          NormalGenericLisse.genericMap B.X)
        (eA : Frame B.X A L.obj n U) (s : P.sheaf.obj.obj (op U))
        (tbar : Spec (.of B.Ω) ⟶ U.left) (htbar : tbar ≫ U.hom = B.x),
        tbar = Spec.map (CommRingCat.ofHom (algebraMap ks B.Ω)) ≫ t ∧
        (∀ i : Fin n,
          HEq (toGeneric B.X (normContinuousRing A).X ks L.obj U t ht
            (column B.X A eA i (Over.mk (𝟙 U)))) (F.sections L (b i))) ∧
        (∀ (i : Fin n) (V : Over U),
          column B.X (Completion A) (e U s) i V =
            (Mod.extendUnitHom
              (normContinuousCoefficientMap B.X
                (Completion.coeRingHom : A →+* Completion A)
                Completion.continuous_coeRingHom) L.obj).hom.app (op V.left)
                  (column B.X A eA i V)) ∧
        (∀ g : ks ≃ₐ[B.X.functionField] ks,
          (((Classical.choose (complete_group_torsor_monodromy.{u})) B
            (group A n hN hC) P (P.sectionToFibre B.x U tbar htbar s) (q g)).down :
              Matrix (Fin n) (Fin n) (Completion A)) =
            (matrix B.X A ks F L n b g).map Completion.coeRingHom) ∧
        (∀ g : ks ≃ₐ[B.X.functionField] ks, q g = 1 → matrix B.X A ks F L n b g = 1) ∧
        (∃! r : B.pi →ₜ* Matrix.GeneralLinearGroup (Fin n) A,
          ∀ g : ks ≃ₐ[B.X.functionField] ks,
            (r (q g) : Matrix (Fin n) (Fin n) A) = matrix B.X A ks F L n b g) ∧
        ∀ (m : ℕ) (M : NormContinuousLisse A B.X)
          (d : Module.Basis (Fin m) A (F.functor.obj M).obj.V)
          (r : B.pi →ₜ* Matrix.GeneralLinearGroup (Fin n) A)
          (r' : B.pi →ₜ* Matrix.GeneralLinearGroup (Fin m) A),
          (∀ g, (r (q g) : Matrix (Fin n) (Fin n) A) = matrix B.X A ks F L n b g) →
          (∀ g, (r' (q g) : Matrix (Fin m) (Fin m) A) = matrix B.X A ks F M m d g) →
          ∀ T : Matrix (Fin m) (Fin n) A,
            (∀ g, T * matrix B.X A ks F L n b g = matrix B.X A ks F M m d g * T) ↔
              ∀ h : B.pi, T * (r h : Matrix (Fin n) (Fin n) A) =
                (r' h : Matrix (Fin m) (Fin m) A) * T := by
  sorry

end AlgebraicGeometry.ProEtale.CompletedFrameGeneric
