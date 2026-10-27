/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.Paper.TorsorAssociatedModulePresentation
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.Galois.AutProfinite
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Lisse modules associated to compact continuous-function torsors

Source: the associated-module expansion of Bhatt--Scholze, Lemma 7.4.7, p. 70,
and Lemma 7.4.10, p. 71, with Stacks Tags 04TR and 04TQ.
(blueprint: lem-sfb-compact-torsor-associated-lisse).

All coefficients are all continuous functions with the norm topology; neither
completeness nor local compactness is assumed for the original normed field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.TorsorAssociatedModule
open CompletedFrameGeneric

/-- Constant rank n is witnessed on an actual pro-etale cover by internal free modules.
Source: Bhatt--Scholze, Lemma 7.4.7, associated-module construction.
(blueprint: lem-sfb-compact-torsor-associated-lisse). -/
def HasRank {X : Scheme.{u}} {A : Type u} [NormedField A]
    (L : NormContinuousLisse A X) (n : ℕ) : Prop :=
  ∃ U : Scheme.Cover.{u} (Scheme.proetalePrecoverage) X,
    ∀ i, Nonempty ((CondensedRing.upperStar (normContinuousRing A).X (U.f i)).obj L.obj ≅
      Mod.finiteFree (coefficientRing (U.X i) (normContinuousRing A)).X n)

/-- Completion gives the actual frame torsor, with the universal contracted product,
its induced point, extended local columns, extended generic basis, and cocycle.
Source: Bhatt--Scholze, Lemma 7.4.7, coefficient completion and frames.
(blueprint: lem-sfb-compact-torsor-associated-lisse). -/
def CompletionAssertions
    (B : NormalTorsorBase.{u}) [IsIntegral B.X]
    (ks : Type u) [Field ks] [Algebra B.X.functionField ks]
    [IsSepClosure B.X.functionField ks]
    (q : (ks ≃ₐ[B.X.functionField] ks) →* B.pi)
    {A : Type u} [NormedField A] {H : TorsorCoefficientGroup.{u}} {n : ℕ}
    (r : H.carrier →ₜ* Matrix.GeneralLinearGroup (Fin n) A)
    (θ : B.pi →ₜ* H.carrier) (P : ContinuousRightTorsor B.X H) (p : P.fibre B.x)
    (L : NormContinuousLisse A B.X) (a : Presentation r P L)
    (b : Module.Basis (Fin n) A (NormalGenericLisse.geometricSections B.X A ks L)) : Prop :=
  ∃ hN : NonarchimedeanGroup
      (ULift.{u + 1} (Matrix.GeneralLinearGroup (Fin n) (UniformSpace.Completion A))),
  ∃ hC : @CompleteSpace
      (ULift.{u + 1} (Matrix.GeneralLinearGroup (Fin n) (UniformSpace.Completion A)))
      (IsTopologicalGroup.leftUniformSpace _ ⊓ IsTopologicalGroup.rightUniformSpace _),
  ∃ (rF : H.carrier →ₜ* Matrix.GeneralLinearGroup (Fin n) (UniformSpace.Completion A))
    (s : H.carrier →ₜ* (group A n hN hC).carrier),
    (∀ h, rF h = Matrix.GeneralLinearGroup.map
      (UniformSpace.Completion.coeRingHom : A →+* UniformSpace.Completion A) (r h)) ∧
    (∀ h, (s h).down = rF h) ∧
    ∃ (Q : ContinuousRightTorsor B.X (group A n hN hC))
      (e : ∀ U : B.X.ProEt, Q.sheaf.obj.obj (op U) ≃
        Frame B.X (UniformSpace.Completion A) (completed B.X A L) n U)
      (E : ContinuousRightTorsor.ExtensionPresentation s P Q)
      (aF : Presentation rF P
        ((GenericLisseScalar.extension B.X
          (UniformSpace.Completion.coeRingHom : A →+* UniformSpace.Completion A)
          UniformSpace.Completion.continuous_coeRingHom).obj L)),
      IsFramePresentation B.X (UniformSpace.Completion A) n (group A n hN hC) (.refl _)
        (completed B.X A L) Q e ∧
      (∀ (U : B.X.ProEt) (z : P.sheaf.obj.obj (op U)),
        HEq (e U (E.quotientMap (op U) z 1)) (aF.frame U z)) ∧
      (∀ (U : B.X.ProEt) (z : P.sheaf.obj.obj (op U)) (i : Fin n) (V : Over U),
        column B.X (UniformSpace.Completion A) (aF.frame U z) i V =
          (GenericLisseScalar.baseUnit B.X
            (UniformSpace.Completion.coeRingHom : A →+* UniformSpace.Completion A)
            UniformSpace.Completion.continuous_coeRingHom L).hom.app (op V.left)
              (column B.X A (a.frame U z) i V)) ∧
      HasRank ((GenericLisseScalar.extension B.X
        (UniformSpace.Completion.coeRingHom : A →+* UniformSpace.Completion A)
        UniformSpace.Completion.continuous_coeRingHom).obj L) n ∧
      ∃ bF : Module.Basis (Fin n) (UniformSpace.Completion A)
        (NormalGenericLisse.geometricSections B.X (UniformSpace.Completion A) ks
          ((GenericLisseScalar.extension B.X
            (UniformSpace.Completion.coeRingHom : A →+* UniformSpace.Completion A)
            UniformSpace.Completion.continuous_coeRingHom).obj L)),
        (∀ i, HEq (bF i) (GenericLisseScalar.unit B.X ks
          (UniformSpace.Completion.coeRingHom : A →+* UniformSpace.Completion A)
          UniformSpace.Completion.continuous_coeRingHom L (b i))) ∧
        (∀ (g : ks ≃ₐ[B.X.functionField] ks) (i j : Fin n),
          bF.repr (GenericLisseScalar.action B.X ks _ g (bF j)) i =
            UniformSpace.Completion.coeRingHom
              ((r (θ (q g)) : Matrix (Fin n) (Fin n) A) i j)) ∧
        ∀ g : ks ≃ₐ[B.X.functionField] ks,
          (((Classical.choose (complete_group_torsor_monodromy.{u})) B
            (group A n hN hC) Q (E.fibreMap B.x p) (q g)).down :
              Matrix (Fin n) (Fin n) (UniformSpace.Completion A)) =
            rF (θ (q g))

/-- Rank, uniqueness relative to every chart, pointed generic basis and completion.
Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10; Stacks Tag 04TQ.
(blueprint: lem-sfb-compact-torsor-associated-lisse). -/
def Realization
    (B : NormalTorsorBase.{u}) [IsIntegral B.X]
    (ks : Type u) [Field ks] [Algebra B.X.functionField ks]
    [IsSepClosure B.X.functionField ks] [Algebra ks B.Ω]
    (q : (ks ≃ₐ[B.X.functionField] ks) →* B.pi)
    {A : Type u} [NormedField A] {H : TorsorCoefficientGroup.{u}} {n : ℕ}
    (r : H.carrier →ₜ* Matrix.GeneralLinearGroup (Fin n) A)
    (θ : B.pi →ₜ* H.carrier) (P : ContinuousRightTorsor B.X H) (p : P.fibre B.x)
    (L : NormContinuousLisse A B.X) (a : Presentation r P L) : Prop :=
  HasRank L n ∧
  (∀ (M : NormContinuousLisse A B.X) (d : Presentation r P M),
    ∃! e : L.obj ≅ M.obj, Respects a d e) ∧
  ∃ b : Module.Basis (Fin n) A (NormalGenericLisse.geometricSections B.X A ks L),
    IsPointedBasis ks B.Ω (algebraMap ks B.Ω) B.x a p (fun j ↦ b j) ∧
    (∀ (g : ks ≃ₐ[B.X.functionField] ks) (i j : Fin n),
      b.repr (GenericLisseScalar.action B.X ks L g (b j)) i =
        (r (θ (q g)) : Matrix (Fin n) (Fin n) A) i j) ∧
    CompletionAssertions B ks q r θ P p L a b

/-- A compact continuous right torsor yields its associated lisse module, uniquely
relative to the associated-module identification. Its pointed generic matrix is r θ q;
completion gives the universal extension and the actual frame torsor. Every continuous
representation is covered by taking its actual compact image with the subspace topology.
Source: associated-module expansion of Bhatt--Scholze 7.4.7, p. 70, and 7.4.10, p. 71.
(blueprint: lem-sfb-compact-torsor-associated-lisse).

Proof, following the seven DAG steps:
1. Ultrametric balls make A totally disconnected. The canonical continuous-field
   comparison realizes the coefficient ring as all continuous functions. The recorded
   internal/section-module equivalence identifies maps of finite free modules with
   matrices; continuity of matrix inversion identifies automorphisms with GL-functions.
2. Choose local torsor sections p_i. Their translations obey h_ik=h_ij h_jk. Glue the
   free modules with inverse coordinate changes r(h_ij)^(-1), by site module gluing.
   The resulting frames obey e_j=e_i r(h_ij). Module gluing descends addition and action.
3. Define the frame for p_i a by e_i r(a). The torsor relation makes it independent
   of charts and gives [ph,v]=[p,r(h)v]. Set-sheaf map descent on common refinements
   gives the unique chart-preserving linear comparison, including its composition law.
4. Pull back to the generic point. Torsor pullback naturality and field normalization
   identify its Cech translation with θ q. Pullback preserves finite free frames, and
   separable-field coordinates give the basis from p. The positive right-frame equation
   e_2=e_1 r(θ q) gives precisely the displayed generic action, with no inverse.
5. The completion inclusion is an isometric field homomorphism. Generic scalar
   comparison extends the basis and every transition entry. The complete matrix-group
   lemma gives the Hausdorff nonarchimedean two-sided complete structural group. The
   actual sheaf of frames, with right precomposition, is its continuous-function torsor.
6. The balanced map (p,a) ↦ e_(p,F) a identifies this frame torsor with the contracted
   product. Locally any balanced map is forced by its value at p_i; overlap agreement
   and set-sheaf descent prove the universal property for arbitrary target set sheaves.
   The induced point is [p,1]; its monodromy and generic matrix are iota_* r θ q.
7. The etale fundamental group is profinite. The actual image of rho is compact and
   Hausdorff with the subspace topology; completion embeds GL_n(A) into GL_n(F).
   Intersections with the small matrix subgroups give its open-subgroup basis. Apply
   torsor classification and steps 1--6 to inclusion r and corestriction θ. Empty free
   modules, incomplete fields, trivial norms and nonfaithful r require no exclusions. -/
theorem compact_torsor_associated_lisse
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
    (hA : ∀ x y : A, ‖x + y‖ ≤ max ‖x‖ ‖y‖) :
    (∀ (H : TorsorCoefficientGroup.{u}) (_hH : CompactSpace H.carrier) (n : ℕ)
      (r : H.carrier →ₜ* Matrix.GeneralLinearGroup (Fin n) A)
      (θ : B.pi →ₜ* H.carrier) (P : ContinuousRightTorsor B.X H) (p : P.fibre B.x),
      (Classical.choose (complete_group_torsor_monodromy.{u})) B H P p = θ →
      ∃ (L : NormContinuousLisse A B.X) (a : Presentation r P L),
        Realization B ks q r θ P p L a) ∧
    ∀ (n : ℕ) (ρ : B.pi →ₜ* Matrix.GeneralLinearGroup (Fin n) A),
      ∃ (H : TorsorCoefficientGroup.{u}) (_hH : CompactSpace H.carrier)
        (eH : H.carrier ≃ₜ* ULift.{u + 1} ρ.toMonoidHom.range)
        (r : H.carrier →ₜ* Matrix.GeneralLinearGroup (Fin n) A)
        (θ : B.pi →ₜ* H.carrier),
        (∀ h, r h = (eH h).down.val) ∧
        (∀ γ, (eH (θ γ)).down.val = ρ γ) ∧
        ∃ (P : ContinuousRightTorsor B.X H) (p : P.fibre B.x),
          (Classical.choose (complete_group_torsor_monodromy.{u})) B H P p = θ ∧
          ∃ (L : NormContinuousLisse A B.X) (a : Presentation r P L),
            Realization B ks q r θ P p L a ∧
            ∃ b : Module.Basis (Fin n) A (NormalGenericLisse.geometricSections B.X A ks L),
              IsPointedBasis ks B.Ω (algebraMap ks B.Ω) B.x a p (fun j ↦ b j) ∧
              ∀ (g : ks ≃ₐ[B.X.functionField] ks) (i j : Fin n),
                b.repr (GenericLisseScalar.action B.X ks L g (b j)) i =
                  (ρ (q g) : Matrix (Fin n) (Fin n) A) i j := by
  sorry

end AlgebraicGeometry.ProEtale.TorsorAssociatedModule
