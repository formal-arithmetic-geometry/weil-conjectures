/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits
import Sheaf.TraceFormula.ProjectiveBundleProper
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.TraceFormula.SmoothCurveSectionCartier
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.FppfLocalOpenSubfunctorDescent
import Sheaf.AlgebraicGeometry.Modules.ZeroLocusPullback
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison

/-!
# A relative nonspecial Abel chart through a prescribed divisor

Source: Deligne, Le lemme de Gabber, Lemma 4.5, printed p.143
(blueprint: lem-sfb-relative-abel-nonspecial-chart).

The helpers specialize existing Hilbert points, divisor lines, module cohomology,
and the canonical evaluation and base-change maps. Algebraic-space sections are
lifted when compared with the larger universe of the existing Picard functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.RelativeAbelChart

/-- Module cohomology over a field, with scalars restricted along the structural map.
Source: Deligne 4.5, p.143 (blueprint: lem-sfb-relative-abel-nonspecial-chart). -/
noncomputable def cohomology {K : Type u} [Field K] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of K)) (M : Y.Modules) (q : ℕ) : ModuleCat.{u} K :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom).obj
    ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj M)

/-- The fixed-degree Hilbert points supported in the smooth locus, with their Cartier
property. This is the relative divisor parameter functor on objects.
Source: Deligne 4.5, p.143 (blueprint: lem-sfb-relative-abel-nonspecial-chart). -/
def Divisor {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (d : ℕ) (T : Over S) :=
  {D : (hilbertPresheaf f d).obj (op T) // D.1.IsInvertible ∧
    ∀ z : D.1.subscheme, D.1.subschemeι z ∈ (pullback.snd f T.hom).smoothLocus}

/-- The Picard class of the dual ideal of a Cartier divisor.
Source: Deligne 4.5, p.143 (blueprint: lem-sfb-relative-abel-nonspecial-chart). -/
noncomputable def lineClass {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (hD : D.IsInvertible) : Y.Pic :=
  @Scheme.Pic.ofIsInvertible Y D.toModulesᵛ hD.isInvertible_dual_toModules

/-- Pull the extended relative divisor back to an arbitrary test over the neighbourhood.
Source: Deligne 4.5, p.143 (blueprint: lem-sfb-relative-abel-nonspecial-chart). -/
noncomputable def testDivisor {X S S' : Scheme.{u}} (f : X ⟶ S) (h : S' ⟶ S)
    (E : (pullback f h).IdealSheafData) (T : Over S') :
    (pullback f (T.hom ≫ h)).IdealSheafData :=
  E.comap (baseChangeMap f (Over.homMk T.hom : (Over.map h).obj T ⟶ Over.mk h))

/-- The class O(E_T), using the existing arbitrary pullback theorem for relative Cartier
ideals; no new choice of a line bundle is made.
Source: Deligne 4.5, p.143 (blueprint: lem-sfb-relative-abel-nonspecial-chart). -/
noncomputable def testLineClass {X S S' : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] (h : S' ⟶ S)
    (E : (pullback f h).IdealSheafData)
    (hE : E.IsRelativeEffectiveCartier (pullback.snd f h)) (T : Over S') :
    (pullback f (T.hom ≫ h)).Pic :=
  lineClass (testDivisor f h E T)
    (hE.isRelativeEffectiveCartier_comap_of_isPullback
      (isPullback_baseChangeMap f
        (Over.homMk T.hom : (Over.map h).obj T ⟶ Over.mk h))).1

/-- The actual line L(E_T), formed from the representative already used by Pic.
Source: Deligne 4.5, p.143 (blueprint: lem-sfb-relative-abel-nonspecial-chart). -/
noncomputable def twist {X S S' : Scheme.{u}} (f : X ⟶ S) (h : S' ⟶ S)
    (E : (pullback f h).IdealSheafData) (T : Over S')
    (L : (pullback f (T.hom ≫ h)).Pic) : (pullback f (T.hom ≫ h)).Modules :=
  (fromSkeleton _).obj L.val ⊗ (testDivisor f h E T).toModulesᵛ

/-- Evaluation is the counit of the canonical tensor-pullback/direct-image adjunction.
Source: Deligne 4.5, p.143 (blueprint: lem-sfb-relative-abel-nonspecial-chart). -/
noncomputable def evaluation {Y T : Scheme.{u}} (p : Y ⟶ T) (B : Y.Modules) :
    (Scheme.Modules.tensorPullback p).obj ((Scheme.Modules.pushforward p).obj B) ⟶ B :=
  (Scheme.Modules.tensorPullbackSectionAdjunction p).counit.app B

/-- Arbitrary ordinary base change means invertibility of the existing canonical map,
for every morphism of test schemes, including identity maps and nonflat maps.
Source: Deligne 4.5, p.143 (blueprint: lem-sfb-relative-abel-nonspecial-chart). -/
def UniversalBaseChange {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    (B : (pullback f T.hom).Modules) : Prop :=
  ∀ (T' : Over S) (a : T' ⟶ T),
    IsIso (Scheme.Modules.moduleBaseChangeMap (pullback.snd f T.hom)
      (pullback.snd f T'.hom) a.left (baseChangeMap f a)
      (isPullback_baseChangeMap f a).w B)

/-- The relative nonspecial Abel chart, including the two formulas on arbitrary tests.
Source: Deligne, Le lemme de Gabber, Lemma 4.5, printed p.143
(blueprint: lem-sfb-relative-abel-nonspecial-chart).

Proof in words, following the eight steps of the DAG node:
1. Restrict to an affine Noetherian neighbourhood. Projective-bundle properness and
ampleness of its structure line give a finite projective-space embedding. In the smooth
locus, lift the finitely many prescribed separable points using the etale slicing lemma,
and take the pointed fibre product of these slices. For degree zero take no slices.
2. Remove pairwise section equalizers and take an affine neighbourhood. Separatedness
makes the sections closed; the smooth-curve section criterion makes their disjoint union
Cartier. It is finite locally free of rank g and extends the prescribed divisor. Finite
presentation over a Noetherian affine and open restriction keep the base Noetherian.
3. Proper flat derived base change makes the direct image of L(E) perfect. The rank-one,
degree-zero perfect locus is open; on it H^0 is the ordinary direct image, a line whose
canonical ordinary base-change maps are isomorphisms for every further base change.
4. Apply the finite Cartier zero-divisor open-locus lemma to evaluation and the smooth
locus. The locus and its divisor are invariant under tensoring L by a base line. The
Picard sheafification and fppf open-subfunctor descent therefore give an open V.
5. The prescribed h^0 and h^1, the curve cohomology bound and etale/Zariski comparison
put the identity at the pointed fibre in this open. Its evaluation divisor is E_s by the
canonical Cartier section. Shrink the base along the identity to retain its whole image.
6. The smooth-divisor parameter theorem represents the degree-g functor by a finite-type
scheme H. The map F to O(F-E) is the Abel map. Its inverse over V is evaluation: the
zero-divisor line isomorphism gives L(E) = O(F) tensor f^*N, hence the same Picard class.
7. Conversely the canonical section of O(F) generates its rank-one direct image on each
residue-field fibre, so generates it locally. Evaluation then has precisely zero divisor F.
Both identities hold on arbitrary tests, including classes represented only fppf locally.
8. H is finite type over the Noetherian base. Its open W is Noetherian and quasi-compact,
so the isomorphic V is quasi-compact. For g=0 the divisor is empty and all steps apply. -/
theorem relative_abel_nonspecial_chart {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [Flat f] [LocallyOfFinitePresentation f]
    (hf : IsProjectiveBundle f) (hnodal : HasNodalGeometricFibres f)
    (P : AlgebraicSpace S)
    (eP : P.obj.obj ⋙ uliftFunctor.{u + 1, u} ≅ (picardFunctor f).obj)
    (A : AlgebraicSpace.OpenSubspace P)
    (hA : ∀ T : Over S, ∃ G : Subgroup ((picardFunctorGrp f).obj (op T)),
      ∀ x : P.obj.obj.obj (op T), x ∈ A.val.obj (op T) ↔
        eP.hom.app (op T) (ULift.up x) ∈ G)
    (s : S) (K : Type u) [Field K] [Algebra (S.residueField s) K]
    [IsSepClosure (S.residueField s) K]
    (q : Spec (.of K) ⟶ S)
    (hq : q = Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
      S.fromSpecResidueField s)
    (g : ℕ)
    (hg : g = Module.finrank K (cohomology (pullback.snd f q)
      (𝟙_ (pullback f q).Modules) 1))
    (Es : (pullback f q).IdealSheafData) (hEs : Es.IsInvertible)
    (x : Fin g → (Spec (.of K) ⟶ pullback f q)) (hx : Function.Injective x)
    (hsection : ∀ i : Fin g, x i ≫ pullback.snd f q = 𝟙 _)
    (hsmooth : ∀ (i : Fin g) (z : Spec (.of K)),
      x i z ∈ (pullback.snd f q).smoothLocus)
    (hpoints : Es = ⨅ i : Fin g, (x i).ker)
    (hH1 : Subsingleton (cohomology (pullback.snd f q) Es.toModulesᵛ 1))
    (hH0 : Module.finrank K (cohomology (pullback.snd f q) Es.toModulesᵛ 0) = 1) :
    ∃ (S' : Scheme.{u}) (h : S' ⟶ S) (q' : Spec (.of K) ⟶ S')
      (E : (pullback f h).IdealSheafData)
      (hE : E.IsRelativeEffectiveCartier (pullback.snd f h)) (hq' : q' ≫ h = q),
      Etale h ∧ IsAffine S' ∧ IsNoetherian S' ∧
      E.comap (baseChangeMap f (Over.homMk q' hq' : Over.mk q ⟶ Over.mk h)) = Es ∧
      ∃ (H : Over S')
        (rH : ∀ T : Over S', (T ⟶ H) ≃ Divisor f g ((Over.map h).obj T))
        (W : H.left.Opens)
        (V : Subfunctor ((Over.map h).op ⋙ P.obj.obj))
        (eW : yoneda.obj (Over.mk (W.ι ≫ H.hom)) ≅ V.toFunctor),
        (∀ (T T' : Over S') (a : T' ⟶ T) (b : T ⟶ H),
          (rH T' (a ≫ b)).val.val =
            (rH T b).val.val.comap (baseChangeMap f ((Over.map h).map a))) ∧
        AlgebraicSpace.IsRepresentableWith
          (fun _ _ a ↦ IsOpenImmersion a.left) V.ι ∧
        (∀ (T : Over S') (y : P.obj.obj.obj (op ((Over.map h).obj T))),
          y ∈ V.obj (op T) → y ∈ A.val.obj (op ((Over.map h).obj T))) ∧
        (∀ T : Over S',
          (eP.inv.app (op ((Over.map h).obj T))
            ((toPicardFunctorHom f ((Over.map h).obj T)) 1)).down ∈ V.obj (op T)) ∧
        CompactSpace W.toScheme ∧
        (∀ (T : Over S') (a : T ⟶ Over.mk (W.ι ≫ H.hom)),
          eP.hom.app (op ((Over.map h).obj T))
            (ULift.up (eW.hom.app (op T) a).val) =
          (toPicardFunctorHom f ((Over.map h).obj T))
            (@Mul.mul (pullback f (T.hom ≫ h)).Pic inferInstance
              (lineClass (rH T (a ≫ Over.homMk W.ι)).val.val
                (rH T (a ≫ Over.homMk W.ι)).property.1)
              (testLineClass f h E hE T)⁻¹)) ∧
        (∀ (T : Over S') (a : T ⟶ Over.mk (W.ι ≫ H.hom))
          (L : (pullback f (T.hom ≫ h)).Pic),
          (toPicardFunctorHom f ((Over.map h).obj T)) L =
            eP.hom.app (op ((Over.map h).obj T))
              (ULift.up (eW.hom.app (op T) a).val) →
          ((Scheme.Modules.pushforward (pullback.snd f (T.hom ≫ h))).obj
            (twist f h E T L)).IsInvertible ∧
          UniversalBaseChange f ((Over.map h).obj T) (twist f h E T L) ∧
          (rH T (a ≫ Over.homMk W.ι)).val.val =
            (evaluation (pullback.snd f (T.hom ≫ h)) (twist f h E T L)).zeroLocus) := by
  sorry

end AlgebraicGeometry.RelativeAbelChart
