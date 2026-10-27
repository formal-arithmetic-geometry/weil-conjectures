/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.FieldTheory.PurelyTranscendentalExtension
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

import Sheaf.TraceFormula.ElementaryModuleDevissage
import Sheaf.TraceFormula.ElementaryDevissageFinitePresentation
import Sheaf.TraceFormula.ElementaryDevissageFlatness
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.AffineChartRelativeFlatCriterion
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization

/-!
# Localized elementary dévissage and transfer of neighbourhoods

Source: Stacks Project, flat.tex, Tag 05I5, first proof, localization of the
057S diagram and application of 057T and 057U
(blueprint: lem-trf-localized-devissage-neighborhood-transfer).

`localizedDevissageBaseChangeConclusions` packages the base-change clauses of this
statement. It quantifies over cartesian presentations of the base-changed diagram;
all its comparison maps use the existing tensor pullback and base-change constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The base-change clauses of the localized dévissage statement, for one specified
pointed change of base. The four fibre isomorphisms are pinned by their projections.
The equation for `E'` pins the comparison to the pullback of the original `E` via the
canonical base-change map and section-normalized pullback composition comparisons.

Source: Stacks Project, flat.tex, Tag 05I5, first proof, localized 057S diagram,
and Tags 057T, 057U and 02KG
(blueprint: lem-trf-localized-devissage-neighborhood-transfer). -/
def localizedDevissageBaseChangeConclusions
    {S X X₁ Z Y : Scheme.{u}} (f : X ⟶ S) (f₁ : X₁ ⟶ S)
    (g : X₁ ⟶ X) (i : Z ⟶ X₁) (π : Z ⟶ Y) (h : Y ⟶ S)
    (F : X.Modules) (G : Z.Modules)
    (E : (pushforward i).obj G ≅ (tensorPullback g).obj F)
    (x : X) (z : Z) (s : S) (n : ℕ)
    (R : Scheme.{u}) (c : R ⟶ S) (r : R) : Prop :=
  c r = s ∧ IsIso (c.residueFieldMap r) ∧
  ∀ (X' X₁' Z' Y' : Scheme.{u})
    (p : X' ⟶ X) (p₁ : X₁' ⟶ X₁) (pZ : Z' ⟶ Z) (pY : Y' ⟶ Y)
    (f' : X' ⟶ R) (f₁' : X₁' ⟶ R) (h' : Y' ⟶ R)
    (g' : X₁' ⟶ X') (i' : Z' ⟶ X₁') (π' : Z' ⟶ Y')
    (_sq : IsPullback p f' f c)
    (_sq₁ : IsPullback p₁ f₁' f₁ c)
    (_sqZ : IsPullback pZ (i' ≫ f₁') (i ≫ f₁) c)
    (_sqY : IsPullback pY h' h c)
    (sqg : IsPullback p₁ g' g p)
    (sqi : IsPullback pZ i' i p₁)
    (sqπ : IsPullback pZ π' π pY),
    g' ≫ f' = f₁' → i' ≫ f₁' = π' ≫ h' →
    Etale g' ∧ IsClosedImmersion i' ∧ LocallyOfFinitePresentation i' ∧
    QuasiCompact i' ∧ QuasiSeparated i' ∧ IsFinite π' ∧
    SmoothOfRelativeDimension n h' ∧ GeometricallyIntegral h' ∧
    IsIso (moduleBaseChangeMap i i' p₁ pZ sqi.w G) ∧
    IsIso (moduleBaseChangeMap π π' pY pZ sqπ.w G) ∧
    (∃ E' : (pushforward i').obj ((tensorPullback pZ).obj G) ≅
        (tensorPullback g').obj ((tensorPullback p).obj F),
      moduleBaseChangeMap i i' p₁ pZ sqi.w G ≫ E'.hom =
        (tensorPullback p₁).map E.hom ≫
          ((tensorPullbackSectionComp p₁ g).symm.app F ≪≫
            (eqToIso (congrArg tensorPullback sqg.w)).app F ≪≫
            (tensorPullbackSectionComp g' p).app F).hom) ∧
    (∃ (x' : X') (z' : Z'),
      p x' = x ∧ f' x' = r ∧ pZ z' = z ∧
      g' (i' z') = x' ∧ h' (π' z') = r ∧
      (π' ⁻¹' ({π' z'} : Set Y')) = {z'} ∧
      IsIso (p.residueFieldMap x') ∧ IsIso (p₁.residueFieldMap (i' z')) ∧
      IsIso (pZ.residueFieldMap z') ∧ IsIso (pY.residueFieldMap (π' z')) ∧
      IsIso (g'.residueFieldMap (i' z')) ∧
      ((∃ U : X'.Opens, x' ∈ U ∧
          (((tensorPullback p).obj F).over U).IsFinitePresentation) ↔
        (∃ U : Y'.Opens, π' z' ∈ U ∧
          (((pushforward π').obj ((tensorPullback pZ).obj G)).over U).IsFinitePresentation)) ∧
      ((∃ U : X'.Opens, x' ∈ U ∧
          ((tensorPullback U.ι).obj ((tensorPullback p).obj F)).IsFlatOver (U.ι ≫ f')) ↔
        (∃ U : Y'.Opens, π' z' ∈ U ∧
          ((tensorPullback U.ι).obj
            ((pushforward π').obj ((tensorPullback pZ).obj G))).IsFlatOver (U.ι ≫ h')))) ∧
    (∃ k : f'.fiber r ⟶ f.fiber s,
      IsIso k ∧ k ≫ f.fiberι s = f'.fiberι r ≫ p) ∧
    (∃ k : f₁'.fiber r ⟶ f₁.fiber s,
      IsIso k ∧ k ≫ f₁.fiberι s = f₁'.fiberι r ≫ p₁) ∧
    (∃ k : (i' ≫ f₁').fiber r ⟶ (i ≫ f₁).fiber s,
      IsIso k ∧ k ≫ (i ≫ f₁).fiberι s = (i' ≫ f₁').fiberι r ≫ pZ) ∧
    (∃ k : h'.fiber r ⟶ h.fiber s,
      IsIso k ∧ k ≫ h.fiberι s = h'.fiberι r ≫ pY)

/-- Localize an elementary dévissage at its marked base point. Its finite pushforward
is a finite module over a flat finitely presented smooth algebra, and all the marked
fibre, canonical comparison and neighbourhood-transfer assertions survive every further
affine elementary étale neighbourhood followed by localization.

Source: Stacks Project, flat.tex, Tag 05I5, first proof, reduction to smooth affines;
Tags 057S, 057T, 057U and 02KG
(blueprint: lem-trf-localized-devissage-neighborhood-transfer).

Proof:
1. Apply elementary module dévissage (057S). Local finite presentation implies local
   finite type by the affine presentation criterion. Obtain the affine pointed diagram,
   its finite-type module, the singleton finite fibre and the smooth geometrically
   integral family of dimension the local dimension of the fibre support.
2. The map from the ambient neighbourhood into X ×_S S₁ is étale by étale cancellation.
   Base change to A = O_{S₁,s₁}. Affine fibre products remain affine. Finite presentation
   of X over S, of the étale source map and of the closed immersion survives base change
   and composition (the affine presentation and finite-presentation permanence lemmas).
3. For A itself and each further elementary localized base C, the residue-field map
   at the closed point is an isomorphism. The closed-fibre cartesian diagram therefore
   identifies with the original fibre diagram. This preserves the marked points and
   their residue fields, the singleton fibre, pure transcendence and the support dimension.
4. Étaleness, finite maps, finitely presented closed immersions and smooth relative
   dimension survive base change. Any field-valued fibre of the new smooth family is
   a field-valued fibre of the original family, so geometric integrality survives too.
5. Pullback preserves quasi-coherence and finite type. Affine pushforward base change
   (02KG), applied to i and π, gives the specified canonical comparisons. The equation
   for E' is their composition with the pullback of E and pullback associativity.
6. On Y = Spec B, write π_*G as the tilde of its affine section module N. If generators
   of G over the finite B-algebra of Z are m_j and algebra generators as a B-module are
   h_k, then h_k m_j generate N over B. Smoothness makes A → B flat and finitely presented
   by the affine criteria for flatness and local finite presentation.
7. Flatness of F_x implies flatness of the original pushforward stalk by 057U.
   Affine stalk localization identifies it with N_q: the first base localization inverts
   only elements already invertible at q, and localization a second time at q changes
   neither that stalk nor its A-action (the affine module germ localization lemma).
8. Over A and each C, the resulting diagram again satisfies 057S with identity base
   neighbourhood. Apply 057T and 057U to obtain, respectively, the finite-presentation
   and relative-flatness neighbourhood equivalences. Transport through the canonical
   comparisons of step 5. No flatness away from the original marked point is assumed. -/
theorem exists_localized_devissage_neighborhood_transfer
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X)
    (hx : ¬ Subsingleton
      (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x))) :
    ∃ n : ℕ,
      topologicalKrullDimAt
        (⟨f.asFiber x, hx⟩ :
          {q : f.fiber (f x) |
            ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk q)}) =
        (n : WithBot ℕ∞) ∧
    ∃ (S₁ : Scheme.{u}) (s₁ : S₁) (e : S₁ ⟶ S),
      IsAffine S₁ ∧ Etale e ∧ e s₁ = f x ∧ IsIso (e.residueFieldMap s₁) ∧
    ∃ (X₁ Z : Scheme.{u}) (B : CommRingCat.{u})
      (α : S₁.presheaf.stalk s₁ →+* B)
      (g : X₁ ⟶ CategoryTheory.Limits.pullback f (S₁.fromSpecStalk s₁ ≫ e))
      (i : Z ⟶ X₁) (π : Z ⟶ Spec B) (z : Z) (G : Z.Modules)
      (N : ModuleCat.{u} B),
      IsAffine X₁ ∧ IsAffine Z ∧ Etale g ∧
      (pullback.fst f (S₁.fromSpecStalk s₁ ≫ e)) (g (i z)) = x ∧
      (∀ w : (CategoryTheory.Limits.pullback (C := Scheme.{u})
          f (S₁.fromSpecStalk s₁ ≫ e)),
        (pullback.fst f (S₁.fromSpecStalk s₁ ≫ e)) w = x → w = g (i z)) ∧
      IsIso (g.residueFieldMap (i z)) ∧
      i ≫ g ≫ pullback.snd f (S₁.fromSpecStalk s₁ ≫ e) =
        π ≫ Spec.map (CommRingCat.ofHom α) ∧
      IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧ QuasiCompact i ∧
      QuasiSeparated i ∧ IsFinite π ∧ G.IsFiniteType ∧ G.IsQuasicoherent ∧
      (π ⁻¹' ({π z} : Set (Spec B))) = {z} ∧
      (Spec.map (CommRingCat.ofHom α)) (π z) =
        IsLocalRing.closedPoint (S₁.presheaf.stalk s₁) ∧
      @Algebra.IsPurelyTranscendentalExtension
        ((Spec (S₁.presheaf.stalk s₁)).residueField
          ((Spec.map (CommRingCat.ofHom α)) (π z))) ((Spec B).residueField (π z))
        inferInstance inferInstance
        ((Spec.map (CommRingCat.ofHom α)).residueFieldMap (π z)).hom.toAlgebra ∧
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom α)) ∧
      GeometricallyIntegral (Spec.map (CommRingCat.ofHom α)) ∧
      LocallyOfFinitePresentation (g ≫ pullback.snd f (S₁.fromSpecStalk s₁ ≫ e)) ∧
      QuasiCompact (g ≫ pullback.snd f (S₁.fromSpecStalk s₁ ≫ e)) ∧
      QuasiSeparated (g ≫ pullback.snd f (S₁.fromSpecStalk s₁ ≫ e)) ∧
      Module.Finite B N ∧ Nonempty ((pushforward π).obj G ≅ tilde N) ∧
      α.Flat ∧ @Algebra.FinitePresentation (S₁.presheaf.stalk s₁) B
        inferInstance inferInstance α.toAlgebra ∧
      (Module.Flat (S.presheaf.stalk (f x))
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) →
        @Module.Flat (S₁.presheaf.stalk s₁)
          (LocalizedModule (π z).asIdeal.primeCompl N) inferInstance inferInstance
          (Module.compHom _ α)) ∧
    ∃ E : (pushforward i).obj G ≅ (tensorPullback g).obj
        ((tensorPullback (pullback.fst f (S₁.fromSpecStalk s₁ ≫ e))).obj F),
      localizedDevissageBaseChangeConclusions
        (pullback.snd f (S₁.fromSpecStalk s₁ ≫ e))
        (g ≫ pullback.snd f (S₁.fromSpecStalk s₁ ≫ e)) g i π
        (Spec.map (CommRingCat.ofHom α))
        ((tensorPullback (pullback.fst f (S₁.fromSpecStalk s₁ ≫ e))).obj F) G E
        (g (i z)) z (IsLocalRing.closedPoint (S₁.presheaf.stalk s₁)) n
        (Spec (S₁.presheaf.stalk s₁)) (𝟙 _) (IsLocalRing.closedPoint (S₁.presheaf.stalk s₁)) ∧
      ∀ (T : Scheme.{u}) [IsAffine T] (t : T)
        (v : T ⟶ Spec (S₁.presheaf.stalk s₁)),
        Etale v → v t = IsLocalRing.closedPoint (S₁.presheaf.stalk s₁) →
        IsIso (v.residueFieldMap t) →
        localizedDevissageBaseChangeConclusions
          (pullback.snd f (S₁.fromSpecStalk s₁ ≫ e))
          (g ≫ pullback.snd f (S₁.fromSpecStalk s₁ ≫ e)) g i π
          (Spec.map (CommRingCat.ofHom α))
          ((tensorPullback (pullback.fst f (S₁.fromSpecStalk s₁ ≫ e))).obj F) G E
          (g (i z)) z (IsLocalRing.closedPoint (S₁.presheaf.stalk s₁)) n
          (Spec (T.presheaf.stalk t)) (T.fromSpecStalk t ≫ v)
          (IsLocalRing.closedPoint (T.presheaf.stalk t)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
