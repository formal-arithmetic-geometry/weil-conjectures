/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperExchangeComparison
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompCompositionBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperRefinementSquareExchangeCompatibility
import WeilConjectures.AlgebraicGeometry.ClassicalProEtaleProperBaseChange
import WeilConjectures.Compactification.DenseCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations

import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # Proper units on the two compact-support localization pieces

Source: latest blueprint, sec-trace-formula/sk-i-global-additivity/
prop-trf-trace-additivity-open-closed.proof.md, Step 6, final paragraph.
(blueprint: lem-trf-canonical-proper-unit-localization).

We use the ordinary internal-module presentation of the discrete constant ring.
The open and closed pieces are computed in their canonical compactifications.
The exchange is the specified proper/open exchange on those models, hence the
open mate and the ordinary closed mate, including the identity-factor comparisons.
The compositor is the normalized CoherentData compositor, not an arbitrary isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CanonicalProperUnitLocalization

open CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The separated finite-type point over k.
Source: blueprint Step 6, the structure morphisms to Spec k
(blueprint: lem-trf-canonical-proper-unit-localization). -/
abbrev point (k : Type u) [Field k] : SepFinType k :=
  ⟨Over.mk (𝟙 (Spec (CommRingCat.of k))),
    ⟨(show LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))) from inferInstance),
      (show QuasiCompact (𝟙 (Spec (CommRingCat.of k))) from inferInstance),
      (show IsSeparated (𝟙 (Spec (CommRingCat.of k))) from inferInstance)⟩⟩

/-- The actual structure morphism, as a morphism of separated finite-type schemes.
Source: blueprint Step 6 (blueprint: lem-trf-canonical-proper-unit-localization). -/
abbrev structureMap {k : Type u} [Field k] (T : SepFinType k) : T ⟶ point k :=
  ObjectProperty.homMk (Over.homMk T.obj.hom (by simp))

variable {k : Type u} [Field k] (H : CompactSupportComposition.CoherentData Λ k)

/-- Unit, inverse canonical proper comparison, then the specified compact-support compositor.
This is beta before geometric-point evaluation, with the chosen structure compactification.
Source: blueprint Step 6 and the displayed definition of beta in the node
(blueprint: lem-trf-canonical-proper-unit-localization). -/
def unitMap (T : SepFinType k) (t : T ⟶ T) [IsProper t.hom.left]
    (cT : Compactification T.obj.hom) (ct : Compactification t.hom.left)
    (N : (localizingClosureProEtale Λ T.obj.left).FullSubcategory) :
    (F Λ cT).obj N.obj ⟶ (F Λ cT).obj ((P Λ t.hom.left).obj N.obj) :=
  (F Λ cT).map ((derivedUpperStarLowerStarAdjunction Λ t.hom.left).unit.app N.obj) ≫
    (F Λ cT).map ((properComparison Λ t.hom.left ct).inv.app
      ((P Λ t.hom.left).obj N.obj)) ≫
    (H.comp t (structureMap T) ct cT (cT.copy t.hom.w)).hom.app
      ⟨_, (H.pullback_preserves T T t.hom.left).1 N.obj N.property⟩

/-- The specified lambda before evaluation, using a supplied localization-piece model.
Source: blueprint Step 6, compact-support composition for a_X h = a_W
(blueprint: lem-trf-canonical-proper-unit-localization). -/
def pieceComparison {W X : SepFinType k} (h : W ⟶ X)
    (cW : Compactification W.obj.hom) (cX : Compactification X.obj.hom)
    (ch : Compactification h.hom.left)
    (N : (localizingClosureProEtale Λ W.obj.left).FullSubcategory) :
    (F Λ cX).obj ((F Λ ch).obj N.obj) ≅ (F Λ cW).obj N.obj :=
  (H.comp h (structureMap X) ch cX (cW.copy h.hom.w)).app N

/-- The recorded geometric-point evaluation, with its section-module universe explicit.
Source: def-weil-ordinary-compact-cohomology, terminal-point evaluation
(blueprint: lem-trf-canonical-proper-unit-localization). -/
abbrev evaluation (k : Type u) [Field k] :
    D Λ (Spec (CommRingCat.of k)) ⥤ DerivedCategory.{u + 2} (ModuleCat.{u + 1} (Γ Λ)) :=
  (condensedRingCoefficientSections Λ (Spec (CommRingCat.of k))).rightDerivedFunctor

/-- The left side of the node's equation, evaluated at the geometric point.
Source: blueprint Step 6, final unit compatibility equation
(blueprint: lem-trf-canonical-proper-unit-localization). -/
def leftMap {W X : SepFinType k} (h : W ⟶ X) (t : X ⟶ X) (w : W ⟶ W)
    [IsProper t.hom.left] [IsProper w.hom.left]
    (cW : Compactification W.obj.hom) (cX : Compactification X.obj.hom)
    (ct : Compactification t.hom.left)
    (ch : Compactification h.hom.left)
    (sq : Square ch ch w.hom.left t.hom.left)
    (N : (localizingClosureProEtale Λ W.obj.left).FullSubcategory) :=
  (evaluation Λ k).map
    (unitMap Λ H X t cX ct
        ⟨_, (H.preserves h ch).1 N.obj N.property⟩ ≫
      (F Λ cX).map ((squareExchange Λ sq).app N.obj) ≫
      (pieceComparison Λ H h cW cX ch
        ⟨_, (H.pullback_preserves W W w.hom.left).1 N.obj N.property⟩).hom)

/-- The right side, evaluated with exactly the same geometric-point functor.
Source: blueprint Step 6, final unit compatibility equation
(blueprint: lem-trf-canonical-proper-unit-localization). -/
def rightMap {W X : SepFinType k} (h : W ⟶ X) (w : W ⟶ W)
    [IsProper w.hom.left]
    (cW : Compactification W.obj.hom) (cX : Compactification X.obj.hom)
    (cw : Compactification w.hom.left) (ch : Compactification h.hom.left)
    (N : (localizingClosureProEtale Λ W.obj.left).FullSubcategory) :=
  (evaluation Λ k).map
    ((pieceComparison Λ H h cW cX ch N).hom ≫ unitMap Λ H W w cW cw N)

/-- The compatibility equation and naturality on all bounded constructible finite-Tor inputs.
The inclusion proof merely exposes the domain of the recorded compositor; it chooses no map.
Source: blueprint Step 6 and the naturality clause of the node
(blueprint: lem-trf-canonical-proper-unit-localization). -/
def Compatibility {W X : SepFinType k} (h : W ⟶ X) (t : X ⟶ X) (w : W ⟶ W)
    [IsProper t.hom.left] [IsProper w.hom.left]
    (cW : Compactification W.obj.hom) (cX : Compactification X.obj.hom)
    (ct : Compactification t.hom.left) (cw : Compactification w.hom.left)
    (ch : Compactification h.hom.left)
    (sq : Square ch ch w.hom.left t.hom.left)
    (inc : condensedConstructibleFiniteTor Λ W.obj.left ≤
      localizingClosureProEtale Λ W.obj.left) : Prop :=
  ∀ N : CondensedConstructibleFiniteTor Λ W.obj.left,
    leftMap Λ H h t w cW cX ct ch sq ⟨N.obj, inc N.obj N.property⟩ =
      rightMap Λ H h w cW cX cw ch ⟨N.obj, inc N.obj N.property⟩ ∧
    ∀ (M : CondensedConstructibleFiniteTor Λ W.obj.left) (f : N ⟶ M),
      (evaluation Λ k).map ((F Λ cX).map ((F Λ ch).map f.hom)) ≫
          rightMap Λ H h w cW cX cw ch ⟨M.obj, inc M.obj M.property⟩ =
        rightMap Λ H h w cW cX cw ch ⟨N.obj, inc N.obj N.property⟩ ≫
          (evaluation Λ k).map ((F Λ cW).map ((P Λ w.hom.left).map f.hom))

/-- The supplied Cartesian open square on the canonical open compactification.
Source: blueprint Step 6, open piece; its proper factor is the identity
(blueprint: lem-trf-canonical-proper-unit-localization). -/
def openSquare {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {t : X ⟶ X} {w : U ⟶ U} (sq : IsPullback w j j t) :
    Square (Compactification.ofIsOpenImmersion j) (Compactification.ofIsOpenImmersion j)
      w t where
  middle := t
  openSquare := sq
  properSquare := ⟨by
    change t ≫ 𝟙 X = 𝟙 X ≫ t
    simp⟩

/-- Proper units respect both localization pieces, naturally in the finite-Tor input.
The existence of inc records well-definedness on the entire native Dctf, rather than
silently requiring the user to supply membership in the compositor's localizing domain.
All compactifications of the structure maps and proper endomorphisms are arbitrary.

Source: latest blueprint, prop-trf-trace-additivity-open-closed.proof.md, Step 6,
final paragraph (blueprint: lem-trf-canonical-proper-unit-localization).

Proof, following the seven DAG steps:
1. Normalize ordinary derived direct-image composition by the composite-adjunction unit;
identified constant coefficients give exact pullback. This is the internal-module transport
of def-weil-pbc-proetale-operations, with no completion.
2. In the open case, the normalized proper/open tower compositor identifies its commutator
with the proper-adjunction mate of the open exchange b_t. The identity factors in openSquare
are exactly the canonical identity comparisons, so squareExchange is b_t on this model.
3. Naturality of the two units and the open exchange, followed by the triangle identity,
gives S_t(b_N) eta_t = G_(h,L_w N) H(eta_w).
4. For the closed piece, identity-open proper compactifications identify G_h with the
ordinary direct-image compositor through S_(ih)=S_(ti). No Cartesian closed square is used.
5. Expand the closed exchange as the mate of the pullback comparison. Compute the unit of
the composite adjunction in both orders; postcompose with S_t H(L_w epsilon_i).
Naturality and the triangle identity give the same unit equation as in step 3.
6. Associativity of the specified compact-support compositor, and cancellation of the
identity-open proper comparisons, intertwine G_h with alpha_(a_X,h).
7. Apply Ra_X!, use naturality, and evaluate at the geometric point. This gives the equation
and naturality displayed in Compatibility. Finite constant coefficients identify native
bounded constructibility with finite constant-model constructibility, giving inc by the
defining universal property of localizingClosure. This proof includes empty pieces, the
zero ring (including exponent zero), identity endomorphisms, and non-Cartesian closed squares.
-/
theorem canonical_proper_unit_localization
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (A : Type) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (hA : ∃ n : ℕ, (ℓ ^ n : A) = 0)
    (H : CompactSupportComposition.CoherentData (Profinite.continuousMapRingObj.{u} A) k)
    (U Z X : SepFinType k) (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j.hom.left] [QuasiCompact j.hom.left]
    [IsClosedImmersion i.hom.left]
    (hji : IsCompl (Set.range j.hom.left.base) (Set.range i.hom.left.base))
    (t : X ⟶ X) (tU : U ⟶ U) (tZ : Z ⟶ Z)
    [IsProper t.hom.left] [IsProper tU.hom.left] [IsProper tZ.hom.left]
    (sqU : IsPullback tU.hom.left j.hom.left j.hom.left t.hom.left)
    (sqZ : CommSq tZ.hom.left i.hom.left i.hom.left t.hom.left)
    (cX : Compactification X.obj.hom) (cU : Compactification U.obj.hom)
    (cZ : Compactification Z.obj.hom) (ct : Compactification t.hom.left)
    (ctU : Compactification tU.hom.left) (ctZ : Compactification tZ.hom.left) :
    ∃ inc : ∀ T : SepFinType k,
      condensedConstructibleFiniteTor (Profinite.continuousMapRingObj.{u} A) T.obj.left ≤
        localizingClosureProEtale (Profinite.continuousMapRingObj.{u} A) T.obj.left,
      Compatibility (Profinite.continuousMapRingObj.{u} A) H j t tU cU cX ct ctU
        (Compactification.ofIsOpenImmersion j.hom.left) (openSquare j.hom.left sqU) (inc U) ∧
      Compatibility (Profinite.continuousMapRingObj.{u} A) H i t tZ cZ cX ct ctZ
        (Compactification.ofIsProper i.hom.left)
        (properIdentityCompactificationSquare sqZ) (inc Z) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CanonicalProperUnitLocalization
