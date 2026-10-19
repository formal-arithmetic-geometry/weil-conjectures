/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Finite direct image and closed exceptional restriction

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, proof of
Proposition 5.4.1, printed p. 291 (blueprint: lem-per-finite-closed-support-exchange).
The functors are on ordinary small-etale D+ with constant module coefficients.
For finite maps the right derived direct images are the exact direct images.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The canonical identification `i_* p'_* ≅ p_* i'_*` on D+, induced by the
fiber-product associativity identification of sections of direct images.
Source: ILO XVII, proof of Proposition 5.4.1, p. 291
(blueprint: lem-per-finite-closed-support-exchange). -/
noncomputable def finiteClosedSupportDirectImageIso
    {X' X Y : Scheme.{u}} (p : X' ⟶ X) (i : Y ⟶ X) :
    (lowerStar (ModuleCat.{u + 1} A) (pullback.fst i p)).rightDerivedFunctorPlus ⋙
        (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus ≅
      (lowerStar (ModuleCat.{u + 1} A) (pullback.snd i p)).rightDerivedFunctorPlus ⋙
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus :=
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.fst i p))
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.snd i p))
  Functor.rightDerivedFunctorPlusCompIso' _ _
      (lowerStarComp (ModuleCat.{u + 1} A) (pullback.fst i p) i
        (pullback.snd i p ≫ p) (pullback.condition (f := i) (g := p)).symm) ≪≫
    (Functor.rightDerivedFunctorPlusCompIso' _ _
      (lowerStarComp (ModuleCat.{u + 1} A) (pullback.snd i p) p)).symm

/-- The actual map `i_* p'_* i'^! → p_*`: apply the canonical direct-image
identification and then `p_*` to the closed adjunction counit for `i'`.
Source: ILO XVII, proof of Proposition 5.4.1, p. 291
(blueprint: lem-per-finite-closed-support-exchange). -/
noncomputable def finiteClosedSupportCounit
    {X' X Y : Scheme.{u}} (p : X' ⟶ X) (i : Y ⟶ X) [IsClosedImmersion i] :
    (closedSupportPlus A (pullback.snd i p) ⋙
        (lowerStar (ModuleCat.{u + 1} A) (pullback.fst i p)).rightDerivedFunctorPlus) ⋙
        (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus ⟶
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (closedSupportPlus A (pullback.snd i p))
      (finiteClosedSupportDirectImageIso A p i).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (closedSupportPlusAdjunction A (pullback.snd i p)).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The canonical comparison `p'_* i'^! → i^! p_*`, the closed-adjunction
transpose of `finiteClosedSupportCounit`. Equivalently it is the comparison obtained
from canonical pullback/closed-direct-image exchange by the ordinary adjunctions.
Source: ILO XVII, proof of Proposition 5.4.1, p. 291
(blueprint: lem-per-finite-closed-support-exchange). -/
noncomputable def finiteClosedSupportExchange
    {X' X Y : Scheme.{u}} (p : X' ⟶ X) (i : Y ⟶ X) [IsClosedImmersion i] :
    closedSupportPlus A (pullback.snd i p) ⋙
        (lowerStar (ModuleCat.{u + 1} A) (pullback.fst i p)).rightDerivedFunctorPlus ⟶
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus ⋙ closedSupportPlus A i :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (closedSupportPlusAdjunction A i).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (finiteClosedSupportCounit A p i) (closedSupportPlus A i)

/-- Finite direct image commutes with closed exceptional restriction, with its prescribed
counit normalization. The inverse of `e` is the specified comparison, not an arbitrary
isomorphism; the unit identifies `i^! i_*` with the identity. The displayed identity
therefore says precisely that applying `i^!` to `p_*` of the `i'` counit gives identity
on `p'_* i'^! M`, and the last clause records invertibility of this actual map.
Source: ILO XVII, proof of Proposition 5.4.1, p. 291
(blueprint: lem-per-finite-closed-support-exchange).

Proof, following the seven steps of the node:
1. Base change makes i' closed and p' finite; closed maps and their composites are finite.
   On an etale V the two direct images both evaluate to sections on V times_X Y'.
   This gives c = finiteClosedSupportDirectImageIso.
2. Finite direct image is exact (lemma-weil-pbc-finite-direct-image-exact), also for
   modules, since forgetting the action preserves and detects exactness. Inverse image
   is exact, and its module adjunction has the actual ordinary unit and counit
   (lem-weil-pbc-inverse-image-module-adjunction). Localizing termwise gives the
   ordinary derived adjunctions; exact direct image computes its right derived functor
   (lem-weil-pbc-exact-functor-derived-functor).
3. The ambient closed adjunction (lem-exc-closed-ambient) restricts to D+: exactness of
   i_* and t-structure orthogonality make its right adjoint preserve lower bounds.
   The published closedSupportPlusAdjunction is this bounded-below adjunction.
4. Closed ordinary counits are invertible (prop-openclosed-lowerstar-fully-faithful),
   hence closed direct image is fully faithful on D+. Its exceptional unit u is
   invertible by the Hom bijections and coyoneda.
5. Canonical finite exchange gives theta: p^* i_* ≅ i'_* p'^*.
   Adjunctions give Hom(T,p'_*i'^!M) ≅ Hom(p'^*T,i'^!M) ≅ Hom(i'_*p'^*T,M)
   ≅ Hom(p^*i_*T,M) ≅ Hom(i_*T,p_*M) ≅ Hom(T,i^!p_*M).
   Coyoneda gives the natural isomorphism delta in the forward direction.
6. For ordinary counits a,a', exchange satisfies i'_*(a') theta = a p^*(c),
   checked on sections over V times_X Y'. Tracing identity through the Hom bijections
   and using naturality and the ordinary triangle identity gives delta = u followed
   by i^!(E), where E = p_*(closed counit) c = finiteClosedSupportCounit.
   This is exactly finiteClosedSupportExchange, fixing its canonical normalization.
7. Take e = delta inverse. Then u followed by i^!(E) followed by e is identity.
   Since u and delta are invertible, i^!(E) is invertible as well. -/
theorem finite_closedSupport_exchange
    {X' X Y : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X]
    (p : X' ⟶ X) [IsFinite p] (i : Y ⟶ X) [IsClosedImmersion i] :
    IsIso (closedSupportPlusAdjunction A i).unit ∧
    ∃ e :
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus ⋙
            closedSupportPlus A i ≅
          closedSupportPlus A (pullback.snd i p) ⋙
            (lowerStar (ModuleCat.{u + 1} A) (pullback.fst i p)).rightDerivedFunctorPlus,
      e.inv = finiteClosedSupportExchange A p i ∧
      ∀ M : _root_.DerivedCategory.Plus
          (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (closedSupportPlusAdjunction A i).unit.app
            (((lowerStar (ModuleCat.{u + 1} A) (pullback.fst i p)).rightDerivedFunctorPlus).obj
              ((closedSupportPlus A (pullback.snd i p)).obj M)) ≫
            (closedSupportPlus A i).map ((finiteClosedSupportCounit A p i).app M) ≫
            e.hom.app M = 𝟙 _ ∧
          IsIso ((closedSupportPlus A i).map ((finiteClosedSupportCounit A p i).app M)) := by
  sorry

end AlgebraicGeometry.Etale
