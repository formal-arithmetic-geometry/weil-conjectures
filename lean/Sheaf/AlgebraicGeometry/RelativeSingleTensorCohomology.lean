/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProEtaleModuleObjects
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Relative tensor with a module in a single degree

Source: blueprint main-20261015, localizing closure, Complexes paragraph;
Stacks Tags 0FNH, 011G and 011H (blueprint: lem-sfb-relative-single-tensor-cohomology).

All tensors below are the relative tensor on internal modules over the pulled-back
condensed ring. The comparison is the unsigned first-variable total-tensor shift.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})

/-- The direct-sum total tensor of the degree-q single complex and P.
Source: Stacks 0FNH (blueprint: lem-sfb-relative-single-tensor-cohomology). -/
noncomputable abbrev relativeSingleTotal (q : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ) :=
  CochainComplex.mapBifunctor ((CochainComplex.singleFunctor _ q).obj M) P
    (curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)))

/-- The canonical unsigned comparison, obtained by identifying S_q M with S_0 M[-q]
and applying the first-variable comparison s^1_{-q}.
Source: Stacks 0FNH (blueprint: lem-sfb-relative-single-tensor-cohomology). -/
noncomputable def relativeSingleShiftIso (q : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ) :
    relativeSingleTotal Λ X q M P ≅ (relativeSingleTotal Λ X 0 M P) ⟦-q⟧ :=
  tensorIso (((CochainComplex.singleFunctors _).shiftIso (-q) q 0
    (neg_add_cancel q)).symm.app M) (Iso.refl P) ≪≫
      CochainComplex.mapBifunctorShift₁Iso
        ((CochainComplex.singleFunctor _ 0).obj M) P
        (curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))) (-q)

/-- The canonical derived first-variable shift comparison on two heart objects.
Source: Layer B K-flat tensor and Stacks 0FNH
(blueprint: lem-sfb-relative-single-tensor-cohomology). -/
noncomputable def relativeSingleDerivedShiftIso (q : ℤ)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) :
    ((DerivedCategory.singleFunctor _ 0).obj M) ⟦-q⟧ ⊗
      (DerivedCategory.singleFunctor _ 0).obj N ≅
    ((DerivedCategory.singleFunctor _ 0).obj M ⊗
      (DerivedCategory.singleFunctor _ 0).obj N) ⟦-q⟧ :=
  ((tensorRight ((DerivedCategory.singleFunctor _ 0).obj N)).commShiftIso (-q)).app
    ((DerivedCategory.singleFunctor _ 0).obj M)

/-- The canonical cohomology comparison, before choosing any resolution.
Source: Stacks 011H and the Layer B tensor shift
(blueprint: lem-sfb-relative-single-tensor-cohomology). -/
noncomputable def relativeSingleTensorCohomologyIso (q r : ℤ)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) :
    (DerivedCategory.homologyFunctor _ r).obj
      (((DerivedCategory.singleFunctor _ 0).obj M) ⟦-q⟧ ⊗
        (DerivedCategory.singleFunctor _ 0).obj N) ≅
    (DerivedCategory.homologyFunctor _ (r - q)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M ⊗
        (DerivedCategory.singleFunctor _ 0).obj N) :=
  (DerivedCategory.homologyFunctor _ r).mapIso
    (relativeSingleDerivedShiftIso Λ X q M N) ≪≫
      ((DerivedCategory.homologyFunctor _ 0).shiftIso (-q) r (r - q)
        (neg_add_eq_sub q r)).app _

/-- The canonical representative arrow from the derived tensor to the total complex.
It uses the inverse of Q(p) and the lax localization multiplication, in its actual
(direction derived tensor to localized ordinary tensor).
Source: Layer B K-flat computation (blueprint: lem-sfb-relative-single-tensor-cohomology). -/
noncomputable def relativeSingleRepresentativeMap (q : ℤ)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ)
    (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj N) [QuasiIso p] :
    ((DerivedCategory.singleFunctor _ 0).obj M) ⟦-q⟧ ⊗
      (DerivedCategory.singleFunctor _ 0).obj N ⟶
    DerivedCategory.Q.obj (relativeSingleTotal Λ X q M P) :=
  tensorHom
    (((DerivedCategory.Q.commShiftIso (-q)).inv.app
      ((CochainComplex.singleFunctor _ 0).obj M)) ≫
      DerivedCategory.Q.map (((CochainComplex.singleFunctors _).shiftIso (-q) q 0
        (neg_add_cancel q)).hom.app M))
    (inv (DerivedCategory.Q.map p)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((CochainComplex.singleFunctor _ q).obj M) P

/-- Relative single-degree tensor calculation, including its canonical representatives.
Source: blueprint main-20261015, localizing-closure Complexes paragraph; Stacks
0FNH, 011G, 011H (blueprint: lem-sfb-relative-single-tensor-cohomology).

Proof: (1) the Layer B K-flat computation identifies the lax multiplication with an
isomorphism when P is K-flat, and Q(p) is invertible. (2) All total summands except
(q,r-q) vanish; its inclusion is therefore an isomorphism. The Leibniz differential
is (-1)^q times 1 tensor d, as the single complex has zero differential.
(3) S_q M = S_0 M[-q]; the unsigned comparison s^1_{-q} is the identity on these
summands. (4) Functoriality of the summand inclusions and naturality of s^1 give the
squares for maps of M and resolutions. (5) Resolve S_0 M by U; U[-q] is K-flat
because both signed total-shift comparisons preserve quasi-isomorphisms. The span
S_i M tensor P <- U_i tensor P -> U_i tensor S_0 N consists of quasi-isomorphisms.
(6) Naturality of the lax multiplication makes both composites from Q(U_i tensor P)
equal; naturality of s^1 identifies their shift squares. Thus the descended comparison
is independent of P and p. (7) Localization descent gives naturality in N, and using
one resolution for a map M -> M' gives naturality in M. (8) Apply H^r and the
cohomology-shift isomorphism with shift -q and resulting degree r-q. This gives the
specified cohomology isomorphism for every resolution, in all integer degrees. -/
theorem relativeSingleTensorCohomology :
    (∀ (q r : ℤ) (M M' N N' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
      (f : M ⟶ M') (g : N ⟶ N'),
      (DerivedCategory.homologyFunctor _ r).map
        (tensorHom (((DerivedCategory.singleFunctor _ 0).map f) ⟦-q⟧')
          ((DerivedCategory.singleFunctor _ 0).map g)) ≫
        (relativeSingleTensorCohomologyIso Λ X q r M' N').hom =
      (relativeSingleTensorCohomologyIso Λ X q r M N).hom ≫
        (DerivedCategory.homologyFunctor _ (r - q)).map
          (tensorHom ((DerivedCategory.singleFunctor _ 0).map f)
            ((DerivedCategory.singleFunctor _ 0).map g))) ∧
    (∀ (q : ℤ) (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
      (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ)
      (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj N) [QuasiIso p],
      P.IsKFlatForTotalTensor → IsIso (relativeSingleRepresentativeMap Λ X q M N P p)) ∧
    (∃ t : ∀ (q : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
      (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ)
      (r a : ℤ), q + a = r →
      ((relativeSingleTotal Λ X q M P).X r ≅ M ⊗ P.X a),
      (∀ (q : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
        (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ)
        (r a : ℤ) (h : q + a = r),
        (t q M P r a h).inv =
          ((curriedTensor _).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) q M).inv).app (P.X a) ≫
          CochainComplex.ιMapBifunctor ((CochainComplex.singleFunctor _ q).obj M) P
            (curriedTensor _) q a r h) ∧
      (∀ (q : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
        (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ)
        (r a : ℤ) (h : q + a = r),
        (t q M P r a h).inv ≫ (relativeSingleTotal Λ X q M P).d r (r + 1) ≫
          (t q M P (r + 1) (a + 1) (by omega)).hom =
            q.negOnePow • (M ◁ P.d a (a + 1))) ∧
      (∀ (q : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
        (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ)
        (r a : ℤ) (h : q + a = r),
        (relativeSingleShiftIso Λ X q M P).hom.f r ≫
          (CochainComplex.shiftFunctorObjXIso
            (relativeSingleTotal Λ X 0 M P) (-q) r a (by omega)).hom ≫
          (t 0 M P a a (zero_add a)).hom = (t q M P r a h).hom)) ∧
    (∀ (q : ℤ) (M M' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
      (f : M ⟶ M') (P P' : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ)
      (g : P ⟶ P'),
      HomologicalComplex.tensorHom ((CochainComplex.singleFunctor _ q).map f) g ≫
        (relativeSingleShiftIso Λ X q M' P').hom =
      (relativeSingleShiftIso Λ X q M P).hom ≫
        (HomologicalComplex.tensorHom ((CochainComplex.singleFunctor _ 0).map f) g) ⟦-q⟧') ∧
    (∀ (q : ℤ) (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))
      (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)) ℤ)
      (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj N) [QuasiIso p],
      P.IsKFlatForTotalTensor →
      relativeSingleRepresentativeMap Λ X q M N P p ≫
        DerivedCategory.Q.map (relativeSingleShiftIso Λ X q M P).hom ≫
        (DerivedCategory.Q.commShiftIso (-q)).hom.app (relativeSingleTotal Λ X 0 M P) =
      (relativeSingleDerivedShiftIso Λ X q M N).hom ≫
        ((tensorIso ((shiftFunctorZero _ ℤ).app
            ((DerivedCategory.singleFunctor _ 0).obj M))
            (Iso.refl ((DerivedCategory.singleFunctor _ 0).obj N))).inv ≫
          relativeSingleRepresentativeMap Λ X 0 M N P p) ⟦-q⟧') := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
