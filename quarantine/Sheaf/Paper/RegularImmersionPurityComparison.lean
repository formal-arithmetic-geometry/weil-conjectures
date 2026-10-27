/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q21 and Q78
-/
module

public import Sheaf.AlgebraicGeometry.RegularImmersionPureCodimension
public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.StandingExceptionalComposition
public import Sheaf.Paper.PurityTwistCancellation
public import Sheaf.Paper.PurityCompositionCoherence
public import Sheaf.Paper.FiniteClopenDerivedDecomposition
public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion

/-! # The smooth-purity comparison for a regular immersion

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular,
pur9-rg-def-phi.md (blueprint: pur9-rg-def-phi).

The connected comparison is specified by tensoring with the positive Tate shift.
This determining equation is the displayed four-arrow composite after cancelling
that invertible shift. The global comparison is specified by restriction to all
connected clopen components, with the prescribed exceptional-composition comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures.PurityFiniteSetting
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RegularImmersionPurity

/-- The existing finite-coefficient derived category, with its full small-site universes.
Source: pur9-rg-def-phi (blueprint: pur9-rg-def-phi). -/
abbrev D (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  PurityCancellationCategory P T

/-- The coefficient unit, using the published positive Tate power at zero.
Source: pur9-rg-def-phi, Lambda_T (blueprint: pur9-rg-def-phi). -/
abbrev unit (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  P.diagonalTwist T 0

/-- The actual comparison inverse image of the degree-zero etale coefficient unit.
Source: pur9-rg-def-phi, coefficient identifications (blueprint: pur9-rg-def-phi). -/
def unitPresentation (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    unit P T ≅
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit P.Coefficient T) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.mapIso
    (eqToIso (compositionEtalePowerZero P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates T))

/-- The unit lies in the recorded bounded constructible category.
Source: pur9-rg-def-phi, Lambda_S (blueprint: pur9-rg-def-phi).
Proof: the ordinary constant finite sheaf is constructible, and its single complex
is bounded. Exact comparison inverse image gives bounded constructible etale origin;
unitPresentation identifies the published zero power with this object. -/
theorem unit_bounded (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) T (unit P T) := by
  sorry

section Functors
variable (P : WeilConjectures.PurityFiniteSetting.{u}) {T V W : Scheme.{u}}
  [T.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
  [W.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
  [QuasiCompact (T ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
  [QuasiCompact (V ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
  [QuasiCompact (W ↘ Spec (.of P.field.k))]

/-- The recorded exceptional functor with the field-base compactification supplied.
Source: pur9-rg-def-phi, Rh! (blueprint: pur9-rg-def-phi). -/
abbrev exceptional (f : T ⟶ V) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :=
  P.smoothPurityExceptionalOver f (V ↘ Spec (.of P.field.k))

/-- The recorded composition map on bounded constructible inputs.
Source: pur9-rg-def-phi, c_{g,f,L} (blueprint: pur9-rg-def-phi). -/
def comp (f : T ⟶ V) (g : V ⟶ W)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (L : D P W)
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) W L) :
    (exceptional P (f ≫ g)).obj L ⟶ (exceptional P f).obj ((exceptional P g).obj L) :=
  standingExceptionalComposition P f g ⟨L, hL⟩

/-- Invertibility of exactly the standing composition mate.
Source: pur9-rg-def-phi, the adjunction-conjugate description
(blueprint: pur9-rg-def-phi).
Proof: alpha is the canonical compact-support composition isomorphism of
thm-sf-comp-composition. The two standing Hom bijections transpose it to comp.
Transposing its inverse gives an inverse: the two triangle identities reduce the
composites to alpha followed by alpha inverse and conversely. This is the
isomorphism part of def-weil-pbc-adjunction-conjugate on the constructible domain. -/
theorem comp_isIso (f : T ⟶ V) (g : V ⟶ W)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (L : D P W)
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) W L) :
    IsIso (comp P f g L hL) := by
  sorry

/-- The canonical composition isomorphism, retaining the specified hom.
Source: pur9-rg-def-phi, c_{g,f,L} (blueprint: pur9-rg-def-phi). -/
def compIso (f : T ⟶ V) (g : V ⟶ W)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (L : D P W)
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) W L) :=
  letI := comp_isIso P f g L hL
  asIso (comp P f g L hL)

end Functors

/-- The structure morphism is over its base with the identity structure on the base.
Source: pur9-rg-def-phi, structure-map convention (blueprint: pur9-rg-def-phi).
Proof: the required triangle is a_T followed by the identity, equal to a_T by
Category.comp_id. No additional structure morphism or hypothesis is introduced. -/
theorem structure_isOver (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :
    (T ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) := by
  sorry

/-- The positive cancellation equation formed before specializing coefficient categories.
This is the displayed negative-twist composite tensored back with the positive shift.
Source: pur9-rg-def-phi, connected composite (blueprint: pur9-rg-def-phi). -/
def positiveEquation {C E : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} E]
    (TX : C ⥤ C ⥤ C) (TZ : E ⥤ E ⥤ E) (G Q : C ⥤ E)
    (U M : E) (A B V OX : C) (OZ : E)
    (unitor : (TZ.obj U).obj M ≅ M) (piX : OX ≅ V) (piZ : OZ ≅ M)
    (b : OZ ≅ G.obj OX) (pull : Q.obj B ≅ M)
    (cop : G.obj ((TX.obj A).obj B) ≅ (TZ.obj (G.obj A)).obj (Q.obj B))
    (add : (TX.obj A).obj B ≅ V) (φ : U ⟶ G.obj A) : Prop :=
  (TZ.map φ).app M ≫ (TZ.obj (G.obj A)).map pull.inv ≫ cop.inv ≫ G.map add.hom =
    unitor.hom ≫ piZ.inv ≫ b.hom ≫ G.map piX.hom

section Structure
variable (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
  [T.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
  [QuasiCompact (T ↘ Spec (.of P.field.k))]
  [IsSeparated (T ↘ Spec (.of P.field.k))]

/-- The absolute dualizing object Ra_T! Lambda_S.
Source: pur9-rg-def-phi, omega_{a_T} (blueprint: pur9-rg-def-phi). -/
def omega : D P T :=
  (exceptional P (T ↘ Spec (.of P.field.k))).obj (unit P (Spec (.of P.field.k)))

/-- The specified smooth orientation, with only the canonical coefficient-unit transport.
Source: pur9-rg-def-phi and def-pur-smooth-purity-map, Pi_{a_T}
(blueprint: pur9-rg-def-phi). -/
def orientation (d : ℕ) [SmoothOfRelativeDimension d (T ↘ Spec (.of P.field.k))] :
    omega P T ≅ P.diagonalTwist T d :=
  letI := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (.of P.field.k))
  letI : HasCompactification (T ↘ Spec (.of P.field.k)) := inferInstance
  (exceptional P (T ↘ Spec (.of P.field.k))).mapIso
    (unitPresentation P (Spec (.of P.field.k))) ≪≫
      P.diagonalDualizingObject d (T ↘ Spec (.of P.field.k)) (𝟙 _)

end Structure

section Coefficients
variable (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
  [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]

/-- The positive Tate objects are bounded constructible in the actual fixed coordinates.
Source: pur9-rg-def-phi, Tate objects (blueprint: pur9-rg-def-phi).
Proof: the finite Kummer line is locally free of rank one since ell is invertible
on every k-scheme. Its finite positive tensor powers remain locally free and
constructible. The shift by twice the power preserves boundedness. Comparison
inverse image gives the recorded bounded constructible etale-origin predicate. -/
theorem twist_bounded (d : ℕ) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) X
      (P.diagonalTwist X d) := by
  sorry

/-- The exceptional image stays in the bounded constructible domain used by c and rho.
Source: pur9-rg-def-phi, constructible exceptional inverse image
(blueprint: pur9-rg-def-phi).
Proof: def-weil-exceptional-inverse-image gives constructible preservation of the
transported etale adjoint over the fixed finite field. The finite fixed-coordinate
formula is exactly smoothPurityExceptionalOver. Thus the canonical coefficient
realization transports that preservation to the predicate used here. -/
theorem exceptional_bounded (f : Z ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : D P X)
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) Z
      ((exceptional P f).obj K) := by
  sorry

/-- The canonical etale normalization transported back to the pro-etale object itself.
The last factor is the comparison counit, so no etale representative is chosen.
Source: pur9-rg-def-phi, rho_e (blueprint: pur9-rg-def-phi). -/
def rho (e : Z ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e] (K : D P X) :
    (exceptional P e).obj K ⟶ (P.smoothPurityPullback e).obj K :=
  letI := FiniteEtaleNormalization.compactification P e
  let A := ModuleCat.{u + 1} P.Coefficient
  let Rν := (comparisonLowerStar A X).rightDerivedFunctor
  let ν := (comparisonUpperStar A Z).mapDerivedCategory
  ν.map ((FiniteEtaleNormalization.rho P e).hom.app (Rν.obj K)) ≫
    ν.map ((Etale.leftDerivedUpperStarIsoMapDerivedCategory A e).hom.app (Rν.obj K)) ≫
    (sfDerivedComparisonPullbackIso P.Ring e).inv.app (Rν.obj K) ≫
    (P.smoothPurityPullback e).map ((derivedComparisonAdjunction A X).counit.app K)

/-- The transported normalization is invertible on the constructible domain.
Source: pur9-rg-def-phi, rho_e (blueprint: pur9-rg-def-phi).
Proof: the first three factors of rho are the specified etale normalization and
canonical derived comparison isomorphisms. On a bounded constructible object,
etale origin and full faithfulness make the comparison counit invertible.
Pullback preserves that isomorphism, so all four factors are invertible. -/
theorem rho_isIso (e : Z ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e] (K : D P X)
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) X K) :
    IsIso (rho P e K) := by
  sorry

/-- The normalized etale isomorphism with the exact pro-etale pullback target.
Source: pur9-rg-def-phi, rho_e (blueprint: pur9-rg-def-phi). -/
def rhoIso (e : Z ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e] (K : D P X)
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) X K) :=
  letI := rho_isIso P e K _hK
  asIso (rho P e K)

end Coefficients

section Connected
variable (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
  [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [IsSeparated (Z ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  (i : Z ⟶ X) [i.IsOver (Spec (.of P.field.k))] [IsClosedImmersion i]

/-- The canonical co-projection for the positive Tate shifts used to cancel m.
Source: pur9-rg-def-phi, the last arrow (blueprint: pur9-rg-def-phi).
Proof: both positive Tate shifts are bounded constructible and finite-Tor. The
negative signed Tate shift is their tensor inverse. Apply lem-pur-coprojection to
K=T_X(c) and L=T_X(m); its projection/counit equation fixes the inverse map.
This is exactly purityCoprojectionProperty in these coefficient coordinates. -/
theorem positiveCoprojection (c m : ℕ) :
    purityCoprojectionProperty P i (X ↘ Spec (.of P.field.k))
      (P.diagonalTwist X c) (P.diagonalTwist X m) := by
  sorry

/-- Extract the specified co-projection; its counit equation determines it uniquely.
Source: pur9-rg-def-phi, inverse co-projection (blueprint: pur9-rg-def-phi). -/
def positiveCoprojectionWitnessIso (c m : ℕ) :=
  (positiveCoprojection P i c m).choose_spec.choose_spec.choose

/-- The very same co-projection type with the functors named before specialization.
The pullback here is still left-derived; no exact/derived identification is suppressed.
Source: pur9-rg-def-phi, co-projection coordinates (blueprint: pur9-rg-def-phi). -/
abbrev PositiveCoprojectionType (c m : ℕ) :=
  (exceptional P i).obj
      (((smoothPurityTensor P.Coefficient X).obj (P.diagonalTwist X c)).obj
        (P.diagonalTwist X m)) ≅
    ((smoothPurityTensor P.Coefficient Z).obj
      ((exceptional P i).obj (P.diagonalTwist X c))).obj
        (((upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor).obj
          (P.diagonalTwist X m))

/-- Name the existing co-projection in the definitionally equal fixed functor interface.
HEq compares only identical sites, tensors, exceptional functors and left-derived
pullbacks; it does not identify merely isomorphic objects or exact pullbacks.
Source: pur9-rg-def-phi, inverse co-projection (blueprint: pur9-rg-def-phi).
Proof: unfold smoothPurityTensor and smoothPurityExceptionalOver, and the finite
exceptional transport. They are exactly the tensor and exceptional functor used in
purityCoprojectionProperty. Its chosen isomorphism therefore has the stated type.
Use that isomorphism and reflexive HEq. HEq to this fixed value gives uniqueness. -/
theorem existsUnique_positiveCoprojectionIso (c m : ℕ) :
    ∃! e : PositiveCoprojectionType P i c m,
      HEq e (positiveCoprojectionWitnessIso P i c m) := by
  sorry

/-- The canonical co-projection, with only its already fixed type presentation named.
Source: pur9-rg-def-phi, inverse co-projection (blueprint: pur9-rg-def-phi). -/
def positiveCoprojectionIso (c m : ℕ) : PositiveCoprojectionType P i c m :=
  (existsUnique_positiveCoprojectionIso P i c m).exists.choose

/-- The coefficient-unit contraction, with the canonical ordered positive Tate product.
Source: pur9-rg-def-phi, cancellation of the m shift (blueprint: pur9-rg-def-phi). -/
def unitProduct (m : ℕ) :
    ((smoothPurityTensor P.Coefficient Z).obj (unit P Z)).obj (P.diagonalTwist Z m) ≅
      P.diagonalTwist Z m :=
  (compositionPowerAdd P Z m 0).symm ≪≫
    eqToIso (congrArg (P.diagonalTwist Z) (Nat.add_zero m))

/-- The canonical c_{a_X,i,Lambda_S}, in absolute dualizing coordinates.
Source: pur9-rg-def-phi, middle orientation arrow (blueprint: pur9-rg-def-phi). -/
def omegaComp : omega P Z ≅ (exceptional P i).obj (omega P X) :=
  letI := structure_isOver P X
  letI := structure_isOver P Z
  letI := FiniteEtaleNormalization.compactification P i
  letI := FiniteEtaleNormalization.compactification P (X ↘ Spec (.of P.field.k))
  letI := FiniteEtaleNormalization.compactification P (Z ↘ Spec (.of P.field.k))
  letI := FiniteEtaleNormalization.compactification P (i ≫ (X ↘ Spec (.of P.field.k)))
  (rightDerivedUpperShriekCongr (ModuleCat.{u + 1} P.Coefficient)
    (comp_over i (Spec (.of P.field.k))).symm).app
      (unit P (Spec (.of P.field.k))) ≪≫
    compIso P i (X ↘ Spec (.of P.field.k)) (unit P (Spec (.of P.field.k)))
      (unit_bounded P (Spec (.of P.field.k)))

/-- A determining equation for the displayed four-arrow composite. Tensor Phi with
T_Z(m), undo the root-normalized pullback comparison, apply inverse co-projection,
and reassemble T_X(N) with N=m+c. The result must be Pi_Z inverse, c, Ri!Pi_X.
Tensoring with T_Z(m) is faithful and invertible; hence this equation determines Phi,
including its scalar. It is the negative-twist formula of lem-pur-twist-cancellation
written without changing the published positive-power presentation of Pi.
Source: pur9-rg-def-phi, connected case (blueprint: pur9-rg-def-phi). -/
def ConnectedEquation (N m c : ℕ) (hN : N = m + c)
    [SmoothOfRelativeDimension N (X ↘ Spec (.of P.field.k))]
    [SmoothOfRelativeDimension m (Z ↘ Spec (.of P.field.k))]
    (φ : unit P Z ⟶ (exceptional P i).obj (P.diagonalTwist X c)) : Prop :=
  positiveEquation (smoothPurityTensor P.Coefficient X)
    (smoothPurityTensor P.Coefficient Z) (exceptional P i)
    (upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor
    (unit P Z) (P.diagonalTwist Z m) (P.diagonalTwist X c)
    (P.diagonalTwist X m) (P.diagonalTwist X N) (omega P X) (omega P Z)
    (unitProduct P (Z := Z) m) (orientation P X N) (orientation P Z m) (omegaComp P i)
    (((leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) i).app (P.diagonalTwist X m)) ≪≫
      compositionTwistPullback P i m)
    (positiveCoprojectionIso P i c m)
    ((compositionPowerAdd P X m c).symm ≪≫
      eqToIso (congrArg (P.diagonalTwist X) hN.symm)) φ

/-- Existence and uniqueness of the connected composite, fixed by its exact equation.
Source: pur9-rg-def-phi, connected definition (blueprint: pur9-rg-def-phi).
Proof: tensor with the inverse of T_Z(m). Lem-pur-twist-cancellation gives precisely
Pi_Z inverse, c_{a_X,i}, and Ri!Pi_X, then inverse co-projection and addition of
signed Tate powers with N-m=c. Naturality of the co-projection counit equation
identifies its tensor with T_Z(m) with ConnectedEquation. Conversely tensor by the
invertible Tate object is faithful, so any two arrows satisfying the equation agree.
This chooses only a uniquely determined morphism, with no arbitrary orientation. -/
theorem existsUnique_connected (N m c : ℕ) (hN : N = m + c)
    [SmoothOfRelativeDimension N (X ↘ Spec (.of P.field.k))]
    [SmoothOfRelativeDimension m (Z ↘ Spec (.of P.field.k))] :
    ∃! φ : unit P Z ⟶ (exceptional P i).obj (P.diagonalTwist X c),
      ConnectedEquation P i N m c hN φ := by
  sorry

/-- The prescribed connected-case comparison in its positive-power coordinates.
Source: pur9-rg-def-phi (blueprint: pur9-rg-def-phi). -/
def connected (N m c : ℕ) (hN : N = m + c)
    [SmoothOfRelativeDimension N (X ↘ Spec (.of P.field.k))]
    [SmoothOfRelativeDimension m (Z ↘ Spec (.of P.field.k))] :
    unit P Z ⟶ (exceptional P i).obj (P.diagonalTwist X c) :=
  (existsUnique_connected P i N m c hN).exists.choose

end Connected

/-- Coordinates for one connected clopen component and its inverse image in Z.
All fields are the geometric properties of such a component, not purity data.
The empty inverse image is permitted. Quantifying over all these coordinates makes
assembly independent of an enumeration or a choice of connected components.
Source: pur9-rg-def-phi, general case (blueprint: pur9-rg-def-phi). -/
structure Component (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))] where
  Xs : Scheme.{u}
  Zs : Scheme.{u}
  [overXs : Xs.Over (Spec (.of P.field.k))]
  [overZs : Zs.Over (Spec (.of P.field.k))]
  [ftXs : LocallyOfFiniteType (Xs ↘ Spec (.of P.field.k))]
  [qcXs : QuasiCompact (Xs ↘ Spec (.of P.field.k))]
  [sepXs : IsSeparated (Xs ↘ Spec (.of P.field.k))]
  [ftZs : LocallyOfFiniteType (Zs ↘ Spec (.of P.field.k))]
  [qcZs : QuasiCompact (Zs ↘ Spec (.of P.field.k))]
  [sepZs : IsSeparated (Zs ↘ Spec (.of P.field.k))]
  j : Xs ⟶ X
  jZ : Zs ⟶ Z
  is : Zs ⟶ Xs
  [overJ : j.IsOver (Spec (.of P.field.k))]
  [overJZ : jZ.IsOver (Spec (.of P.field.k))]
  [overIs : is.IsOver (Spec (.of P.field.k))]
  [openJ : IsOpenImmersion j]
  [closedJ : IsClosedImmersion j]
  [openJZ : IsOpenImmersion jZ]
  [closedJZ : IsClosedImmersion jZ]
  [closedIs : IsClosedImmersion is]
  [connectedXs : ConnectedSpace Xs]
  square : IsPullback jZ is i j

attribute [instance] Component.overXs Component.overZs Component.ftXs Component.qcXs
  Component.sepXs Component.ftZs Component.qcZs Component.sepZs Component.overJ
  Component.overJZ Component.overIs Component.openJ Component.closedJ Component.openJZ
  Component.closedJZ Component.closedIs Component.connectedXs

section Assembly
variable (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
  [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [IsSeparated (Z ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  (i : Z ⟶ X) [i.IsOver (Spec (.of P.field.k))] [IsClosedImmersion i]

/-- The displayed beta_s, including the canonical Tate-pullback coordinate change.
Its factors are Ri_s!(rho_j inverse), c_{j,i_s} inverse, equality of the two composites,
c_{i,jZ}, and rho_jZ. These are the standing functors and the counit-normalized rho.
Source: pur9-rg-def-phi, displayed beta_s (blueprint: pur9-rg-def-phi). -/
def componentBeta (C : Component P i) (c : ℕ) :
    (exceptional P C.is).obj (P.diagonalTwist C.Xs c) ⟶
      (P.smoothPurityPullback C.jZ).obj ((exceptional P i).obj (P.diagonalTwist X c)) :=
  letI := FiniteEtaleNormalization.compactification P C.is
  letI := FiniteEtaleNormalization.compactification P C.j
  letI := FiniteEtaleNormalization.compactification P C.jZ
  letI := FiniteEtaleNormalization.compactification P i
  letI := FiniteEtaleNormalization.compactification P (C.is ≫ C.j)
  letI := FiniteEtaleNormalization.compactification P (C.jZ ≫ i)
  (exceptional P C.is).map
    ((compositionTwistPullback P C.j c).inv ≫
      (rhoIso P C.j (P.diagonalTwist X c) (twist_bounded P c)).inv) ≫
    (compIso P C.is C.j (P.diagonalTwist X c) (twist_bounded P c)).inv ≫
    (rightDerivedUpperShriekCongr (ModuleCat.{u + 1} P.Coefficient) C.square.w.symm).hom.app
      (P.diagonalTwist X c) ≫
    (compIso P C.jZ i (P.diagonalTwist X c) (twist_bounded P c)).hom ≫
    (rhoIso P C.jZ ((exceptional P i).obj (P.diagonalTwist X c))
      (exceptional_bounded P i _ (twist_bounded P c))).hom

/-- The exact connected-component characterization of Phi. On an empty inverse image
restriction is zero. Otherwise every presentation of the two pure dimensions gives
the specified connected composite, transported by beta_s. The pullback of Lambda_Z
is identified with Lambda_Zs by the canonical root/unit comparison at power zero.
Source: pur9-rg-def-phi, general case (blueprint: pur9-rg-def-phi). -/
def ComponentEquations (c : ℕ)
    (φ : unit P Z ⟶ (exceptional P i).obj (P.diagonalTwist X c)) : Prop :=
  (IsEmpty Z → φ = 0) ∧ ∀ C : Component P i,
    (IsEmpty C.Zs → (P.smoothPurityPullback C.jZ).map φ = 0) ∧
    (∀ (N m : ℕ) (hN : N = m + c)
      [SmoothOfRelativeDimension N (C.Xs ↘ Spec (.of P.field.k))]
      [SmoothOfRelativeDimension m (C.Zs ↘ Spec (.of P.field.k))],
      (P.smoothPurityPullback C.jZ).map φ =
        (compositionTwistPullback P C.jZ 0).hom ≫
          connected P C.is N m c hN ≫ componentBeta P i C c)

/-- Existence and uniqueness of the assembled smooth-purity comparison.
Source: pur9-rg-def-phi, connected and general definitions
(blueprint: pur9-rg-def-phi).
Proof: smooth finite-type X is regular and Noetherian. Its connected components
are a finite clopen cover and each has a fixed pure smooth dimension N. For a
nonempty inverse image, regularity of Z over the perfect field gives smoothness
(lem-pur-regular-immersion-smooth-structure), and the stalkwise dimension equality
from the affine regular sequence gives pure dimension m with N=m+c.
The same dimension formula holds for the empty regular sequence at c=0.
Use existsUnique_connected on each
such component. On the empty inverse images use zero. The finite-clopen derived
restriction equivalence of lem-pur-finite-clopen-derived-decomposition is fully
faithful, so these component arrows glue to a unique global arrow. Its target
identifications are precisely componentBeta, the displayed rho/c paste. The
normalizations of c and rho at identities show that for connected X the identity
component gives the original connected composite. Naturality and the same
normalizations give the equations for every isomorphic choice of component
coordinates. If X or Z is empty, all relevant Hom sets are singletons and the
constructed arrow is zero. No smoothness or dimension witness is added as a
hypothesis: those properties follow from the geometric hypotheses and hreg. -/
theorem existsUnique_comparison (c : ℕ)
    (_hreg : WeilConjectures.PurityConventions.IsRegularOfPureCodimension i c)
    [Smooth (X ↘ Spec (.of P.field.k))] [IsRegular Z] :
    ∃! φ : unit P Z ⟶ (exceptional P i).obj (P.diagonalTwist X c),
      ComponentEquations P i c φ := by
  sorry

/-- The smooth-purity comparison for a regular immersion, assembled over the finite
connected clopen decomposition. Choice extracts the unique arrow with the exact
component equations; every piece uses the canonical orientations, c, and rho.
Source: main-20261015, pur9-rg-def-phi.md (blueprint: pur9-rg-def-phi). -/
def comparison (c : ℕ)
    (hreg : WeilConjectures.PurityConventions.IsRegularOfPureCodimension i c)
    [Smooth (X ↘ Spec (.of P.field.k))] [IsRegular Z] :
    unit P Z ⟶ (exceptional P i).obj (P.diagonalTwist X c) :=
  (existsUnique_comparison P i c hreg).exists.choose

end Assembly
end AlgebraicGeometry.ProEtale.RegularImmersionPurity
