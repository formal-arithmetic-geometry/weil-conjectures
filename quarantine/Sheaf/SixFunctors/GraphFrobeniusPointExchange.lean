/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

import Sheaf.Paper.CompletedAdicCoefficientDatum
import Sheaf.Paper.IntegralScalarExtensionConstructible
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Paper.IntegralFinitePullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Frobenius exchange and point transport give ordinary pullback

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
prop-trf-graph-frobenius-operator.proof.md, Step 2
(blueprint: lem-trf-graph-frobenius-point-exchange).

## Main definitions and statement

- `graphPointTransportPower`: the recorded point transport along powers of h, with
  the canonical identity-on-complexes change of localization size.
- `graphPointExchangeComposite`: point transport followed by the prescribed square mate.
- `graphPointOrdinaryPullback`: the recorded unit/Leray ordinary pullback.
- `graphFrobenius_point_exchange`: equality of these maps and naturality.

Pullbacks are expressed in the intrinsic finite-coefficient coordinates of the recorded
finite point transport. The ordinary pullback is transported from the tensor coordinates
by their canonical unit-preserving comparison. Powers of point transport are composed
using canonical pullback composition: on sections these compose restriction, distinguished
colimit insertion and the tensor unit for h^m. No k-linearity of g^m is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- Finiteness of exactly the positive quotient ring fixed in the conventions.
Source: blueprint finite-coefficient convention
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
instance graphPointCoefficientFinite (T : TraceFormulaCoefficientConventions.{u}) :
    Finite T.coefficientRing :=
  Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
    T.level T.level_pos

/-- The recorded point fibre in its original coefficient localization.
Source: blueprint finite point-fibre convention
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
abbrev graphPointSmallFibre (T : TraceFormulaCoefficientConventions.{u}) :
    proEtaleDerivedCategory (Spec (.of T.datum.k)) T.coefficientRing ⥤
      @DerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing))
        _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections T.datum.k T.coefficientRing) _ _ _

/-- The recorded point fibre in the localization of ordinary cohomology.
Source: blueprint ordinary cohomology convention
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
abbrev graphPointFibre (T : TraceFormulaCoefficientConventions.{u}) :
    proEtaleDerivedCategory (Spec (.of T.datum.k)) T.coefficientRing ⥤
      DerivedCategory.{u + 2} (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) :=
  (pointFiniteSections T.datum.k T.coefficientRing).mapDerivedCategory

/-- The identity on coefficient complexes, derived between the two localization sizes.
Source: blueprint coefficient-size convention; localization universal property
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
def graphPointLocalizationLift (T : TraceFormulaCoefficientConventions.{u}) :
    @DerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing))
        _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _) ⥤
      DerivedCategory.{u + 2} (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) :=
  @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    _ _ _ _ (𝟭 (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing))) _ _ _

/-- Canonical localization comparison, normalized by the identity on complexes.
Source: blueprint coefficient-size convention; exact derived composition
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
def graphPointFibreComparison (T : TraceFormulaCoefficientConventions.{u}) :
    T.graphPointSmallFibre ⋙ T.graphPointLocalizationLift ≅ T.graphPointFibre :=
  (@Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _) _
    (pointFiniteSections T.datum.k T.coefficientRing)
    (𝟭 (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing))) _ _ _ _ _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (Functor.rightUnitor (pointFiniteSections T.datum.k T.coefficientRing))

/-- Positive-level form of the recorded finite transport. Matching the level before
forming its coefficient categories retains the canonical instances at each level.
Source: blueprint restriction--insertion--tensor-unit formula
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
def graphPointTransportPositive (T : TraceFormulaCoefficientConventions.{u}) :
    (n : ℕ) → (hn : 1 ≤ n) →
    (N : proEtaleDerivedCategory (Spec (.of T.datum.k))
      ({ T with level := n, level_pos := hn }).coefficientRing) →
    ({ T with level := n, level_pos := hn }).graphPointSmallFibre.obj N ⟶
      ({ T with level := n, level_pos := hn }).graphPointSmallFibre.obj
        ((@sfIntrinsicDerivedPullback
          ({ T with level := n, level_pos := hn }).coefficientRing _
          (graphPointCoefficientFinite { T with level := n, level_pos := hn }) _ _
          (frobeniusPointIso T.datum).hom).obj N)
  | 0, hn, _ => False.elim (Nat.not_succ_le_zero 0 hn)
  | n + 1, _, N => frobeniusPointTransportFinite T.datum T.coefficients.l
      T.coefficients.different T.coefficientField n N

/-- Recorded finite point transport, at the arbitrary positive level fixed by T.
Source: blueprint restriction--insertion--tensor-unit formula
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
def graphPointTransportOne (T : TraceFormulaCoefficientConventions.{u})
    (N : proEtaleDerivedCategory (Spec (.of T.datum.k)) T.coefficientRing) :
    T.graphPointFibre.obj N ⟶ T.graphPointFibre.obj
      ((sfIntrinsicDerivedPullback T.coefficientRing (frobeniusPointIso T.datum).hom).obj N) :=
  (T.graphPointFibreComparison.inv.app N) ≫
    T.graphPointLocalizationLift.map
      (T.graphPointTransportPositive T.level T.level_pos N) ≫
    T.graphPointFibreComparison.hom.app _

/-- Iterated restriction--insertion--pullback transport. Canonical composition collapses
successive insertions to the distinguished insertion for h^m, and successive tensor units
send x to x tensor 1. The zero case is only the canonical identity normalization.
Source: blueprint Step 2, iota along h^m
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
def graphPointTransportPower (T : TraceFormulaCoefficientConventions.{u}) :
    (m : ℕ) → (N : proEtaleDerivedCategory (Spec (.of T.datum.k)) T.coefficientRing) →
    T.graphPointFibre.obj N ⟶
      T.graphPointFibre.obj
        ((sfIntrinsicDerivedPullback T.coefficientRing
          (HPow.hPow (α := End (Spec (.of T.datum.k)))
            (frobeniusPointIso T.datum).hom m)).obj N)
  | 0, N => T.graphPointFibre.map
      ((sfIntrinsicDerivedPullbackId T.coefficientRing (Spec (.of T.datum.k))).inv.app N)
  | m + 1, N =>
      T.graphPointTransportOne N ≫
        T.graphPointTransportPower m
          ((sfIntrinsicDerivedPullback T.coefficientRing (frobeniusPointIso T.datum).hom).obj
            N) ≫
        T.graphPointFibre.map
          ((sfIntrinsicDerivedPullbackComp T.coefficientRing
            (HPow.hPow (α := End (Spec (.of T.datum.k)))
              (frobeniusPointIso T.datum).hom m) (frobeniusPointIso T.datum).hom).inv.app N) ≫
        T.graphPointFibre.map
          (eqToHom (congrArg (fun h ↦ (sfIntrinsicDerivedPullback T.coefficientRing h).obj N)
            (pow_succ' (End.of (frobeniusPointIso T.datum).hom) m).symm))

/-- The ordinary Frobenius square mate, with its powers and semilinear base retained.
Source: blueprint Step 2, e_(m,M); the recorded ambient finite exchange
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
def graphPointExchange (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ) :=
  FrobeniusExchange.finiteExchange T.coefficientRing T.structureMap T.structureMap
    (HPow.hPow (α := End T.geometricBaseChange)
      (T.datum.geometricGaloisFrobenius T.X₀) m)
    (HPow.hPow (α := End (Spec (.of T.datum.k))) (frobeniusPointIso T.datum).hom m)
    (T.datum.frobenius_open_square T.X₀ T.X₀ (𝟙 T.X₀) m).2.2.1

/-- Ordinary RΓ = Fib_s composed with Ra_*, in exactly the recorded coefficient universe.
Source: blueprint ordinary-cohomology convention
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
abbrev graphPointSections (T : TraceFormulaCoefficientConventions.{u}) :=
  @finiteOrdinarySectionsFunctor.{u} T.datum T.coefficientRing _ T.geometricBaseChange
    ⟨T.structureMap⟩

/-- The composite Fib(e_m) after iota along h^m, before any Weil isomorphism is applied.
Source: blueprint Step 2, displayed equality
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
def graphPointExchangeComposite (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :=
  T.graphPointTransportPower m
      ((proEtaleConstantDerivedDirectImage T.structureMap T.coefficientRing).obj M) ≫
    T.graphPointFibre.map
      ((T.graphPointExchange m).app M)

/-- The canonical ordinary pullback in the same intrinsic pullback coordinates as e_m.
Source: blueprint Step 2, rho defined by adjunction unit and global sections of direct image
(blueprint: lem-trf-graph-frobenius-point-exchange). -/
def graphPointOrdinaryPullback (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :=
  @finiteOrdinaryPullback.{u} T.datum T.coefficientRing _ _ T.geometricBaseChange
      ⟨T.structureMap⟩
      (HPow.hPow (α := End T.geometricBaseChange)
        (T.datum.geometricGaloisFrobenius T.X₀) m) M ≫
    T.graphPointSections.map
      ((openSquareDerivedPullbackModel T.coefficientRing
        (HPow.hPow (α := End T.geometricBaseChange)
          (T.datum.geometricGaloisFrobenius T.X₀) m)).hom.app M)

/-- Ordinary Frobenius exchange followed by point transport equals ordinary cohomology
pullback, naturally on D^b_ctf(Y,A). The second clause spells out naturality in M.
Source: main-20261015 blueprint, prop-trf-graph-frobenius-operator.proof.md, Step 2
(blueprint: lem-trf-graph-frobenius-point-exchange).

Proof:
1. Put a = a_Y, g = g_Y^m, b = h^m. Paste the Cartesian Frobenius square m times.
   For u : U → s set W = Y ×_(a,u) U and V = Y ×_(a,bu) U. The square identification
   d : W ≅ V sends (y,v) to (g(y),v). This needs no assertion that g is over k.
   By lem-weil-proetale-isomorphism-inverse-image, inverse image along g and b is exact
   relabelling. The finite module tensor comparison is x to x tensor 1.
2. Choose a K-injective representative I of M using def-weil-pbc-proetale-operations.
   The exact left adjoint a* makes a_*I K-injective. The equivalence g* is also right
   adjoint to its exact inverse, so g*I is K-injective, by
   lem-weil-pbc-right-adjoint-preserves-kinjective. Exact point evaluation computes
   both cohomology objects as I(Y) and (g*I)(Y), by
   lem-weil-point-proetale-sections-exact and def-weil-proetale-module-direct-image.
3. The fraction characterization of lem-pc-pre-derived-adjoint-functors-general
   identifies the derived exchange with the termwise underived mate on I: its transpose
   is the canonical square comparison followed by g* of the a counit. The composition
   comparison is termwise by lem-weil-pbc-proetale-derived-pullback-composition.
4. The colimit adjunction of lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction
   sends an insertion to restriction. Thus the mate at U is restriction along d,
   preserving the scalar tensor factor and in particular 1. This formula commutes with
   restrictions and sheafification, by def-weil-proetale-inverse-image.
5. At U = s the point transport is restriction along the projection V → Y, followed
   by the distinguished insertion and tensor unit. The exchange then restricts along
   d. Their composite is restriction along g, because the projection composed with d
   is g. This computes Fib_s(e_m) after iota, by def-weil-finite-coefficient-point.
6. Evaluate the g adjunction unit at the final object. After the canonical global
   sections identification for direct image, it inserts at the final-object index;
   relabelling identifies this with the same restriction I(g), with tensor scalar 1.
   The derived fraction characterization identifies this with rho. The canonical
   constant coefficient map fixes scalars, so no coefficient automorphism occurs.
   The recorded finiteOrdinaryPullback uses precisely this unit and canonical Leray
   comparison. Its unit-preserving pullback coordinate change gives the right side
   below. All restriction, insertion, tensor, counit and resolution maps commute with
   maps of complexes; bifunctoriality of the derived adjunction gives naturality.
-/
theorem graphFrobenius_point_exchange (T : TraceFormulaCoefficientConventions.{u})
    [IsProper T.X₀.hom] (m : ℕ) (_hm : 1 ≤ m) :
    (∀ M : T.boundedConstructibleFiniteTor.FullSubcategory,
      T.graphPointExchangeComposite m M.obj = T.graphPointOrdinaryPullback m M.obj) ∧
    (∀ (M N : T.boundedConstructibleFiniteTor.FullSubcategory) (f : M ⟶ N),
      T.graphPointSections.map f.hom ≫ T.graphPointExchangeComposite m N.obj =
        T.graphPointExchangeComposite m M.obj ≫
          T.graphPointSections.map
            ((sfIntrinsicDerivedPullback T.coefficientRing
              (HPow.hPow (α := End T.geometricBaseChange)
                (T.datum.geometricGaloisFrobenius T.X₀) m)).map f.hom)) := by
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
