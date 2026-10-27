/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-! # Localization and local comparison for regular functions

Source: Stacks Project, Tag 02KH, degree zero; the fraction and germ argument in
`lem-sfb-qcqs-functions-local-comparison` (blueprint: lem-sfb-qcqs-functions-local-comparison).

The auxiliary definitions give actual chart morphisms, pullbacks, section maps and fractions.
Localization of the ring M uses the image of the denominator submonoid in M. Algebra
compatibility is expressed by coefficient equations for ring equivalences. Arbitrary
localization presentations include the local ring itself and iterated localizations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The restriction to V followed by its canonical map to Spec Γ(V).
Source: Stacks 02KH, affine-base reduction
(blueprint: lem-sfb-qcqs-functions-local-comparison). -/
def qcqsFunctionsChart {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens) :
    (f ⁻¹ᵁ V).toScheme ⟶ Spec Γ(T, V) :=
  (f ∣_ V) ≫ V.toSpecΓ

/-- Base change of the inverse-image open along an R-algebra B.
Source: Stacks 02KH, cartesian square
(blueprint: lem-sfb-qcqs-functions-local-comparison). -/
abbrev qcqsFunctionsBaseChange {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens)
    (B : CommRingCat.{u}) (φ : Γ(T, V) →+* B) : Scheme.{u} :=
  pullback (qcqsFunctionsChart f V) (Spec.map (CommRingCat.ofHom φ))

/-- Pullback of a numerator m in Γ(f⁻¹V), using the canonical open-section identification.
Source: Stacks 02KH, degree-zero comparison
(blueprint: lem-sfb-qcqs-functions-local-comparison). -/
def qcqsFunctionsNumerator {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens)
    (B : CommRingCat.{u}) (φ : Γ(T, V) →+* B) :
    Γ(Y, f ⁻¹ᵁ V) →+* Γ(qcqsFunctionsBaseChange f V B φ, ⊤) :=
  ((f ⁻¹ᵁ V).topIso.inv ≫
    (pullback.fst (qcqsFunctionsChart f V) (Spec.map (CommRingCat.ofHom φ))).appTop).hom

/-- The structural coefficient map from B to sections on the local base change.
Source: Stacks 02KH, degree-zero comparison
(blueprint: lem-sfb-qcqs-functions-local-comparison). -/
def qcqsFunctionsCoefficient {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens)
    (B : CommRingCat.{u}) (φ : Γ(T, V) →+* B) :
    B →+* Γ(qcqsFunctionsBaseChange f V B φ, ⊤) :=
  ((Scheme.ΓSpecIso B).inv ≫
    (pullback.snd (qcqsFunctionsChart f V) (Spec.map (CommRingCat.ofHom φ))).appTop).hom

/-- Ordinary localization S⁻¹M, with denominators mapped from R into M by f sharp.
Source: Stacks algebra.tex, Tag 00CO
(blueprint: lem-sfb-qcqs-functions-local-comparison). -/
abbrev qcqsFunctionsLocalization {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens)
    (S : Submonoid Γ(T, V)) : Type u :=
  Localization (S.map (f.app V).hom)

/-- The fraction m/s in the ordinary localization of the section ring.
Source: Stacks algebra.tex, Tag 00CO
(blueprint: lem-sfb-qcqs-functions-local-comparison). -/
def qcqsFunctionsFraction {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens)
    (S : Submonoid Γ(T, V)) (m : Γ(Y, f ⁻¹ᵁ V)) (s : S) :
    qcqsFunctionsLocalization f V S :=
  Localization.mk m ⟨f.app V s, ⟨s, s.property, rfl⟩⟩

/-- The structure presheaf pushed forward along f, with Mathlib's ring stalks and germs.
Source: Stacks sheaves.tex, Tags 007I and 007T
(blueprint: lem-sfb-qcqs-functions-local-comparison). -/
abbrev qcqsFunctionsPushforward {Y T : Scheme.{u}} (f : Y ⟶ T) :
    TopCat.Presheaf CommRingCat.{u} T :=
  (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).obj Y.presheaf

/-- Localization, stalk comparison, and the stalk criterion for the canonical sharp map.
Source: Stacks coherent.tex, Tag 02KH, i = 0, and sheaves.tex, Tag 007T
(blueprint: lem-sfb-qcqs-functions-local-comparison).

Proof plan, following the node's ten steps:
1. The inverse-image open is a base change (lem-weil-pbc-open-preimage-fibre-product).
   Qcqs permanence and qcqs-over-affine make its source a qcqs scheme.
2. Localization is flat (lem-weil-pbc-localization-flat); its Spec map is flat
   (lem-weil-pbc-flat-ring-map-iff-flat-affine), even when zero is a denominator.
3. The tensor-localization identification (lem-weil-pbc-localization-base-change) sends
   m tensor a/s to am/s, with inverse m/s to m tensor 1/s.
4. Apply lem-weil-pbc-flat-base-change-global-sections-qcqs. Its degree-zero formula
   gives the stated fraction equation and the coefficient equation.
5. Further-localization maps agree on numerators and inverted denominators; hence the
   naturality square commutes. This also applies to iterated localizations.
6. On D(h), affine-open localization and the open-preimage pullback identify sections
   with M_h. The principal opens form a basis
   (lem-weil-pbc-affine-open-section-vanishing-prime and
   lem-weil-pbc-spec-localization-away-basic-open).
7. Send m/s to the germ of the corresponding fraction on a principal neighborhood.
   Fraction relations make this a ring map; affine-open stalk localization identifies
   the scalar ring (lem-weil-pbc-affine-open-stalk-localization).
8. Every germ comes from a principal neighborhood and is therefore such a fraction.
   A fraction with zero germ vanishes after a further principal restriction; clearing
   that denominator proves injectivity, including zero divisors and empty preimages.
9. Apply step 4 with B the local ring. The germ equations identify beta on stalks
   with its structural coefficient map, and identify the composite with pullback.
10. The stalk criterion (lem-weil-pbc-sets-sheaf-iso-on-stalks) detects invertibility
    of beta. The sectionwise inverse is a ring map, and uniqueness of inverses
    makes it commute with every restriction. -/
theorem qcqs_functions_local_comparison {Y T : Scheme.{u}} (f : Y ⟶ T)
    [QuasiCompact f] [QuasiSeparated f] :
    (∀ (V : T.Opens) (hV : IsAffineOpen V),
      ∃ θ : ∀ (S : Submonoid Γ(T, V)) (B : CommRingCat.{u}) (φ : Γ(T, V) →+* B),
          @IsLocalization Γ(T, V) _ S B _ φ.toAlgebra →
          qcqsFunctionsLocalization f V S ≃+* Γ(qcqsFunctionsBaseChange f V B φ, ⊤),
        (∀ (S : Submonoid Γ(T, V)) (B : CommRingCat.{u}) (φ : Γ(T, V) →+* B)
          (hB : @IsLocalization Γ(T, V) _ S B _ φ.toAlgebra)
          (m : Γ(Y, f ⁻¹ᵁ V)) (s : S),
          θ S B φ hB (qcqsFunctionsFraction f V S m s) *
              qcqsFunctionsCoefficient f V B φ (φ s) = qcqsFunctionsNumerator f V B φ m) ∧
        (∀ (S : Submonoid Γ(T, V)) (B : CommRingCat.{u}) (φ : Γ(T, V) →+* B)
          (hB : @IsLocalization Γ(T, V) _ S B _ φ.toAlgebra)
          (a : Γ(T, V)) (s : S),
          θ S B φ hB (qcqsFunctionsFraction f V S (f.app V a) s) *
              qcqsFunctionsCoefficient f V B φ (φ s) = qcqsFunctionsCoefficient f V B φ (φ a)) ∧
        (∀ (S S' : Submonoid Γ(T, V)) (B C : CommRingCat.{u})
          (φ : Γ(T, V) →+* B) (ψ : Γ(T, V) →+* C)
          (hB : @IsLocalization Γ(T, V) _ S B _ φ.toAlgebra)
          (hC : @IsLocalization Γ(T, V) _ S' C _ ψ.toAlgebra)
          (t : B →+* C) (_ : t.comp φ = ψ)
          (q : qcqsFunctionsBaseChange f V C ψ ⟶ qcqsFunctionsBaseChange f V B φ)
          (_ : q ≫ pullback.fst _ _ = pullback.fst _ _)
          (_ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom t))
          (l : qcqsFunctionsLocalization f V S →+* qcqsFunctionsLocalization f V S')
          (_ : ∀ m : Γ(Y, f ⁻¹ᵁ V),
            l (qcqsFunctionsFraction f V S m 1) = qcqsFunctionsFraction f V S' m 1)
          (z : qcqsFunctionsLocalization f V S),
          θ S' C ψ hC (l z) = q.appTop (θ S B φ hB z)) ∧
        (∀ y : V, ∃ e : qcqsFunctionsLocalization f V
            (hV.primeIdealOf y).asIdeal.primeCompl ≃+* (qcqsFunctionsPushforward f).stalk y,
          (∀ (m : Γ(Y, f ⁻¹ᵁ V)) (s : (hV.primeIdealOf y).asIdeal.primeCompl),
            e (qcqsFunctionsFraction f V _ m s) *
                (qcqsFunctionsPushforward f).germ V y y.property (f.app V s) =
              (qcqsFunctionsPushforward f).germ V y y.property m) ∧
          (∀ (W : T.Opens) (i : W ⟶ V) (hy : (y : T) ∈ W)
            (m : Γ(Y, f ⁻¹ᵁ V)) (s : (hV.primeIdealOf y).asIdeal.primeCompl)
            (z : Γ(Y, f ⁻¹ᵁ W)),
            (qcqsFunctionsPushforward f).map i.op m =
              (qcqsFunctionsPushforward f).map i.op (f.app V s) *
                @id ((qcqsFunctionsPushforward f).obj (op W)) z →
            e.symm ((qcqsFunctionsPushforward f).germ W y hy z) =
              qcqsFunctionsFraction f V _ m s) ∧
          (∀ a : T.presheaf.stalk y,
            θ (hV.primeIdealOf y).asIdeal.primeCompl (T.presheaf.stalk y)
                (T.presheaf.germ V y y.property).hom (hV.isLocalization_stalk y)
                (e.symm (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map f.c) a)) =
              qcqsFunctionsCoefficient f V (T.presheaf.stalk y)
                (T.presheaf.germ V y y.property).hom a))) ∧
    (IsIso f.c ↔ ∀ (V : T.Opens) (_ : IsAffineOpen V) (y : V),
      Function.Bijective (qcqsFunctionsCoefficient f V (T.presheaf.stalk y)
        (T.presheaf.germ V y y.property).hom)) ∧
    (IsIso f.c → ∃ σ : ∀ U : T.Opens, Γ(Y, f ⁻¹ᵁ U) ≃+* Γ(T, U),
      (∀ (U : T.Opens) (a : Γ(T, U)), σ U (f.app U a) = a) ∧
      (∀ (U : T.Opens) (b : Γ(Y, f ⁻¹ᵁ U)), f.app U (σ U b) = b) ∧
      (∀ (U W : T.Opens) (i : W ⟶ U) (b : Γ(Y, f ⁻¹ᵁ U)),
        σ W ((qcqsFunctionsPushforward f).map i.op b) = T.presheaf.map i.op (σ U b))) := by
  sorry

end

end AlgebraicGeometry
