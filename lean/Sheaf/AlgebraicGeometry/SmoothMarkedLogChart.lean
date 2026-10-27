/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.AffineSpace

import Sheaf.AlgebraicGeometry.LogSmoothLogRegular

/-! # Smooth and marked associated log charts

Source: Illusie--Laszlo--Orgogozo, Exposé VI 1.1, 1.4, 1.8 and Proposition 1.9,
printed pp. 69--71 (blueprint: lem-trf-smooth-marked-log-chart).

The two statements give the unmarked and marked cases. A global `IsChart`, together
with its structural formula, specifies the associated log structure up to its unique
chart-preserving isomorphism; no log structure is chosen from a mere existence proof.
The base closed subset is represented by its open complement `UY`, and the source
boundary by `Uᶜ`. The monoid `P × Multiplicative ℕ` represents `P ⊕ ℕ`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The smooth case with no marking, including its identity monoid-base-change comparison.
Source: ILO VI 1.4, 1.8 and Proposition 1.9, printed pp. 69--71
(blueprint: lem-trf-smooth-marked-log-chart).

Proof:
1. Use Q = P in the smooth case and Q = P × ℕ in the marked case. The latter
   is fs by componentwise finite generation, injectivity into the group completion,
   and saturation. The associated stalk pushouts extend the base chart inclusion
   to a log morphism, sending a pair (p,a) to (h(p),g*a). Pullback of units respects
   every pushout relation (def-trf-fs-log-blowup).
2. Groupification gives the identity or a ↦ (a,0), with cokernel zero or ℤ.
   On monomial bases ℤ[P × ℕ] = ℤ[P][t]. Base change therefore identifies the
   comparison target with Y or A¹_Y; the comparison is g or c because it fixes
   base functions and pulls the extra coordinate back to z (def-sbc-affine-space).
3. A local map of strict local rings reflects units. The associated log stalk is
   trivial exactly when all chart images are units. This means g(w) ∈ UY, and in
   the marked case also z is a unit at w. Hence the triviality locus is exactly U
   (def-trf-log-regular-pair).
4. Apply logSmooth_logRegular to these fs charts: the base is log regular, the
   group map is injective with torsion-free cokernel, and the comparison is the
   given smooth g or étale c. Its divisorial recovery identifies L with O ∩ j*Oˣ
   over U, and proves density. The closed complement is nowhere dense and its
   divisorial structure is fs and log regular, as required for the resulting pair.
-/
theorem smooth_associatedLogChart
    (Y : FineSaturatedLogScheme.{u}) (UY : Y.scheme.Opens) (hdY : DenseRange UY.ι)
    (hpair : @IsDivisorialFineSaturatedLogRegularPair Y.scheme UY.toScheme UY.ι
      inferInstance Y.locallyNoetherian hdY)
    (eY : Y.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf UY.ι)
    (heY : eY.hom ≫ divisorialStructuralMap UY.ι = Y.logStructure.alpha)
    (P : Type u) [CommMonoid P] (hP : IsFineSaturatedMonoid P)
    (a : P →* Y.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y.scheme))))
    (ha : Y.logStructure.IsChart (Scheme.Etale.mk (𝟙 Y.scheme)) a)
    (W : Scheme.{u}) [IsLocallyNoetherian W]
    (g : W ⟶ Y.scheme) [Smooth g]
    (L : EtaleLogStructure W)
    (b : P →* L.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (hb : L.IsChart (Scheme.Etale.mk (𝟙 W)) b)
    (hab : ∀ p : P, L.alpha.app (op (Scheme.Etale.mk (𝟙 W))) (b p) =
      g.appTop (Y.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 Y.scheme))) (a p)))
    (U : W.Opens) (hU : U = g ⁻¹ᵁ UY) :
    ∃ hfs : L.IsFineSaturated,
      (FineSaturatedLogScheme.mk W inferInstance L hfs).IsLogRegular ∧
      (∃ (f : EtaleLogHom (FineSaturatedLogScheme.mk W inferInstance L hfs) Y)
        (hf : g ≫ 𝟙 Y.scheme = 𝟙 W ≫ f.base),
        ∀ p : P, f.sectionMap (Scheme.Etale.mk (𝟙 Y.scheme))
          (Scheme.Etale.mk (𝟙 W)) g hf (a p) = b p) ∧
      Function.Injective (Algebra.GrothendieckGroup.lift
        ((Algebra.GrothendieckGroup.of (M := P)).comp
          (MonoidHom.id P))) ∧
      Subsingleton (Algebra.GrothendieckGroup P ⧸
        (Algebra.GrothendieckGroup.lift
        ((Algebra.GrothendieckGroup.of (M := P)).comp
          (MonoidHom.id P))).range) ∧
      (∃ (e :
        pullback (Y.logStructure.chartToSpec (Scheme.Etale.mk (𝟙 Y.scheme)) a)
          (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ
          (MonoidHom.id P)))) ≅ Y.scheme)
        (k : W ⟶ _),
          e.hom = pullback.fst _ _ ∧
          k ≫ pullback.snd _ _ =
            L.chartToSpec (Scheme.Etale.mk (𝟙 W)) b ∧
          k ≫ e.hom = g) ∧
      ∃ hd : DenseRange U.ι,
        L.trivialityLocus = (U : Set W) ∧
        (∃ e : L.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι,
          e.hom ≫ divisorialStructuralMap U.ι = L.alpha) ∧
        interior (closure ((U : Set W)ᶜ)) = ∅ ∧
        IsDivisorialFineSaturatedLogRegularPair W U.toScheme U.ι hd := by
  sorry

/-- The marked étale-coordinate case, including the normalized affine-line comparison.
Source: ILO VI 1.4, 1.8 and Proposition 1.9, printed pp. 69--71
(blueprint: lem-trf-smooth-marked-log-chart).

Proof:
1. Use Q = P in the smooth case and Q = P × ℕ in the marked case. The latter
   is fs by componentwise finite generation, injectivity into the group completion,
   and saturation. The associated stalk pushouts extend the base chart inclusion
   to a log morphism, sending a pair (p,a) to (h(p),g*a). Pullback of units respects
   every pushout relation (def-trf-fs-log-blowup).
2. Groupification gives the identity or a ↦ (a,0), with cokernel zero or ℤ.
   On monomial bases ℤ[P × ℕ] = ℤ[P][t]. Base change therefore identifies the
   comparison target with Y or A¹_Y; the comparison is g or c because it fixes
   base functions and pulls the extra coordinate back to z (def-sbc-affine-space).
3. A local map of strict local rings reflects units. The associated log stalk is
   trivial exactly when all chart images are units. This means g(w) ∈ UY, and in
   the marked case also z is a unit at w. Hence the triviality locus is exactly U
   (def-trf-log-regular-pair).
4. Apply logSmooth_logRegular to these fs charts: the base is log regular, the
   group map is injective with torsion-free cokernel, and the comparison is the
   given smooth g or étale c. Its divisorial recovery identifies L with O ∩ j*Oˣ
   over U, and proves density. The closed complement is nowhere dense and its
   divisorial structure is fs and log regular, as required for the resulting pair.
-/
theorem marked_associatedLogChart
    (Y : FineSaturatedLogScheme.{u}) (UY : Y.scheme.Opens) (hdY : DenseRange UY.ι)
    (hpair : @IsDivisorialFineSaturatedLogRegularPair Y.scheme UY.toScheme UY.ι
      inferInstance Y.locallyNoetherian hdY)
    (eY : Y.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf UY.ι)
    (heY : eY.hom ≫ divisorialStructuralMap UY.ι = Y.logStructure.alpha)
    (P : Type u) [CommMonoid P] (hP : IsFineSaturatedMonoid P)
    (a : P →* Y.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y.scheme))))
    (ha : Y.logStructure.IsChart (Scheme.Etale.mk (𝟙 Y.scheme)) a)
    (W : Scheme.{u}) [IsLocallyNoetherian W]
    (c : W ⟶ AffineSpace (ULift.{u} (Fin 1)) Y.scheme) [Etale c]
    (g : W ⟶ Y.scheme) (hg : g = c ≫ (AffineSpace (ULift.{u} (Fin 1)) Y.scheme ↘ Y.scheme))
    (z : Γ(W, ⊤))
    (hz : z = c.appTop (AffineSpace.coord (S := Y.scheme) (ULift.up 0)))
    (L : EtaleLogStructure W)
    (b : (P × Multiplicative ℕ) →* L.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (hb : L.IsChart (Scheme.Etale.mk (𝟙 W)) b)
    (hab : ∀ p : P × Multiplicative ℕ,
      L.alpha.app (op (Scheme.Etale.mk (𝟙 W))) (b p) =
        g.appTop (Y.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 Y.scheme))) (a p.1)) *
          z ^ p.2.toAdd)
    (U : W.Opens) (hU : U = g ⁻¹ᵁ UY ⊓ W.basicOpen z) :
    ∃ hfs : L.IsFineSaturated,
      (FineSaturatedLogScheme.mk W inferInstance L hfs).IsLogRegular ∧
      (∃ (f : EtaleLogHom (FineSaturatedLogScheme.mk W inferInstance L hfs) Y)
        (hf : g ≫ 𝟙 Y.scheme = 𝟙 W ≫ f.base),
        ∀ p : P, f.sectionMap (Scheme.Etale.mk (𝟙 Y.scheme))
          (Scheme.Etale.mk (𝟙 W)) g hf (a p) = b (p, 1)) ∧
      Function.Injective (Algebra.GrothendieckGroup.lift
        ((Algebra.GrothendieckGroup.of (M := P × Multiplicative ℕ)).comp
          (MonoidHom.inl P (Multiplicative ℕ)))) ∧
      Nonempty ((Algebra.GrothendieckGroup (P × Multiplicative ℕ) ⧸
        (Algebra.GrothendieckGroup.lift
        ((Algebra.GrothendieckGroup.of (M := P × Multiplicative ℕ)).comp
          (MonoidHom.inl P (Multiplicative ℕ)))).range) ≃* Multiplicative ℤ) ∧
      (∃ (e :
        pullback (Y.logStructure.chartToSpec (Scheme.Etale.mk (𝟙 Y.scheme)) a)
          (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ
          (MonoidHom.inl P (Multiplicative ℕ))))) ≅
          AffineSpace (ULift.{u} (Fin 1)) Y.scheme) (k : W ⟶ _),
          e.hom ≫ (AffineSpace (ULift.{u} (Fin 1)) Y.scheme ↘ Y.scheme) =
            pullback.fst _ _ ∧
          AffineSpace.coord (S := Y.scheme) (ULift.up 0) =
            (e.inv ≫ pullback.snd _ _).appTop
              ((Scheme.ΓSpecIso (.of (MonoidAlgebra ℤ (P × Multiplicative ℕ)))).inv
                (MonoidAlgebra.single (1, Multiplicative.ofAdd 1) 1)) ∧
          k ≫ pullback.snd _ _ =
            L.chartToSpec (Scheme.Etale.mk (𝟙 W)) b ∧
          k ≫ e.hom = c) ∧
      ∃ hd : DenseRange U.ι,
        L.trivialityLocus = (U : Set W) ∧
        (∃ e : L.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι,
          e.hom ≫ divisorialStructuralMap U.ι = L.alpha) ∧
        interior (closure ((U : Set W)ᶜ)) = ∅ ∧
        IsDivisorialFineSaturatedLogRegularPair W U.toScheme U.ι hd := by
  sorry

end AlgebraicGeometry
