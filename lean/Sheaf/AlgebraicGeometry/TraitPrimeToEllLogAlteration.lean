/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Algebra.MonoidAlgebra.Basic

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
import Sheaf.AlgebraicGeometry.NormalScheme
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.AlgebraicGeometry.GabberLogSmoothEquivariantModification
import Sheaf.AlgebraicGeometry.LogRegularProjectiveLogResolution
import Sheaf.AlgebraicGeometry.ProjectiveFiniteGroupQuotient
import Sheaf.AlgebraicGeometry.TameTraitQuotientLogEtale
import Sheaf.AlgebraicGeometry.TorsorSubgroupQuotientFiniteEtale
import Sheaf.AlgebraicGeometry.TraitSemistableGaloisAlteration
import Sheaf.DeligneLaumon.TraitLogSmoothUniformizerChart

/-!
# Prime-to-ell log-smooth alteration over a trait

Source: ILO, Travaux de Gabber, Exposé XVI, §3.7, printed pp. 254--255,
geometric construction before the purity argument
(blueprint: lem-per-trait-prime-to-ell-log-alteration).

The chart helpers spell out the fixed uniformizer chart, including invertible torsion.
A global lift of the uniformizer chart specifies the log morphism from the canonical
trait log structure. Its compatibility with local source charts is retained explicitly.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Group completion of a uniformizer-chart monoid map. Source: ILO XVI 3.6.3, 3.7
(blueprint: lem-per-trait-prime-to-ell-log-alteration). -/
noncomputable def uniformizerLogChartGroupMap {P : Type u} [CommMonoid P]
    (g : Multiplicative (ULift.{u} ℕ) →* P) :
    Algebra.GrothendieckGroup (Multiplicative (ULift.{u} ℕ)) →*
      Algebra.GrothendieckGroup P :=
  Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := P)).comp g)

/-- An fs source chart compatible with a prescribed global lift of the uniformizer.
The target chart is the canonical `ℕ → A`, and both scheme maps are pinned on every
monomial. The comparison is pinned by both projections, so it is the canonical map.
Source: ILO XVI 3.6.3 and 3.7
(blueprint: lem-per-trait-prime-to-ell-log-alteration). -/
structure TraitUniformizerLogChart (Y : Scheme.{u}) (M : EtaleLogStructure Y)
    (A : CommRingCat.{u}) (q : Y ⟶ Spec A) (π : A)
    (b : Multiplicative (ULift.{u} ℕ) →*
      M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) where
  V : Y.Etale
  P : Type u
  instP : CommMonoid P
  fineP : @IsFineSaturatedMonoid P instP
  chart : P →* M.monoidSheaf.obj.obj (op V)
  isChart : M.IsChart V chart
  g : Multiplicative (ULift.{u} ℕ) →* P
  compatibility : ∀ n : Multiplicative (ULift.{u} ℕ),
    chart (g n) =
      M.monoidSheaf.obj.map
        (MorphismProperty.Over.homMk V.hom (Category.comp_id V.hom)).op (b n)
  y : Spec A ⟶ Spec (.of (MonoidAlgebra ℤ (Multiplicative (ULift.{u} ℕ))))
  y_chart : ∀ n : Multiplicative (ULift.{u} ℕ),
    y.appTop ((Scheme.ΓSpecIso
      (.of (MonoidAlgebra ℤ (Multiplicative (ULift.{u} ℕ))))).inv
        (MonoidAlgebra.single n 1)) = (Scheme.ΓSpecIso A).inv (π ^ n.toAdd.down)
  x : V.left ⟶ Spec (.of (MonoidAlgebra ℤ P))
  x_chart : ∀ p : P,
    x.appTop ((Scheme.ΓSpecIso (.of (MonoidAlgebra ℤ P))).inv
      (MonoidAlgebra.single p 1)) = M.alpha.app (op V) (chart p)
  comparison : V.left ⟶
    pullback y (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g)))
  comparison_fst : comparison ≫ pullback.fst y
    (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g))) = V.hom ≫ q
  comparison_snd : comparison ≫ pullback.snd y
    (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g))) = x
  gp_injective : Function.Injective (uniformizerLogChartGroupMap g)
  torsion_finite : Finite (CommGroup.torsion
    (Algebra.GrothendieckGroup P ⧸ (uniformizerLogChartGroupMap g).range))
  torsion_invertible : ∀ z : V.left, IsUnit
    (Nat.card (CommGroup.torsion
      (Algebra.GrothendieckGroup P ⧸ (uniformizerLogChartGroupMap g).range)) :
        V.left.presheaf.stalk z)
  smooth : Smooth comparison

/-- The geometric prime-to-ell alteration theorem, with the uniformizer form of log
smoothness. Source: ILO XVI 3.7, pp. 254--255
(blueprint: lem-per-trait-prime-to-ell-log-alteration).

Proof (the eight steps of the DAG):
1. Apply lem-per-trait-semistable-galois-alteration to obtain the semistable G-model
   and its connected finite étale G-torsor on a nonempty open of X. Constant-field
   normalization is part of this input and does not change the eventual degree over X.
2. Choose an ell-Sylow H using lem-weil-pbc-sylow-subgroup-prime-index. Its index is
   prime to ell. By lem-per-tame-trait-quotient-log-etale, T = S prime/H is a finite
   dominant trait over S, and the semistable model is log smooth over T. The degree
   of S prime/T need only divide the order of H; faithfulness on the trait is unneeded.
3. The finite map T → S is separated. The graph of the model's T-map is closed by
   lem-weil-pbc-closed-immersion-base-change. Pull back the S-projective embedding
   and use the graph to obtain quasi-projectivity over T. Affine generators over R
   also generate over the finite intermediate algebra, giving finite type over T.
4. Stabilizer orders divide the ell-power order of H and are invertible on the trait.
   The torsor makes the action generically free. Apply
   lem-per-gabber-log-smooth-equivariant-modification to obtain a projective birational
   H-model whose quotient is fs log regular and log smooth over T.
5. Compose the projective maps using lem-trf-h-projective-composition. Apply
   lem-per-projective-finite-group-quotient over T and over X. Categorical uniqueness
   identifies the quotients. It is integral and quasi-projective of finite type over T,
   and projective and dominant over X; the quotient map is finite surjective.
6. T is excellent by lem-per-complete-local-excellence. Apply
   lem-per-log-regular-projective-log-resolution to the quotient. This gives regular Y,
   projective birational over the quotient and still log smooth over T. Apply
   lem-per-trait-log-smooth-uniformizer-chart for the fixed injective uniformizer charts.
7. Shrink the torsor open away from the proper image of the modification's bad locus.
   By lem-per-torsor-subgroup-quotient-finite-etale the quotient on this open is finite
   étale of degree [G:H], positive and prime to ell, with no normality of H required.
8. Remove the proper image of the log resolution's bad locus as well, using
   lem-kun-projective-implies-proper and def-weil-proper-morphism. The same nonempty
   open then gives finite étaleness of Y → X and function-field degree [G:H]. Combine
   the projective embeddings using lem-chow-segre for quasi-projectivity over S and T;
   lem-sfb-finite-type-composition-base-change supplies both finite-type assertions.
-/
theorem exists_trait_primeToEll_log_alteration
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsStrictlyHenselianLocalRing R] [CharZero (FractionRing R)]
    (hchar : ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField R) p)
    (ell : ℕ) (hell : ell.Prime) (hinv : IsUnit (ell : R))
    (X : Scheme.{u}) [IsIntegral X] (hreg : IsRegularScheme X)
    (s : X ⟶ Spec R) [Flat s] [LocallyOfFiniteType s] [QuasiCompact s]
    (hqp : ∃ (N : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec R)),
      IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec R) ↘ Spec R = s) :
    ∃ (A : CommRingCat.{u}) (hA : IsDomain A)
      (_ : @IsDiscreteValuationRing A inferInstance hA)
      (t : Spec A ⟶ Spec R) (Y : FineSaturatedLogScheme.{u})
      (q : Y.scheme ⟶ Spec A) (f : Y.scheme ⟶ X) (d : ℕ) (π : A)
      (b : Multiplicative (ULift.{u} ℕ) →*
        Y.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 Y.scheme)))),
      IsFinite t ∧ IsDominant t ∧ IsIntegral Y.scheme ∧ IsRegularScheme Y.scheme ∧
      LocallyOfFiniteType q ∧ QuasiCompact q ∧
      LocallyOfFiniteType (q ≫ t) ∧ QuasiCompact (q ≫ t) ∧
      (∃ (N : ℕ) (i : Y.scheme ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec A)),
        IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec A) ↘ Spec A = q) ∧
      (∃ (N : ℕ) (i : Y.scheme ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec R)),
        IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec R) ↘ Spec R = q ≫ t) ∧
      f ≫ s = q ≫ t ∧ IsHProjective f ∧ IsDominant f ∧ 0 < d ∧ ¬ell ∣ d ∧
      (∃ U : X.Opens, Nonempty U ∧ IsFinite (f ∣_ U) ∧ Etale (f ∣_ U)) ∧
      f.fiberDegree (genericPoint X) = d ∧ Irreducible π ∧
      (∀ n : Multiplicative (ULift.{u} ℕ),
        Y.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 Y.scheme))) (b n) =
          q.appTop ((Scheme.ΓSpecIso A).inv (π ^ n.toAdd.down))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Y.scheme),
        ∃ c : TraitUniformizerLogChart Y.scheme Y.logStructure A q π b,
          Nonempty ((Scheme.pointSmallEtale z).fiber.obj c.V)) := by
  sorry

end AlgebraicGeometry
