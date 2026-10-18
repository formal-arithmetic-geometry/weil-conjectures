/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.IndHeartFullFaithfulness
public import Sheaf.Paper.ModuleObjects
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.SheafTensor
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage
import Sheaf.Paper.IndConstructibleFilteredColimits

/-!
# A uniform bound for proper direct image on the ind-constructible heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound,
statement and proof (blueprint: sk-lem-proper-heart-bound).

## Main statements

- `properHeartBound`: the finite-extension coefficient case.
- `properHeartBound_padicAlgCl`: the condensed algebraic-closure coefficient case.

The helpers only expand the degree-zero derived direct image and the three conclusions.
IndCons is the recorded filtered-colimit closure of finite constant-model constructibles.
For an integer d, the fibre bound is expressed by testing all finite lower bounds of
`topologicalKrullDim`; this retains negative d and empty fibres, whose dimension is bottom.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The functor M ↦ H^q(Rp_*(M[0])) on internal modules over the pulled-back coefficient ring.
Source: blueprint sk-lem-proper-heart-bound, definition of R^q p_* in the standing conventions
(blueprint: sk-lem-proper-heart-bound). This is the full module-object derived direct image. -/
def properHeartHigherDirectImage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (q : ℤ) :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y) :=
  DerivedCategory.singleFunctor _ 0 ⋙ (CondensedRing.lowerStar Λ p).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ q

/-- The three conclusions of the proper heart bound: vanishing in degrees q > 2d+1,
ind-constructibility in every nonnegative degree, and preservation of arbitrary small sums
of ind-constructibles by each nonnegative higher direct image. Preservation means that the
image of every colimit cofan is a colimit; its legs are the images of the original injections.
By fullness, repleteness and ambient-sum closure of IndCons, this is exactly preservation
of sums in IndCons itself, including the empty sum.
Source: blueprint sk-lem-proper-heart-bound, displayed formulas and final assertion
(blueprint: sk-lem-proper-heart-bound). -/
def ProperHeartBoundAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (d : ℤ) : Prop :=
  (∀ M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) M →
    (∀ q : ℤ, 2 * d + 1 < q → IsZero ((properHeartHigherDirectImage Λ p q).obj M)) ∧
    (∀ q : ℤ, 0 ≤ q → ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible Λ Y) ((properHeartHigherDirectImage Λ p q).obj M))) ∧
  (∀ (q : ℤ), 0 ≤ q → ∀ (S : Type (u + 1))
    (M : S → CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)),
    (∀ s : S, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) (M s)) →
    ∀ c : Cofan M, IsColimit c →
      Nonempty (IsColimit ((properHeartHigherDirectImage Λ p q).mapCocone c)))

/-- For a proper morphism in the standing separated finite-type positive-characteristic
setting, higher direct image of ind-constructible E-modules vanishes above 2d+1, stays
ind-constructible in nonnegative degrees, and preserves arbitrary direct sums.
Source: blueprint main-20261015, sk-lem-proper-heart-bound, statement and proof
(blueprint: sk-lem-proper-heart-bound).

Proof for stage 3 (the seven DAG steps):
1. Properness gives finite type and separatedness, hence qcqs, using
   def-weil-proper-morphism, def-weil-finite-type-morphism, def-weil-closed-immersion,
   def-weil-quasi-separated-morphism and lem-weil-pbc-affine-scheme-qcqs.
   The field is Noetherian (def-weil-pbc-noetherian-ring); finite type over its spectrum
   makes X and Y locally Noetherian and quasi-compact by pqf-def-locnoeth and
   lem-weil-pbc-finite-type-over-noetherian, as det-ind-heart-full-faithfulness requires.
2. det-proper-heart-bound-rational gives the uniform constructible bound 2d+1, via
   integral lattices, the torsion bound 2d, the Milnor bound and rationalization.
3. A constructible C in degree zero is bounded constructible by sk-def-sfb-constructible.
   det-thm-sfb-proper-base-change-rational preserves that category under proper pushforward;
   thus every R^q p_* C is constructible.
4. def-weil-pbc-internal-abelian-sheaf-module-equivalence and sk-def-sfb-sheaf-tensor
   identify internal modules with sectionwise modules without changing underlying sheaves.
   lem-weil-pbc-equivalence-injective-resolutions transports injective resolutions;
   lem-weil-pbc-module-sheaves-colimits-forgetful gives exactness and small colimits.
   Restriction from p_*Λ_X to Λ_Y preserves both, as underlying abelian sheaves agree.
5. Use lem-sc-bounded-below-injective-resolution and
   lem-weil-pbc-dplus-injective-representative to compute the full module derived
   direct image on the transported injective resolution. sk-def-sfb-module-derived-pushpull
   and sk-def-sfb-module-pushforward-pullback identify the underlying direct-image complexes.
   Naturality identifies the continuity comparisons with the canonical module maps in
   det-proper-heart-continuity-direct-image.
6. Present M as a small filtered colimit of constructibles by clause (2) of
   det-ind-heart-full-faithfulness. Continuity identifies its R^q p_* with the colimit
   of their R^q p_*; step 3 gives membership in IndCons and step 2 gives vanishing.
7. det-ind-heart-filtered-colimits gives closure under arbitrary sums on X and Y.
   det-proper-heart-continuity-direct-image makes the image of a coproduct cofan a
   colimit. Fullness and repleteness from det-ind-heart-full-faithfulness give the
   coproduct universal property in IndCons, including the empty family. -/
theorem properHeartBound
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperHeartBoundAssertions (Profinite.continuousMapRingObj.{u} E) p d := by
  sorry

/-- The uniform proper heart bound for the condensed algebraic closure, whose sections
are continuous maps valued in some finite subextension, rather than all continuous maps
into the algebraic closure. Source: blueprint main-20261015, sk-lem-proper-heart-bound,
statement and proof (blueprint: sk-lem-proper-heart-bound).

Proof for stage 3: follow the same seven DAG steps as properHeartBound. Properness gives
qcqs and finite type over k gives Noetherian X and Y (the properness, finite-type,
closed-immersion, quasi-separated, affine-qcqs, Noetherian-ring, locally-Noetherian and
finite-type-over-Noetherian nodes). det-proper-heart-bound-rational gives the constructible
vanishing bound, and det-thm-sfb-proper-base-change-rational with sk-def-sfb-constructible
makes the constructible direct images constructible. The internal/sectionwise equivalence,
sk-def-sfb-sheaf-tensor, lem-weil-pbc-equivalence-injective-resolutions and
lem-weil-pbc-module-sheaves-colimits-forgetful transport cohomology and colimits.
lem-sc-bounded-below-injective-resolution and lem-weil-pbc-dplus-injective-representative
identify the two derived direct images naturally, using sk-def-sfb-module-derived-pushpull
and sk-def-sfb-module-pushforward-pullback. Apply det-proper-heart-continuity-direct-image
to the filtered constructible presentation from det-ind-heart-full-faithfulness.
Vanishing and IndCons membership follow term by term; det-ind-heart-filtered-colimits
and direct-sum continuity give preservation of every coproduct cofan, including the empty
one, in the full replete ind-constructible subcategories. -/
theorem properHeartBound_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperHeartBoundAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p d := by
  sorry

end AlgebraicGeometry.ProEtale
