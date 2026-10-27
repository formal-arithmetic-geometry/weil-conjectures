module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.RingTheory.Depth

import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.AlgebraicGeometry.GenericFibreAffineRingModels
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
import WeilConjectures.RingTheory.FlatLocalDepthFormula

/-! # Depth and generic restriction for line bundles on flat curve families

Source: Stacks Project, algebra.tex, Tag 0337 (`lemma-apply-grothendieck`) and
Tag 00LL (`lemma-ideal-nonzerodivisor`); schemes.tex, Tag 0HA1
(`lemma-local-ring-fibre`); morphisms.tex, Tag 01T6 (`lemma-finite-type-noetherian`).
The assembly is the original lattice proof, steps 1--2
(blueprint: lem-sfb-flat-curve-line-depth).

The residue field is the canonical `IsLocalRing.ResidueField R`. The restriction map
is the adjunction unit `pullbackΓ` along the generic-fibre projection. Its target
is written as the pullback of the tensor power, canonically identified with the
tensor power of the pulled-back line. `tensorPow 0` is the structure module.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- A flat finite-type family with reduced pure one-dimensional special fibre is
Noetherian. All nonnegative tensor powers of a line have injective uniformizer
multiplication on stalks and injective restriction to the generic fibre. At each
closed special-fibre point, the local ring and the tensor-power stalk have depth
at least two. The existential finiteness witness only supplies the input required
by `IsLocalRing.depth`; it is a conclusion, not an additional hypothesis.

Source: Stacks Project, Tags 0337, 00LL, 0HA1 and 01T6; original lattice proof
steps 1--2 (blueprint: lem-sfb-flat-curve-line-depth).

Proof:
1. The DVR is Noetherian because all ideals are principal. Finite type over its
   Noetherian spectrum makes X Noetherian, with a finite affine Noetherian cover.
   Affine stalks are localizations and hence Noetherian.
2. A local generator of M gives one for every tensor power, with 1 in degree zero.
   Flatness makes multiplication by the nonzero uniformizer injective on local
   rings over the closed point, using flat-module torsion-freeness. At points over
   the generic point the uniformizer is a unit. Thus it acts injectively on every
   tensor-power stalk. A DVR has only its generic and closed points, by the
   unit-times-uniformizer-power description of its nonzero elements.
3. On an affine trivializing chart, generic restriction is localization at the
   uniformizer, by generic_fibre_affine_ring_models. Step 2 makes this element
   a nonzerodivisor on sections (test germs), so localization is injective.
   The sheaf axiom glues this injectivity globally. Pullback of the generator
   identifies the restricted tensor power with the tensor power of the restriction.
4. At a closed special-fibre point, the fibre-stalk quotient identifies its local
   ring B with A/pi A. It is Noetherian and reduced. Finite type over the residue
   field, pure dimension one, the equidimensional-open local-dimension lemma, and
   the closed-point dimension theorem give dim B = 1, so its maximal ideal is nonzero.
5. This maximal ideal is not associated: if ann(b) were maximal, a unit b would
   force that ideal to be zero; a nonunit b belongs to it and has b^2 = 0, hence
   b = 0 by reducedness, whose annihilator is the whole ring. The nonzerodivisor
   lemma now gives a regular element in the maximal ideal, hence depth B >= 1.
6. The DVR has depth at least one, witnessed by its uniformizer. Apply the flat
   local depth formula to R -> A, with closed fibre B, obtaining depth A >= 2.
   A free rank-one identification of the line stalk with A preserves regular
   sequences, their quotients and nonvanishing, hence their depth suprema. This
   also supplies its finite-module witness. All steps include tensor power zero.
-/
theorem flat_curve_line_depth (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (π : R) (hπ : Irreducible π)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) [Flat f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [IsReduced (pullback f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))]
    (hdim : (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue R)))).IsPureDimension 1)
    (M : X.Modules) [M.IsInvertible] :
    IsNoetherian X ∧ ∀ m : ℕ,
      (∀ x : X, Function.Injective fun t : TopCat.Presheaf.stalk
          (C := Ab.{u}) (X := X) (M.tensorPow m).val.presheaf x ↦
        (X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (.of R)).inv π))) • t) ∧
      Function.Injective (pullbackΓ
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (M.tensorPow m)) ∧
      ∀ x : pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))),
        IsClosed ({x} : Set _) →
        (2 : ℕ∞) ≤ IsLocalRing.depth
          (R := X.presheaf.stalk
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) x))
          (X.presheaf.stalk
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) x)) ∧
        ∃ hf : Module.Finite
            (X.presheaf.stalk
              ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) x))
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X)
              (M.tensorPow m).val.presheaf
              ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) x)),
          (2 : ℕ∞) ≤ @IsLocalRing.depth
          (X.presheaf.stalk
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) x)) _ _
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X)
              (M.tensorPow m).val.presheaf
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) x))
          _ _ hf := by
  sorry
end AlgebraicGeometry
