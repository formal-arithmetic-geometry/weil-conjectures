/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Modules.LocalSplittingFiniteFree
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.AffineTraceTower
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.FiniteDirectImageComposition
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.NoetherianAffineLineUnit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Splittings of vector-bundle extensions and ordinary etale cohomology

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI, Proposition 1.5,
printed pages 226--227 (blueprint: lem-per-vector-extension-splitting-cohomology).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The scheme of splittings, its affine charts and translation maps, and ordinary
etale cohomology invariance. The universal property is written using the actual
universal section and the section-normalized composition comparison. In the last
clause the target uses inverse image; the canonical roots-of-unity comparisons of
`lem-asd-etale-finite-twist-pullback` identify it with the Tate sheaf on `S`.

Source: Illusie--Laszlo--Orgogozo, Expose XVI, Proposition 1.5, printed page 227
(blueprint: lem-per-vector-extension-splitting-cohomology).

Proof plan:
1. On rank strata use `lem-sc-local-splitting-finite-free`, then trivialize the two
   outer bundles on affine opens. Quasi-compactness gives a finite subcover.
   Tensor pullback preserves the split identities for every test morphism.
2. Over a chart the sections are matrices `(T,1)`. By
   `lem-per-affine-space-global-functions`, matrices are exactly morphisms into
   affine space, naturally for arbitrary test schemes. The coordinate matrix is
   the universal section.
3. Changing frames and local splittings gives invertible affine transformations
   `T ↦ A T B + C`. Uniqueness of coordinates proves the cocycle identities.
   Glue the schemes and projections using `lem-weil-pbc-glue-schemes` and
   `lem-weil-pbc-scheme-morphism-gluing`.
4. Glue the local universal sections by the sheaf axiom. A section over any test
   scheme gives unique compatible chart maps, hence a unique global map. The
   difference of two sections factors uniquely through the injection in split
   coordinates; these factors glue by uniqueness.
5. The affine charts and their coordinate towers are Noetherian by
   `def-amb-affine-trace-tower` and `pqf-def-locnoeth`. Their finite cover makes
   the glued scheme Noetherian, including zero-dimensional charts and empty bases.
6. Restriction to an etale slice preserves injective module sheaves: it is right
   adjoint to exact extension by zero (`lem-pur-site-restriction-module-adjunction-exact`).
   The slice equivalence (`lem-weil-pbc-etale-site-localization-open`) and the
   sectionwise direct-image formula identify restricted derived direct images
   and units with those of the base change.
7. Induct on chart dimension using `lem-per-noetherian-affine-line-unit` and the
   coordinate tower. The composition comparison of
   `lem-weil-derived-direct-image-composition` identifies the composite unit;
   its transpose is the identity by the triangle identities.
8. Detect the constant unit on charts using geometric-stalk conservativity and
   `lem-weil-pbc-unbounded-derived-iso-cohomology`. Tate sheaves are etale locally
   free lines by `lem-asd-etale-finite-twist-pullback`, so the same localization
   argument makes the twisted units invertible for every signed twist.
9. Resolve the inverse-image Tate sheaf by injective module sheaves. Exact inverse
   image makes direct image preserve injectives. The unit identifies its direct
   image resolution with a resolution on the base. Underlying abelian acyclicity
   (`det-pbc-conventions-module-cohomology`) and Leray acyclicity compute both
   cohomologies by the identical global-section complex.
10. Compare with `def-weil-pbc-cohomology-pullback`: two maps to an injective
    abelian resolution agree in the derived category and hence are homotopic by
    `lem-weil-pbc-kinjective-hom-derived`. Naturality of the unit and the triangle
    identity identify the resulting isomorphism with the canonical pullback.
-/
theorem vectorExtensionSplittingCohomology (X : Scheme.{u}) [IsNoetherian X]
    (ell n : ℕ) (hell : ell.Prime) (hn : 0 < n) (hX : IsUnit (ell : Γ(X, ⊤)))
    (T : ShortComplex X.Modules) (hT : T.ShortExact)
    [T.X₁.IsFiniteLocallyFree] [T.X₂.IsFiniteLocallyFree] [T.X₃.IsFiniteLocallyFree] :
    ∃ (S : Scheme.{u}) (rho : S ⟶ X)
      (s : (Modules.tensorPullback rho).obj T.X₃ ⟶ (Modules.tensorPullback rho).obj T.X₂),
      s ≫ (Modules.tensorPullback rho).map T.g = 𝟙 _ ∧
      (∃ r : (Modules.tensorPullback rho).obj T.X₂ ⟶ (Modules.tensorPullback rho).obj T.X₁,
        (Modules.tensorPullback rho).map T.f ≫ r = 𝟙 _ ∧
        r ≫ (Modules.tensorPullback rho).map T.f +
          (Modules.tensorPullback rho).map T.g ≫ s = 𝟙 _) ∧
      (∀ (Y : Scheme.{u}) (f : Y ⟶ X)
        (t : (Modules.tensorPullback f).obj T.X₃ ⟶ (Modules.tensorPullback f).obj T.X₂),
        t ≫ (Modules.tensorPullback f).map T.g = 𝟙 _ →
        ∃! h : {h : Y ⟶ S // h ≫ rho = f},
          eqToHom (congrArg (fun g => (Modules.tensorPullback g).obj T.X₃) h.property.symm) ≫
            (Modules.tensorPullbackSectionComp h.val rho).hom.app T.X₃ ≫
            (Modules.tensorPullback h.val).map s ≫
            (Modules.tensorPullbackSectionComp h.val rho).inv.app T.X₂ ≫
            eqToHom (congrArg (fun g => (Modules.tensorPullback g).obj T.X₂) h.property) = t) ∧
      (∃ (I : Type u) (U : I → X.Opens) (a b : I → ℕ), (⨆ i, U i) = ⊤ ∧
        ∀ i, (T.X₁.restrict (U i).ι).IsFiniteLocallyFreeOfRank (a i) ∧
          (T.X₃.restrict (U i).ι).IsFiniteLocallyFreeOfRank (b i) ∧
          ∃ e : pullback rho (U i).ι ≅ AffineSpace (ULift.{u} (Fin (a i * b i))) (U i),
            e.hom ≫ (AffineSpace (ULift.{u} (Fin (a i * b i))) (U i) ↘ (U i).toScheme) =
              pullback.snd rho (U i).ι) ∧
      (∀ (Y : Scheme.{u}) (f : Y ⟶ X)
        (t t' : (Modules.tensorPullback f).obj T.X₃ ⟶ (Modules.tensorPullback f).obj T.X₂),
        t ≫ (Modules.tensorPullback f).map T.g = 𝟙 _ →
        t' ≫ (Modules.tensorPullback f).map T.g = 𝟙 _ →
        ∃! v : (Modules.tensorPullback f).obj T.X₃ ⟶ (Modules.tensorPullback f).obj T.X₁,
          v ≫ (Modules.tensorPullback f).map T.f = t - t') ∧
      IsNoetherian S ∧
      IsIso ((Etale.mapDerivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))) rho).unit.app
          (Etale.constantComplex (ULift.{u + 1} (ZMod (ell ^ n))) X)) ∧
      (∀ (t : ℤ) (q : ℕ), Function.Bijective
        (Etale.cohomologyMap rho
          ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n))))
              AddCommGrpCat.{u + 1})).obj
            (finiteEtaleTateSheaf (ULift.{u + 1} (ZMod (ell ^ n))) (ell ^ n) X
              (congrArg (ULift.up : ZMod (ell ^ n) → ULift.{u + 1} (ZMod (ell ^ n)))
                (ZMod.natCast_self (ell ^ n))) t)) q)) := by
  sorry

end AlgebraicGeometry.Scheme
