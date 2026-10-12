/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.RingTheory.FiniteFreeMapResidueLocalization
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Local fibre-generator lifting after descent of the pullback bundles

Source: Stacks Project, Tag 0BF2, the perfect-complex argument through d = 0.
(blueprint: lem-sc-picard-h1-local-section-base-descent)
-/

@[expose] public section

set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Once the pullback bundles descend to an immersed base, joint H1 injectivity lifts
an original fibre generator to a section on an open neighbourhood in that base.
This assertion concerns sections only, and makes no assertion about Picard loci or
representation of intersections.

Source: Stacks Project, Tag 0BF2, proof after replacing the base by the intersection,
through the equality d = 0 and lifting the fibre generator.
(blueprint: lem-sc-picard-h1-local-section-base-descent)

Proof:
1. Base change the proper flat finitely presented families and the invertible module
   along k. Since k is an immersion and k(w) = s, the residue fields at w and s are
   canonically isomorphic. Thus the fibre-descent hypothesis and the joint H1 injection
   transport to w. The structure-pushforward hypotheses hold after this base change.
2. Each hLi exhibits the target bundle as the pullback of a finite locally free N.
   Faithfully flat descent applies: the universal structure-pushforward isomorphism
   makes every target family surjective, hence its flat structure map is faithfully
   flat. Consequently N is invertible. Shrink to a common affine neighbourhood of w
   on which these finitely many N are trivial. The same argument over the residue
   field makes the original fibre bundle trivial by hLs.
3. Apply perfect_derivedDirectImage_baseChange to the base-changed bundles. Invertibility
   supplies finite presentation and relative flatness. Their derived direct images
   are perfect, their formation commutes with residue-field base change, H0 has rank
   one, and negative fibre cohomology vanishes.
4. Apply exists_finiteFreeResidueModel to all these perfect complexes and shrink to a
   common affine neighbourhood. They have degree-zero term O, degree-j ranks equal
   to the fibre Betti numbers, and all residue differentials are zero. Represent the
   derived pullback maps by chain maps between these fixed bounded finite free models:
   on the affine base their terms are projective and their Hom complexes compute
   derived morphisms. The degree-zero residue maps are isomorphisms because pullback
   takes a fibre generator to a generator; shrink to invert these maps.
5. The joint degree-one residue map is injective by hH. If its source rank is positive,
   apply finiteFreeMap_residue_localization to the joint degree-one map, inverting
   a nonzero maximal minor to make that map injective (in fact split injective).
   If the rank is zero it is already injective; this also handles an empty family.
   Each target H0 is O. Its generator embeds into the degree-zero term O by a scalar
   which is nonzero modulo the marked prime, by H0 base change. Invert that scalar;
   the generator spans the whole term, so its degree-zero differential is zero.
   The chain-map identities then force the source degree-zero differential to be zero.
6. The generator of that source term is an H0 class, hence a global section of the
   base-changed L on this neighbourhood V. Its residue is the original trivializing
   fibre section, so its germs generate L at every point over the marked point of V.
   This is precisely membership in Modules.nonvanishingLocus. -/
theorem picard_h1_local_section_of_base_descent {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLi : ∀ i, ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        (Modules.tensorPullback (pullback.snd (fi i) k)).obj N))
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (hH : Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1 ↦ fun i ↦
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) 1 x)) :
    ∃ (V : W.Opens) (hwV : w ∈ V),
      ∃ σ : Γ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L, ⊤),
        ∀ x : (pullback f (V.ι ≫ k) : Scheme.{v}),
          (pullback.snd f (V.ι ≫ k)) x = (⟨w, hwV⟩ : V.toScheme) →
            x ∈ Modules.nonvanishingLocus
              ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L) σ := by sorry

end AlgebraicGeometry.Scheme
