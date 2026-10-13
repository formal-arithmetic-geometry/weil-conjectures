/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
import Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit
import Mathlib.RingTheory.LocalRing.Module
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial

/-! # Joint degree-one comparison for a fixed minimal source model

Source: Stacks Project, Tag 0BF2, the displayed chain maps and their residue comparison.
(blueprint: lem-sc-picard-h1-fixed-model-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- On an affine with trivial target bundles, construct the joint degree-one map
out of a supplied minimal source complex and identify its residue map geometrically.
Source: Stacks Project, Tag 0BF2, displayed chain maps; Tags 08CR and 0B91.
(blueprint: lem-sc-picard-h1-fixed-model-comparison)

Proof: Each target bundle is trivial on the entire supplied affine U, so its direct
image is the direct image of the structure module. The structure adjunction unit
identifies its H-zero with O_U. Perfect direct-image base change makes the target
complex perfect and universally connective. On the affine, choose a bounded finite
projective representative. Starting at its lowest negative degree, residue
connectiveness makes the outgoing map injective on every residue field. Locally
finite projective terms are finite free, so the local-ring residue split-injection
criterion gives a locally free cokernel. This finitely presented cokernel is finite
projective on the affine, so the injection splits globally. Cancel this pair and
repeat until no negative terms remain. Its degree-zero cohomology after every base
change is the structure
module, by hOi and the target trivialization. Use
exists_flat_derived_structure_unit for the derived unit and its fibre H-zero
comparison, and represent that map by a chain map on the affine. At every residue
field its degree-zero generator is nonzero, so this cycle is unimodular in the
connective projective degree-zero term. Split off that unit summand. The remaining
degree-zero differential is split injective: it is injective on every residue fibre,
so the same local-ring criterion gives a finitely presented locally free cokernel,
which is finite projective on the affine. Split and cancel this contractible pair.
This gives a connective finite projective model with only the unit in degree zero
and zero outgoing degree-zero differential. Its degree-one projective term is a
retract of a finite free module. Represent each canonical derived pullback arrow by a chain map
using the affine perfect-map theorem. Compose its degree-one component with that
retract inclusion. Choose the sum of the finitely many free target ranks as q and
identify their finite product with A^q. Their joint map b annihilates the source
outgoing differential by the chain equations and the zero target differentials.
The supplied source term-rank isomorphisms imply that every source differential
vanishes over the residue field: its term dimensions equal its Betti dimensions.
Consequently its residue degree-one term is its H-one. Trivialize the source fibre
using hLs and the field rank-one lemma; the structure adjunction unit excludes the
empty fibre. This identifies the source residue term with structure-sheaf H-one,
giving alpha. On each target, project from the free ambient term to the projective
term. Over the residue field choose a linear retraction of its degree-one term onto
the kernel of the outgoing differential; this kernel is H-one because the incoming
differential is zero. The source minimality makes the chain-map image lie in that
kernel, so this retraction changes none of the image vectors. Compare the
pulled-back source trivialization with the target trivialization; they differ by a
nonzero residue scalar. Adjust the target cohomology identification by this scalar.
The affine higher-direct-image comparison and naturality of canonical derived base
change then identify this map with the structure-sheaf cohomology pullback of alpha.
The immersion identifies kappa(w) with kappa(s); affine evaluation identifies kappa(p)
with kappa(w). Taking the product gives beta and the asserted square. When n is zero
use q zero and the unique map. When m is zero the source H-one is zero by minimality.
Neither a target trivialization outside U nor an H-one injectivity assumption is used.
-/
theorem picard_h1_fixed_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
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
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) j w)))))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K)) :
    ∃ (q : ℕ) (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U))),
      (∀ a : Γ(W, U),
        b (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a))) = 0) ∧
          let p := RingHom.ker (W.evaluation U w hwU).hom
          letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
            ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
                Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
              (β : (p.ResidueField ⊗[Γ(W, U)] (Fin q → Γ(W, U))) →+
                (∀ i, Sheaf.H
                  (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)),
              ∀ z, β ((b.baseChange p.ResidueField) z) = fun i ↦
                structureSheafCohomologyPullback
                  (((Over.pullback (S.fromSpecResidueField s)).map
                    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                      (ui i) (hui i))).left) 1 (α z) := by sorry

end AlgebraicGeometry.Scheme
