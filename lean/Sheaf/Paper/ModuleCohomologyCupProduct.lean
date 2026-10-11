/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Sheaf.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Topology.Sheaves.CechComparison

/-! # Cup products computed by acyclic resolutions

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cohomology-cup-product).
The characterization uses resolutions with a sectionwise bilinear chain pairing.
It determines the derived cup product; Godement resolutions supply such pairings.
-/

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The class of a cocycle, using Mathlib's kernel description of the cycles.
Source: Stacks, section-cup-product (blueprint: def-sc-module-cohomology-cup-product). -/
def cupCycleClass {R : Type uM} [Ring R] (K : CochainComplex (ModuleCat.{uM} R) ℕ)
    (n : ℕ) (z : (K.sc n).moduleCatLeftHomologyData.K) : K.homology n :=
  (K.sc n).homologyπ ((K.sc n).moduleCatCyclesIso.inv z)

/-- A resolution that computes module cohomology, with a comparison to an injective
resolution over the original coefficient sheaf. The global comparison must induce
isomorphisms; this holds, in particular, for flasque resolutions.
Source: Stacks, Tags 01DZ and 0FKV (blueprint: def-sc-module-cohomology-cup-product). -/
structure CupAcyclicResolution {X : Scheme.{uM}} (F : X.Modules) where
  K : CochainComplex X.Modules ℕ
  augmentation : (CochainComplex.single₀ X.Modules).obj F ⟶ K
  quasiIso : QuasiIso augmentation
  I : InjectiveResolution F
  comparison : K ⟶ I.cocomplex
  over : augmentation ≫ comparison = I.ι
  computes : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ) |>.map comparison) n)

/-- The cohomology class represented by a global cocycle in an acyclic resolution.
Source: Stacks, Tags 01DZ and 0FKV (blueprint: def-sc-module-cohomology-cup-product). -/
def CupAcyclicResolution.class {X : Scheme.{uM}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ)
    (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K) :
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj F :=
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
    (HomologicalComplex.homologyMap
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map D.comparison) n
      (cupCycleClass _ n z))

/-- A sectionwise O-linear chain pairing of three nonnegative acyclic resolutions,
restricting in degree zero to the ordinary tensor of coefficient sections.
The sign in Leibniz is the total tensor sign. No compatibility of cup products on
cohomology is assumed in this data.
Source: Stacks, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cohomology-cup-product). -/
structure CupResolutionPairing {X : Scheme.{uM}} (F G : X.Modules) where
  left : CupAcyclicResolution F
  right : CupAcyclicResolution G
  target : CupAcyclicResolution (F ⊗ G)
  pair : ∀ (r s : ℕ) (V : X.Opens),
    Γ(left.K.X r, V) →ₗ[Γ(X, V)] Γ(right.K.X s, V) →ₗ[Γ(X, V)]
      Γ(target.K.X (r + s), V)
  restriction : ∀ (r s : ℕ) (V W : X.Opens) (h : W ≤ V)
    (a : Γ(left.K.X r, V)) (b : Γ(right.K.X s, V)),
    (target.K.X (r + s)).presheaf.map (homOfLE h).op (pair r s V a b) =
      pair r s W ((left.K.X r).presheaf.map (homOfLE h).op a)
        ((right.K.X s).presheaf.map (homOfLE h).op b)
  leibniz : ∀ (r s : ℕ) (V : X.Opens)
    (a : Γ(left.K.X r, V)) (b : Γ(right.K.X s, V)),
    (target.K.d (r + s) (r + s + 1)).val.app (op V) (pair r s V a b) =
      (eqToHom (congrArg (fun n ↦ target.K.X n)
          (by omega : r + 1 + s = r + s + 1))).val.app (op V)
        (pair (r + 1) s V ((left.K.d r (r + 1)).val.app (op V) a) b) +
      (-1 : ℤ) ^ r •
        (eqToHom (congrArg (fun n ↦ target.K.X n)
            (by omega : r + (s + 1) = r + s + 1))).val.app (op V)
          (pair r (s + 1) V a ((right.K.d s (s + 1)).val.app (op V) b))
  augmentation_pair : ∀ (V : X.Opens) (a : Γ(F, V)) (b : Γ(G, V)),
    pair 0 0 V ((left.augmentation.f 0).val.app (op V) a)
        ((right.augmentation.f 0).val.app (op V) b) =
      (target.augmentation.f 0).val.app (op V) (tmulSection a b)

/-- The sheaf cup product is the bilinear pairing computed by every acyclic resolution
pairing extending the tensor of sections. This is the usual derived cup product:
resolve by Godement complexes, apply the naive signed tensor pairing, and identify
cohomology through the resolution comparison. Conversely, for any such pairing the
map from the derived tensor of F and G to F tensor G is determined by its degree-zero
augmentation, so it gives the same product.
Source: Stacks, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cohomology-cup-product). -/
def IsModuleCupProduct {X : Scheme.{uM}} (F G : X.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G))) : Prop :=
  ∀ (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
    c.val = D.pair p q ⊤ a.val b.val →
      cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c

/-- The acyclic-resolution characterization defines a unique sheaf cup product.
Source: Stacks, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cohomology-cup-product).
Proof: choose Godement resolutions, which compute global cohomology and admit the
sectionwise signed pairing. Leibniz shows products of cycles are cycles and products
with boundaries are boundaries, giving a bilinear map on the quotient. Any other
acyclic resolution pairing yields a derived map F tensor-derived G to F tensor G.
Since the former lies in nonpositive degrees and the latter in degree zero, this map
is determined by H-zero; the augmentation fixes it to the ordinary tensor map.
Thus every pairing gives the usual cup product and the characterization is unique. -/
theorem exists_unique_moduleCupProduct {X : Scheme.{uM}} (F G : X.Modules) (p q : ℕ) :
    ∃! cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)),
      IsModuleCupProduct F G p q cup := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
