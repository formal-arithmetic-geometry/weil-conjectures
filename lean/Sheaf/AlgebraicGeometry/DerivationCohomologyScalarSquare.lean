/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.ScalarAbelianExtFactorization
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.CategoryTheory.Sites.Spaces
import Sheaf.CategoryTheory.GlobalModuleAbelianCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Mathlib.RingTheory.Kaehler.TensorProduct
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Scalar extension and cohomology of the universal derivation

Source: Stacks Project, Cohomology of Schemes, Tag 02KH (the separated-case Cech proof),
Cohomology, Tag 01F1, Cohomology on Sites, Tag 03FD, and Algebra, Tag 00RV
(blueprint: lem-sfb-derivation-cohomology-scalar-square).

The cohomology objects are the recorded right derived functors on module sheaves,
restricted to the ground field. Their canonical scalar-sheaf Ext comparison transports
maps that are linear only over the field. The auxiliary maps below are composites
of these existing comparisons; none chooses a sheaf, a resolution, or a map.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
open Modules
noncomputable section
/-- The map induced by a ground-field-linear coefficient map, using the canonical
injective-resolution comparison with Ext in vector-space sheaves.
Source: Stacks Project, Tags 01DZ and 03FD
(blueprint: lem-sfb-derivation-cohomology-scalar-square). -/
def scalarDerivationCohomologyMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (d : scalarSheaf f (SheafOfModules.unit X.ringCatSheaf) ⟶
      scalarSheaf f f.relativeDifferentials) (q : ℕ)
    (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) q) :
    scalarCohomology f f.relativeDifferentials q := by
  letI : HasExt.{u + 1} (KSheaf X k) := HasExt.standard _
  exact (scalarCohomologyExtEquiv f f.relativeDifferentials q).symm
    ((scalarCohomologyExtEquiv f (SheafOfModules.unit X.ringCatSheaf) q x).comp
      (Abelian.Ext.mk₀ d) (add_zero q))

/-- The canonical comparison from module cohomology to underlying abelian cohomology,
factored through cohomology in sheaves of ground-field vector spaces.
Source: Stacks Project, Tags 01F1 and 03FD
(blueprint: lem-sfb-derivation-cohomology-scalar-square). -/
def scalarModuleAbelianComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (q : ℕ)
    (x : scalarCohomology f F q) : HOver f F q :=
  scalarAbelianExtComparison k X (scalarSheaf f F) q
    (scalarCohomologyExtEquiv f F q x)

/-- Canonical cohomology pullback for an O-linear coefficient map into direct image.
It uses exact abelian inverse image, its constant-integer comparison, and the adjoint
coefficient map. Source: Stacks Project, Tag 01F7
(blueprint: lem-sfb-derivation-cohomology-scalar-square). -/
def abelianCoefficientCohomologyMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (h : F ⟶ (pushforward g).obj G) (q : ℕ)
    (x : F.H q) : G.H q :=
  Sheaf.H.map (coeff g h) q
    (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q x)

/-- Scalar extension commutes with the cohomology of the universal derivation.
Source: Stacks Project, Tags 02KH, 01F1, 03FD, and 00RV
(blueprint: lem-sfb-derivation-cohomology-scalar-square).

Proof: Use the canonical module-to-abelian comparison, also after restriction to
constant-field coefficients. In degree one for the structure sheaf,
new-sc-scalar-abelian-ext-factorization identifies the scalar Ext composite with
the direct module-to-abelian comparison. Choose a finite affine cover of the scheme;
separatedness makes all its intersections affine, including the empty intersections.
The inverse-image cover after field extension has the same property. Relative
differentials and the structure sheaf are quasi-coherent. Affine vanishing gives
canonical additive Cech edge isomorphisms, natural for the derivation. Flat Cech
base change identifies each coefficient complex after tensoring with K. On a pure
tensor z tensor lambda the comparison has coordinates lambda times h(z). The Leibniz
rule and d(lambda)=0 show that this identification intertwines the derivations.
Exact field extension commutes with kernels, images, and quotients, hence with each
cohomology group of the possibly unbounded Cech complex. Assemble these comparisons
with the edge isomorphisms. Their site-change naturality gives the displayed
normalization on 1 tensor x, independently of the affine cover. Finally insert the
cochain derivation identity and the naturality of tensor-homology comparison to
obtain the square on pure tensors; these generate the entire tensor product. -/
theorem derivation_cohomology_scalar_square
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [IsProjective f] :
    ∃ (d : scalarSheaf f (SheafOfModules.unit X.ringCatSheaf) ⟶
        scalarSheaf f f.relativeDifferentials)
      (dK : scalarSheaf (baseChangeSnd (S := K) f)
          (SheafOfModules.unit (baseChangedScheme (S := K) f).ringCatSheaf) ⟶
        scalarSheaf (baseChangeSnd (S := K) f)
          (baseChangeSnd (S := K) f).relativeDifferentials)
      (h₁ : f.relativeDifferentials ⟶ (pushforward (baseChangeFst (S := K) f)).obj
        (baseChangeSnd (S := K) f).relativeDifferentials),
      (∀ (U : X.Opens) (a : Γ(X, U)),
        d.hom.app (op U) a = f.relativeDifferentialsDerivation.d (X := op U) a) ∧
      (∀ (U : (baseChangedScheme (S := K) f).Opens)
        (a : Γ(baseChangedScheme (S := K) f, U)),
        dK.hom.app (op U) a =
          (baseChangeSnd (S := K) f).relativeDifferentialsDerivation.d (X := op U) a) ∧
      (∀ (U : X.Opens) (a : Γ(X, U)),
        h₁.val.app (op U) (f.relativeDifferentialsDerivation.d (X := op U) a) =
          (baseChangeSnd (S := K) f).relativeDifferentialsDerivation.d
            (X := op (baseChangeFst (S := K) f ⁻¹ᵁ U))
            ((baseChangeFst (S := K) f).app U a)) ∧
      ∀ q : ℕ,
        (Function.Bijective
            (scalarModuleAbelianComparison f (SheafOfModules.unit X.ringCatSheaf) q) ∧
          ∀ (r : k) (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) q),
            scalarModuleAbelianComparison f (SheafOfModules.unit X.ringCatSheaf) q (r • x) =
              r • scalarModuleAbelianComparison f (SheafOfModules.unit X.ringCatSheaf) q x) ∧
        (Function.Bijective (scalarModuleAbelianComparison f f.relativeDifferentials q) ∧
          ∀ (r : k) (x : scalarCohomology f f.relativeDifferentials q),
            scalarModuleAbelianComparison f f.relativeDifferentials q (r • x) =
              r • scalarModuleAbelianComparison f f.relativeDifferentials q x) ∧
        (Function.Bijective (scalarModuleAbelianComparison (baseChangeSnd (S := K) f)
            (SheafOfModules.unit (baseChangedScheme (S := K) f).ringCatSheaf) q) ∧
          ∀ (r : K) (x : scalarCohomology (baseChangeSnd (S := K) f)
            (SheafOfModules.unit (baseChangedScheme (S := K) f).ringCatSheaf) q),
            scalarModuleAbelianComparison (baseChangeSnd (S := K) f)
                (SheafOfModules.unit (baseChangedScheme (S := K) f).ringCatSheaf) q (r • x) =
              r • scalarModuleAbelianComparison (baseChangeSnd (S := K) f)
                (SheafOfModules.unit (baseChangedScheme (S := K) f).ringCatSheaf) q x) ∧
        (Function.Bijective (scalarModuleAbelianComparison (baseChangeSnd (S := K) f)
            (baseChangeSnd (S := K) f).relativeDifferentials q) ∧
          ∀ (r : K) (x : scalarCohomology (baseChangeSnd (S := K) f)
            (baseChangeSnd (S := K) f).relativeDifferentials q),
            scalarModuleAbelianComparison (baseChangeSnd (S := K) f)
                (baseChangeSnd (S := K) f).relativeDifferentials q (r • x) =
              r • scalarModuleAbelianComparison (baseChangeSnd (S := K) f)
                (baseChangeSnd (S := K) f).relativeDifferentials q x) ∧
        ∃ (β₀ : (K ⊗[k] scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) q) ≃ₗ[K]
            scalarCohomology (baseChangeSnd (S := K) f)
              (SheafOfModules.unit (baseChangedScheme (S := K) f).ringCatSheaf) q)
          (β₁ : (K ⊗[k] scalarCohomology f f.relativeDifferentials q) ≃ₗ[K]
            scalarCohomology (baseChangeSnd (S := K) f)
              (baseChangeSnd (S := K) f).relativeDifferentials q),
          (∀ x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) q,
            scalarModuleAbelianComparison (baseChangeSnd (S := K) f)
                (SheafOfModules.unit (baseChangedScheme (S := K) f).ringCatSheaf) q
                (β₀ ((1 : K) ⊗ₜ[k] x)) =
              abelianCoefficientCohomologyMap (baseChangeFst (S := K) f)
                (SheafOfModules.unitToPushforwardObjUnit
                  (baseChangeFst (S := K) f).toRingCatSheafHom) q
                (scalarModuleAbelianComparison f (SheafOfModules.unit X.ringCatSheaf) q x)) ∧
          (∀ x : scalarCohomology f f.relativeDifferentials q,
            scalarModuleAbelianComparison (baseChangeSnd (S := K) f)
                (baseChangeSnd (S := K) f).relativeDifferentials q (β₁ ((1 : K) ⊗ₜ[k] x)) =
              abelianCoefficientCohomologyMap (baseChangeFst (S := K) f) h₁ q
                (scalarModuleAbelianComparison f f.relativeDifferentials q x)) ∧
          ∀ (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) q) (aK : K),
            β₁ (aK ⊗ₜ[k] scalarDerivationCohomologyMap f d q x) =
              scalarDerivationCohomologyMap (baseChangeSnd (S := K) f) dK q
                (β₀ (aK ⊗ₜ[k] x)) := by
  sorry

end
end AlgebraicGeometry.Scheme
