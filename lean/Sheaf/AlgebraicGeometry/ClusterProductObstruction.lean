module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import Mathlib.RingTheory.Artinian.Module
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-! # A cohomological subcluster obstruction to quadratic restriction

Source: Franciosi--Tenni, The canonical ring of a 3-connected curve (2014),
Section 2, Lemma 2.12, printed pp. 42--43, reduced smooth-support specialization
(blueprint: lem-sfb-cluster-product-obstruction).

The target of quadratic restriction is the actual restricted tensor-square line.
Scalar restriction gives cohomology its specified k-vector-space structure.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections with scalars restricted along the specified k-structure.
Source: Franciosi--Tenni, Lemma 2.12, H^0(C,L)
(blueprint: lem-sfb-cluster-product-obstruction). -/
noncomputable def clusterSections {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (L : C.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)).obj
    (L.val.obj (op ⊤))

/-- Dimension over k of the recorded module-sheaf cohomology, by scalar restriction.
Source: Franciosi--Tenni, Lemma 2.12, notation h^q(C,F)
(blueprint: lem-sfb-cluster-product-obstruction). -/
noncomputable def clusterCohomologyDimension {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (F : C.Modules) (q : ℕ) : ℕ :=
  Module.finrank k
    ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)).obj
      ((RingedSpace.moduleCohomology C.toRingedSpace q).obj F))

/-- The actual quadratic restriction: tensor over k, tensor sections, and restrict to S.
The first map imposes the additional Gamma(C,O_C)-balancing relations; it sends
pure tensors to the same pure tensors. The section-normalized pullback unit sends
m to 1 tensor m, so a tensor b is sent to (ab)|S without a trivialization of the line.
Source: Franciosi--Tenni, Lemma 2.12 and Remark 2.11
(blueprint: lem-sfb-cluster-product-obstruction). -/
noncomputable def clusterQuadraticRestriction {k : Type u} [Field k]
    {C S : Scheme.{u}} (f : C ⟶ Spec (.of k)) (i : S ⟶ C) (L : C.Modules) :
    TensorProduct k (clusterSections f L) (clusterSections f L) →
      Γ((tensorPullback i).obj (L ⊗ L), ⊤) :=
  letI : Algebra k Γ(C, ⊤) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toAlgebra
  letI : Module Γ(C, ⊤) (clusterSections f L) :=
    inferInstanceAs (Module Γ(C, ⊤) Γ(L, ⊤))
  letI : IsScalarTower k Γ(C, ⊤) (clusterSections f L) :=
    IsScalarTower.of_compHom k Γ(C, ⊤) Γ(L, ⊤)
  fun z ↦ ((tensorPullbackSectionAdjunction i).unit.app (L ⊗ L)).app ⊤
    (tensorSectionsMap L L ⊤
      (TensorProduct.mapOfCompatibleSMul Γ(C, ⊤) k Γ(C, ⊤)
        (clusterSections f L) (clusterSections f L) z))

/-- Failure of quadratic restriction yields a nonempty cohomological subcluster obstruction.
Source: Franciosi--Tenni (2014), Lemma 2.12, printed pp. 42--43,
with the reduced smooth-support specialization of the DAG
(blueprint: lem-sfb-cluster-product-obstruction).

Proof plan (the DAG's diagonal-pairing proof):
1. Projectivity implies properness and finite type (lem-kun-projective-implies-proper,
   def-weil-proper-morphism). Finite type over k makes C Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Invertibility makes L coherent by
   pqf-lem-coherent-ft-locnoeth; lem-pc-coherent-hi makes its cohomology finite-dimensional.
2. The finite reduced algebra of S is Artinian (lem-weil-pbc-finite-dim-algebra-artinian).
   Decompose it into residue fields by lem-sfb-reduced-artinian-residue-product and
   lem-weil-pbc-spec-finite-product-fields; each field is k by
   lem-weil-pbc-closed-point-residue-field-base. Choose frames of L on these points.
   The section tensor product then has coordinates a(x)b(x).
3. By lem-sfb-proper-subspace-separating-functional choose a nonzero functional
   lambda = sum c_x z_x annihilating all products. Its nonempty support T is an open
   and closed subscheme of S. The image W of H^0(C,L) in k^T is isotropic for
   B(z,w) = sum c_x z_x w_x.
4. Every c_x on T is nonzero, so this diagonal bilinear form is nondegenerate.
   By lem-sfb-nondegenerate-orthogonal-dimension, dim W-perp = |T| - dim W.
   Since W is contained in W-perp, rank-nullity
   (lem-weil-pbc-idempotent-charpoly-rank-nullity) gives 2 dim W <= |T|.
   This argument is valid in characteristic two.
5. Tensor the ideal sequence of T by the invertible L (lem-sc-ext-tensor-exact),
   obtaining 0 -> I_T tensor L -> L -> i_*(L|T) -> 0. Its quotient description
   is checked on trivializing opens. H^1(T,L|T) vanishes by
   lem-sc-noetherian-cohomology-above-dimension. Transfer this to C by
   lem-sc-zariski-module-abelian-cohomology-agree and
   lem-sc-cohomology-closed-immersion-pushforward.
6. Use lem-weil-pbc-scheme-modules-enough-injectives,
   lem-sc-global-sections-left-exact and lem-weil-pbc-derived-functor-long-exact.
   For a=h^0(C,L), b=h^1(C,L), n=|T|, r=dim W the resulting exact sequence gives
   h^0(C,I_T tensor L)=a-r and h^1(C,I_T tensor L)=n-r+b by rank-nullity.
   Their sum is a+b+n-2r >= a+b, as required.
-/
theorem exists_subcluster_cohomology_obstruction
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsHProjective f]
    [ConnectedSpace C] [IsReduced C]
    (hpure : ∀ Z : Set C, Z ∈ irreducibleComponents C → topologicalKrullDim Z = 1)
    (hnodal : ∀ x : C, x ∉ f.smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
        (C.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})))
    (L : C.Modules) [L.IsInvertible]
    (heffective : ∃ s : Γ(L, ⊤), ∀ x : C,
      x ∈ genericPoints C → L.presheaf.germ ⊤ x trivial s ≠ 0)
    (S : Scheme.{u}) (i : S ⟶ C) [IsClosedImmersion i]
    [IsReduced S] [IsFinite (i ≫ f)]
    (hsmooth : ∀ x : S, i x ∈ f.smoothLocus)
    (hquadratic : ¬ Function.Surjective (clusterQuadraticRestriction f i L)) :
    ∃ (T : Scheme.{u}) (j : T ⟶ S), IsClosedImmersion j ∧ Nonempty T ∧
      clusterCohomologyDimension f ((j ≫ i).ker.toModules ⊗ L) 0 +
          clusterCohomologyDimension f ((j ≫ i).ker.toModules ⊗ L) 1 ≥
        clusterCohomologyDimension f L 0 + clusterCohomologyDimension f L 1 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
