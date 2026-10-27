module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.AlgebraicGeometry.SectionComponentPullback
import WeilConjectures.AlgebraicGeometry.SmoothSectionComponentOpen
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.Topology.Compactness.Compact

/-!
# Affine product charts of the neutral part of a Néron lft-model

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 10.1, paragraph after Definition 1,
printed p. 290, and 6.4; the product map is 5.1 Lemma 4.
(blueprint: lem-sfb-neron-lft-neutral-affine-product-chart)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Restrict the multiplication of an S-group to the square of an open subscheme.
The tensor product in `Over S` is the fibre product over S, so the source is U ×_S U.
Source: BLR, Néron Models, 5.1 Lemma 4
(blueprint: lem-sfb-neron-lft-neutral-affine-product-chart). -/
noncomputable def groupOpenProductMap {S : Scheme.{u}} (G : Grp (Over S))
    (U : G.X.left.Opens) :
    (Over.mk (U.ι ≫ G.X.hom) ⊗ Over.mk (U.ι ≫ G.X.hom)).left ⟶ G.X.left :=
  (((Over.homMk U.ι : Over.mk (U.ι ≫ G.X.hom) ⟶ G.X) ⊗ₘ
    (Over.homMk U.ι : Over.mk (U.ι ≫ G.X.hom) ⟶ G.X)) ≫ μ[G.X]).left

/-- The geometric neutral locus of a Néron lft-model is an open subgroup and locally
admits an affine open whose square surjects under multiplication.
Source: BLR, Néron Models, 10.1 paragraph after Definition 1, p. 290; 6.4; 5.1 Lemma 4.
(blueprint: lem-sfb-neron-lft-neutral-affine-product-chart).

The displayed section-component locus is exactly the union of the geometric identity
components: `section_component_preimage_of_isPullback` identifies its inverse image in
every geometric fibre with the component of the induced identity section. An open subgroup
with this image carries precisely the open subscheme structure on that locus.

Proof:
1. Section components commute with base change (lem-sbc-section-component-cartesian).
Apply lem-sfb-locally-algebraic-group-identity-component to the smooth geometric fibres.
Their identity components are geometrically irreducible and quasi-compact. Surjectivity
under residue-field extension and continuity give quasi-compact ordinary components.
2. Around a point of the locus choose a finite union W of affine opens containing both
its fibre component and the entire identity section. The base is affine, hence the section
image is quasi-compact. Separatedness makes W quasi-separated and its finite affine cover
makes W quasi-compact over the base. It is smooth by open-immersion smooth composition.
Apply lem-sbc-smooth-section-component-open to W and its section. Its neutral locus gives
an open neighbourhood contained in the required locus. Thus that locus is open.
3. On geometric fibres the locus is a subgroup. Lift points to algebraically closed
residue fields to see multiplication and inverse preserve it. Factor those operations
and the identity through the open subscheme. Uniqueness of open factorization gives all
group identities and its inclusion is a group homomorphism.
4. For s choose an affine neighbourhood A of the identity in this open subgroup.
Smoothness implies flatness and local finite presentation (sbc-lem-smooth-criterion),
so its image is open (lem-weil-pbc-flat-lfp-open). Choose a principal affine base open
B containing s inside that image. U = A ×_S B is affine by the affine fibre-product
lemma and has nonempty fibres. After algebraic closure its fibres are nonempty opens
of the geometrically irreducible identity components, hence dense.
5. For any geometric point g of the neutral subgroup, the opens U and g U⁻¹ intersect
in that irreducible geometric fibre. Over the residue field of a point of intersection,
write g = uv with u,v in U. This lifts every underlying point through U ×_B U, proving
surjectivity of the canonical multiplication restriction. No bound on components is used. -/
theorem neronLft_neutralAffineProductChart
    (D K : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] [Field K] [Algebra D K] [IsFractionRing D K]
    (_hDim : ringKrullDim D = 1)
    (V : Grp (Over (Spec (.of K)))) [IsCommMonObj V.X]
    [Smooth V.X.hom] [IsSeparated V.X.hom]
    [LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]
    (N : Grp (Over (Spec (.of D)))) [IsCommMonObj N.X]
    [Smooth N.X.hom] [IsSeparated N.X.hom]
    (α : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D K)))).mapGrp.obj N ≅ V)
    (_hNeron : ∀ (Y : Over (Spec (.of D))) [Smooth Y.hom],
      Function.Bijective (fun h : Y ⟶ N.X ↦
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D K)))).map h ≫ α.hom.hom.hom)) :
    ∃ C : N.X.left.Opens,
      (C : Set N.X.left) =
        {x | x ∈ connectedComponentIn (N.X.hom ⁻¹' {N.X.hom x})
          (η[N.X].left (N.X.hom x))} ∧
      ∃ (H : Grp (Over (Spec (.of D)))) (j : H ⟶ N),
        IsOpenImmersion j.hom.hom.left ∧ Set.range j.hom.hom.left = (C : Set N.X.left) ∧
        ∀ s : Spec (.of D), ∃ B : (Spec (.of D)).Opens,
          s ∈ B ∧ IsAffine B.toScheme ∧
          ∃ U : ((Over.pullback B.ι).mapGrp.obj H).X.left.Opens,
            IsAffine U.toScheme ∧
            Surjective (groupOpenProductMap ((Over.pullback B.ι).mapGrp.obj H) U) := by
  sorry

end AlgebraicGeometry
