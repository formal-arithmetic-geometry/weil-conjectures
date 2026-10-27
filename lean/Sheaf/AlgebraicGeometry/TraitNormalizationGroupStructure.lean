module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationSmoothPullback
import Sheaf.AlgebraicGeometry.ComponentDominantNormalizationLift
import Sheaf.RingTheory.DvrNormalGenericReducedSpecial

/-! # Group structures on a finite normalization over a trait

Source: Prasad--Yu, On quasi-reductive group schemes, Appendix by Brian Conrad,
Corollary A.4, proof, printed p.29; Stacks Tags 035Q, 047N and 047P
(blueprint: lem-sfb-trait-normalization-group-structure).

The four helpers only bundle the recorded reduction, componentwise normalization and
canonical maps in the over category. They construct no additional geometric objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.TraitNormalization

noncomputable section

/-- The canonical reduction, equipped with its composite structure map to the base.
Source: Prasad--Yu, Appendix A.4 proof, p.29; Stacks Tag 0356
(blueprint: lem-sfb-trait-normalization-group-structure). -/
def reduction {S : Scheme.{u}} (G : Over S) : Over S :=
  Over.mk (G.left.nilradical.subschemeι ≫ G.hom)

/-- The canonical inclusion of the reduction, as a morphism over the base.
Source: Prasad--Yu, Appendix A.4 proof, p.29; Stacks Tag 0356
(blueprint: lem-sfb-trait-normalization-group-structure). -/
def reductionι {S : Scheme.{u}} (G : Over S) : reduction G ⟶ G :=
  Over.homMk G.left.nilradical.subschemeι

/-- The recorded componentwise normalization of the reduction, over the same base.
Source: Prasad--Yu, Appendix A.4 proof, p.29; Stacks Tag 0CDV
(blueprint: lem-sfb-trait-normalization-group-structure). -/
def normalization {S : Scheme.{u}} (G : Over S) : Over S :=
  Over.mk ((reduction G).left.fromReducedNormalization ≫ (reduction G).hom)

/-- The canonical componentwise normalization map to the reduction, over the base.
Source: Prasad--Yu, Appendix A.4 proof, p.29; Stacks Tag 035Q
(blueprint: lem-sfb-trait-normalization-group-structure). -/
def normalizationπ {S : Scheme.{u}} (G : Over S) : normalization G ⟶ reduction G :=
  Over.homMk (reduction G).left.fromReducedNormalization

/-- The reduction has a unique subgroup structure, the normalization map is generically
an isomorphism, and the normalization has a unique compatible group structure.
Source: Prasad--Yu, Appendix Corollary A.4 proof, printed p.29
(blueprint: lem-sfb-trait-normalization-group-structure).

Proof:
1. A DVR is Noetherian. Finite-type schemes and their finite fibre powers are Noetherian
   (lem-weil-pbc-finite-type-over-noetherian, lem-sfb-finite-type-composition-base-change).
   Flatness of products follows from lem-weil-pbc-flat-morphism-base-change and
   lem-weil-pbc-flat-ring-map-comp. On affine charts, flatness
   (lem-weil-pbc-flat-morphism-affine-criterion) makes multiplication by a uniformizer
   injective. Thus restriction to the generic fibre is injective, so a reduced generic
   fibre implies reducedness, and generic fibres are schematically dense.
2. Geometric reducedness makes H_L squared reduced
   (lem-sfb-flat-geometrically-reduced-pullback); step 1 makes H squared reduced.
   Multiplication, inverse and identity factor through the reduction
   (lem-weil-pbc-reduced-source-factors-through-closed-subscheme). Its monicity proves
   every group diagram and uniqueness of the structure on H.
3. H_L is smooth (lem-sfb-geometrically-reduced-group-smooth), hence normal
   (lem-sfb-smooth-normal-ascent). Normalization commutes with its open inclusion
   (lem-pc-open-immersion-smooth-composition,
   lem-sfb-componentwise-normalization-smooth-pullback). The normalization of normal H_L
   is an isomorphism by lem-sfb-component-dominant-normalization-lift and
   lem-sfb-componentwise-normalization-generic-properties. Transport the generic group law.
4. The generic fibre of N squared is smooth, using
   lem-weil-pbc-smooth-ring-map-base-change-composition, and normal by normal ascent.
   Its special fibre is reduced by lem-sfb-flat-geometrically-reduced-pullback.
   Apply lem-sfb-dvr-normal-generic-reduced-special on affine charts: N squared is normal.
   N is normal by lem-sfb-componentwise-normalization-generic-properties.
5. Every component of a flat Noetherian trait scheme meets the generic fibre:
   lem-sc-flat-going-down, lem-weil-pbc-spec-irreducible-components-minimal-primes and
   lem-sc-components-open-injection. Generic multiplication is smooth (a projection
   conjugated by (x,y) to (xy,y)), hence flat by lem-pc-smooth-flat; generic inversion
   is an isomorphism. Thus both maps to H dominate components, also on the total spaces.
6. Apply lem-sfb-component-dominant-normalization-lift to lift multiplication and inverse
   uniquely to N. Their generic restrictions are exactly the transported operations.
7. The generic identity lifts over the DVR by finiteness, lem-weil-pbc-finite-proper and
   lemma-nagata-proper-separated-valuation-extension. A section is not assumed dominant.
8. Associativity, both unit identities and both inverse identities hold generically.
   By step 1 and lemma-nagata-ext-scheme-theoretically-dominant-separated they hold
   everywhere on the relevant flat powers. The same argument on N squared, N and S
   proves uniqueness. The normalization map is a homomorphism, and its generic
   isomorphism therefore identifies the generic group structures. -/
theorem existsUnique_group_structures
    (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (L : Type u) [Field L] [Algebra V L] [IsFractionRing V L]
    (G : Over (Spec (.of V))) [GrpObj G]
    [Flat G.hom] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Flat (reduction G).hom] [IsSeparated (reduction G).hom]
    [LocallyOfFiniteType (reduction G).hom] [QuasiCompact (reduction G).hom]
    [Flat (normalization G).hom] [IsSeparated (normalization G).hom]
    [LocallyOfFiniteType (normalization G).hom] [QuasiCompact (normalization G).hom]
    [IsFinite (normalizationπ G).left]
    [GeometricallyReduced (pullback.snd (reduction G).hom
      (Spec.map (CommRingCat.ofHom (algebraMap V L))))]
    [GeometricallyReduced (pullback.snd (normalization G).hom
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))))] :
    IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap V L)))).map
      (normalizationπ G)) ∧
    (∃! hH : GrpObj (reduction G),
      @IsMonHom _ _ _ _ _ hH.toMonObj inferInstance (reductionι G)) ∧
    (∀ hH : GrpObj (reduction G),
      @IsMonHom _ _ _ _ _ hH.toMonObj inferInstance (reductionι G) →
      ∃! hN : GrpObj (normalization G),
        @IsMonHom _ _ _ _ _ hN.toMonObj hH.toMonObj (normalizationπ G)) := by
  sorry

end

end AlgebraicGeometry.TraitNormalization
