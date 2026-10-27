module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import Sheaf.RingTheory.ValuationRingNormal
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange

/-!
# Effective descent of smooth groups over fields and traits

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 6.5 Theorem 1, printed p.157,
group-scheme case (blueprint: lem-sfb-smooth-group-field-trait-descent).

The descent datum uses the existing transport-of-points interface. Its compatibility with
multiplication expresses that the overlap isomorphism is a group isomorphism. The effective
model is equipped with a group isomorphism from its base change, compatible with this datum.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Smooth separated groups of finite type descend along faithfully flat extensions of fields
or discrete valuation rings. No affineness or projectivity hypothesis is required.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 6.5 Theorem 1, printed p.157;
proof on printed pp.160--162 (blueprint: lem-sfb-smooth-group-field-trait-descent).

Proof plan:
1. The affine spectrum map is flat and surjective by
`lem-weil-pbc-flat-ring-map-iff-flat-affine` and
`lem-weil-pbc-faithfully-flat-surjective-spectrum`. The one-member affine target cover and
`pqf-lem-affine-local-target` show it is affine; `lem-weil-pbc-affine-morphism-permanence`
makes it quasi-compact, hence an fpqc cover (`def-weil-pbc-fpqc-covering`).
2. In the field case use `lem-sfb-finite-type-group-ample-line` and
`lem-sfb-field-ample-scheme-datum-effectivity`. In the DVR case first apply these to the
generic fibre, retaining finite type and separatedness by `lem-weil-pbc-lft-base-change`,
`lem-pc-quasi-compact-base-change` and `lem-weil-pbc-separated-base-change`.
3. Apply `lem-sfb-trait-generic-effective-dense-affine` to get a datum-invariant affine open
with an affine effective model. Then `lem-sfb-trait-horizontal-boundary-datum` gives the
horizontal Cartier boundary and a compatible datum on its associated invertible module.
4. A DVR is Noetherian, one-dimensional (`lem-sc-dvr-dimension-one`) and normal
(`lem-weil-pbc-valuation-ring-normal`). The open neutral subgroup from
`lem-sfb-smooth-group-relative-neutral-open` has geometric orbits equal to fibre components.
The dense open meets them all, so the action on that open is surjective. Apply
`lem-sfb-dedekind-action-boundary-ampleness` and `lem-sfb-polarized-affine-fpqc-effectivity`
to obtain an effective underlying scheme.
5. Descend multiplication, identity and inverse using `lem-galois-fpqc-morphisms-descend`;
its injectivity descends their identities. The resulting base-change isomorphism is a group
isomorphism realizing the original datum. Descend smoothness, separatedness, local finite
type and quasi-compactness using `lem-trf-smooth-fpqc-base-descent`,
`lem-weil-pbc-fpqc-descend-separated`, `lem-weil-pbc-fpqc-descend-locally-finite-type` and
`lem-weil-pbc-fpqc-descend-quasi-compact`. The last two express finite type.
-/
theorem exists_smooth_group_field_trait_descent
    (B C : Type u) [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    (φ : B →+* C) (hφ : φ.FaithfullyFlat)
    (hbase : (IsField B ∧ IsField C) ∨
      (IsDiscreteValuationRing B ∧ IsDiscreteValuationRing C))
    (G' : Grp (Over (Spec (.of C))))
    [Smooth G'.X.hom] [IsSeparated G'.X.hom]
    [LocallyOfFiniteType G'.X.hom] [QuasiCompact G'.X.hom]
    (D : Over.DescentDatum (Spec.map (CommRingCat.ofHom φ)) G'.X)
    (hmul : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of C))
      (h : f₁ ≫ Spec.map (CommRingCat.ofHom φ) =
        f₂ ≫ Spec.map (CommRingCat.ofHom φ)) (a b : Over.mk f₁ ⟶ G'.X),
      D.transport f₁ f₂ h (a * b) = D.transport f₁ f₂ h a * D.transport f₁ f₂ h b) :
    ∃ G : Grp (Over (Spec (.of B))),
      Smooth G.X.hom ∧ IsSeparated G.X.hom ∧
      LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom ∧
      ∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj G ≅ G',
        ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of C))
          (h : f₁ ≫ Spec.map (CommRingCat.ofHom φ) =
            f₂ ≫ Spec.map (CommRingCat.ofHom φ)) (a : Over.mk f₁ ⟶ G'.X),
          (D.transport f₁ f₂ h a).left ≫ e.inv.hom.hom.left ≫
              pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom φ)) =
            a.left ≫ e.inv.hom.hom.left ≫
              pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom φ)) := by
  sorry

end AlgebraicGeometry
