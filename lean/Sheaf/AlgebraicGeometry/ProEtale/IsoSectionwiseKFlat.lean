/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.AlgebraicInverseImageKFlat
import Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints

/-! # K-flatness under sectionwise reindexing

Source: Stacks Project, Tag 06YN; the K-flatness part of
`lem-pod-sectionwise-flat-kflat`.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance 2000] SheafOfModules.hasSheafify_coefficientUniverse
attribute [local instance 2000] SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The explicit algebraic presentation of sectionwise inverse image.
Source: Stacks Project, Modules on Sites, Tag 03D2; Cohomology on Sites, Tag 0DEP.
The ring identification is induced by `c`, and the underlying module identification
is the identity. The scalar graph follows by cancelling `c` with its inverse. -/
private noncomputable def sectionwiseAlgebraicLift
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj RY ≅ RX) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u, u + 1, u + 1}
      (isoSectionwiseInverseImage g (Type (u + 1))) RY RX := by
  let U := CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1}
  let er := (sheafCompose (ProEt.topology X) U).mapIso c
  refine
    { ringUnderlying := er
      modules := isoSectionwiseModuleInverseImage.{u, u} g
        (RY := (sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)
        (RX := (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom
      moduleUnderlying := Iso.refl _
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (c.hom.hom.app V).hom (t.hom.app _ x).down =
      (c.hom.hom.app V).hom (a.hom.app _ x).down +
        (c.hom.hom.app V).hom (b.hom.app _ x).down
    simpa only [id, map_add] using congrArg (c.hom.hom.app V).hom (h _ x)
  · intro T a b t h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (c.hom.hom.app V).hom (t.hom.app _ x).down =
      (c.hom.hom.app V).hom (a.hom.app _ x).down *
        (c.hom.hom.app V).hom (b.hom.app _ x).down
    simpa only [id, map_mul] using congrArg (c.hom.hom.app V).hom (h _ x)
  · intro T a h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (c.hom.hom.app V).hom (a.hom.app _ x).down = 0
    simpa only [id, map_zero] using congrArg (c.hom.hom.app V).hom (h _ x)
  · intro T a h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (c.hom.hom.app V).hom (a.hom.app _ x).down = 1
    simpa only [id, map_one] using congrArg (c.hom.hom.app V).hom (h _ x)
  · intro M T a b t h V x
    exact h _ x
  · intro M T a h V x
    exact h _ x
  · intro M T a b t h V x
    change T.obj.obj ((proEtaleIsoPostcompose g).op.obj V) at x
    change (t.hom.app _ x).down =
      ((inv ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom).hom.app V).hom
          ((c.hom.hom.app V).hom (a.hom.app _ x).down) •
            (show M.val.obj ((proEtaleIsoPostcompose g).op.obj V) from
              (b.hom.app _ x).down)
    rw [IsIso.Iso.inv_hom]
    change (t.hom.app _ x).down =
      (c.inv.hom.app V).hom ((c.hom.hom.app V).hom (a.hom.app _ x).down) •
        (show M.val.obj ((proEtaleIsoPostcompose g).op.obj V) from
          (b.hom.app _ x).down)
    have hc (z : RY.obj.obj ((proEtaleIsoPostcompose g).op.obj V)) :
        (c.inv.hom.app V).hom ((c.hom.hom.app V).hom z) = z :=
      congrArg (fun f ↦ (f.hom.app V).hom z) c.hom_inv_id
    rw [hc]
    exact h _ x

/-- Sectionwise inverse image with an invertible coefficient identification preserves
K-flat complexes for the independent-coefficient tensor predicate.

Source: Stacks Project, Tag 06YN and the K-flatness part of the tensor argument in
`lem-pod-sectionwise-flat-kflat` (blueprint: lem-pod-sectionwise-flat-kflat-kflat).

Proof: the inverse reindexing functor is an exact equivalence and preserves the
colimits forming total tensor complexes. The sectionwise tensor comparison is
natural in both variables and respects the signed differential. For an acyclic
complex on the target site, transport it by the inverse, apply K-flatness, and
transport the resulting acyclic total tensor complex back. -/
theorem isoSectionwiseModuleInverseImage_preservesKFlat
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj RY ≅ RX)
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤
      SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) [F.Additive]
    (_hF : F = isoSectionwiseModuleInverseImage.{u, u} g
      (RY := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)
      (RX := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom) :
    ∀ K : CochainComplex (SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology Y) (R := RY) K →
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology X) (R := RX)
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  -- Use the already implemented stalk argument of Stacks 0DEP instead of
  -- reconstructing the total-tensor comparison for this particular equivalence.
  classical
  subst F
  let L := isoSectionwiseInverseImage g (Type (u + 1))
  have : L.IsEquivalence :=
    (isoSectionwiseInverseImage_equivalence.{u, u + 2, u + 1, 0, 0}
      g (Type (u + 1))).1
  let f : GeometricMorphism
      (Sheaf (ProEt.topology X) (Type (u + 1)))
      (Sheaf (ProEt.topology Y) (Type (u + 1))) :=
    { inverse := L
      direct := L.asEquivalence.inverse
      adj := L.asEquivalence.toAdjunction
      leftExact := inferInstance }
  let I := sectionwiseAlgebraicLift g RY RX c
  have : I.modules.Additive := by
    dsimp only [I, sectionwiseAlgebraicLift]
    infer_instance
  obtain ⟨ι, p, hp⟩ := proEtale_enoughPoints.{u, u} X
  let s : ∀ i, RingedSitePoint RX (p i) :=
    fun i ↦ Classical.choice (RingedSitePoint.nonempty RX (p i))
  have hcons : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse) := by
    constructor
    intro A B a _
    exact hp a (fun i ↦ (isIso_iff_bijective ((p i).inverse.map a)).1 inferInstance)
  exact SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (ProEt.topology Y) (ProEt.topology X) f I ι p s hcons

end AlgebraicGeometry.Scheme
