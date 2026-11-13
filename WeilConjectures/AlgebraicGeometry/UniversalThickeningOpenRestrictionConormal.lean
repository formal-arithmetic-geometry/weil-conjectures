/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormallyUnramifiedConormal
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKernelModule

/-!
# Conormal modules of universal thickenings under open restriction

The conormal module of a formally unramified morphism, computed from its universal first
order thickening, is compatible with restriction to opens.

## References

* [Stacks Project, Tag 04FA](https://stacks.math.columbia.edu/tag/04FA)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The conormal comparison for open restriction data: the restricted morphism `hV` is formally
unramified with universal first order thickening `hV'`, and the restriction to `V` of the
conormal module of `h` is isomorphic to the conormal module of `hV`. -/
theorem universalFirstOrderThickening_open_restriction_conormal
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : IsUniversalFirstOrderThickening h i h')
    (hform : FormallyUnramified h)
    {V : Z.Opens} {U : X.Opens}
    {hV : V.toScheme ⟶ U.toScheme} {V' : Z'.Opens}
    {iV : V.toScheme ⟶ V'.toScheme} {hV' : V'.toScheme ⟶ U.toScheme}
    (hdata : i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
      iV ≫ V'.ι = V.ι ≫ i ∧ hV' ≫ U.ι = V'.ι ≫ h' ∧
      iV ≫ hV' = hV ∧ IsUniversalFirstOrderThickening hV iV hV') :
    ∃ (hVform : FormallyUnramified hV),
      ∃ (HV : IsUniversalFirstOrderThickening hV iV hV'),
        Nonempty
          ((Scheme.Modules.restrictFunctor V.ι).obj
              (@formallyUnramifiedConormal _ _ _ h hform i h' H) ≅
            @formallyUnramifiedConormal _ _ _ hV hVform iV hV' HV) := by
  have hcompat : i ≫ h' = h := H.2.1
  have hfactor : hV ≫ U.ι = V.ι ≫ h := by
    rw [← hdata.2.2.2.2.1, Category.assoc, hdata.2.2.2.1,
      ← Category.assoc, hdata.2.2.1, Category.assoc, hcompat]
  let : FormallyUnramified h := hform
  have : FormallyUnramified (V.ι ≫ h) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have : FormallyUnramified (hV ≫ U.ι) := by rw [hfactor]; infer_instance
  have hVform : FormallyUnramified hV := FormallyUnramified.of_comp hV U.ι
  let HV := hdata.2.2.2.2.2
  let : IsClosedImmersion i := H.1.1
  let : IsClosedImmersion iV := HV.1.1
  obtain ⟨e⟩ := nonempty_tensorPullback_open_kernel i iV hdata.1 hdata.2.2.1
  let a := (Scheme.Modules.restrictAdjunction V.ι).leftAdjointUniq
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction V.ι))
  obtain ⟨b⟩ := Scheme.Modules.nonempty_tensorPullbackComp V.ι i
  obtain ⟨c⟩ := Scheme.Modules.nonempty_tensorPullbackComp iV V'.ι
  have d : Scheme.Modules.tensorPullback (V.ι ≫ i) ≅
      Scheme.Modules.tensorPullback (iV ≫ V'.ι) :=
    eqToIso (congrArg Scheme.Modules.tensorPullback hdata.2.2.1.symm)
  refine ⟨hVform, HV, ⟨?_⟩⟩
  exact a.app _ ≪≫ (b.app _).symm ≪≫ d.app _ ≪≫ c.app _ ≪≫
    (Scheme.Modules.tensorPullback iV).mapIso e

end AlgebraicGeometry
