/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.FlatBaseDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorFlat

/-! # Stalkwise Tor-independence of base-flat complexes

## Implementation details

The localized comparison of the base-derived tensor cohomology model is used with its canonical
map. Its target is the ordinary tensor stalk complex, canonically the stalk of tensor pullback
by `Scheme.Modules.exists_tensorPullback_stalk_iso`, applied degreewise. The algebra-map
equations specify the actual structure maps of the cartesian square.

## References

* Stacks Project, Tags 0A1D and 0DJ8
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Base-flat bounded-above quasi-coherent complexes satisfy the stalkwise condition.

(Stacks, Tags 0A1D and 0DJ8) -/
theorem derivedPullback_torIndependent_flat_complex
    {S T X : Scheme.{u}} (g : T ⟶ S) (f : X ⟶ S)
    (G : CochainComplex X.Modules ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (G.X i))
    (hqc : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (hflat : ∀ i : ℤ, (G.X i).IsFlatOver f)
    (x' : ↥(pullback f g))
    [Algebra (S.presheaf.stalk (f ((pullback.fst f g) x'))) (X.presheaf.stalk ((pullback.fst f g)
      x'))] [Algebra (S.presheaf.stalk (f ((pullback.fst f g) x'))) (T.presheaf.stalk
      ((pullback.snd f g) x'))] [Algebra ((X.presheaf.stalk ((pullback.fst f g) x'))
      ⊗[(S.presheaf.stalk (f ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g)
      x'))) ((pullback f g).presheaf.stalk x')]
    (hRA : algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x'))) (X.presheaf.stalk
      ((pullback.fst f g) x')) = (f.stalkMap ((pullback.fst f g) x')).hom)
    (hRB : algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x'))) (T.presheaf.stalk
      ((pullback.snd f g) x')) =
      (g.stalkMap ((pullback.snd f g) x')).hom.comp (S.presheaf.stalkCongr (Inseparable.of_eq
        (congrArg (fun φ : pullback f g ⟶ S => φ x') pullback.condition))).hom.hom)
    (hAC : (algebraMap ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f
      ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g) x'))) ((pullback f
      g).presheaf.stalk x')).comp (algebraMap (X.presheaf.stalk ((pullback.fst f g) x'))
      ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f ((pullback.fst f g)
      x')))] (T.presheaf.stalk ((pullback.snd f g) x')))) =
      ((pullback.fst f g).stalkMap x').hom)
    (hBC : (algebraMap ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f
      ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g) x'))) ((pullback f
      g).presheaf.stalk x')).comp
      Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap x').hom)
    [HasDerivedCategory.{w} (ModuleCat.{u} (S.presheaf.stalk (f ((pullback.fst f g) x'))))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (T.presheaf.stalk ((pullback.snd f g) x')))]
    (M : ModuleCat.BaseDerivedTensorCohomologyModel (S.presheaf.stalk (f ((pullback.fst f g) x')))
      (X.presheaf.stalk ((pullback.fst f g) x')) (T.presheaf.stalk ((pullback.snd f g) x'))
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace ((pullback.fst f g)
      x')).mapHomologicalComplex (.up ℤ)).obj G) ((pullback f g).presheaf.stalk x')) :
    ∀ i : ℤ, IsIso (M.localizedComparison i) := by
  have _hqc := hqc
  let Q := ((RingedSpace.moduleStalkFunctor X.toRingedSpace
    ((pullback.fst f g) x')).mapHomologicalComplex (.up ℤ)).obj G
  let P := ((ModuleCat.restrictScalars
    (algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x')))
      (X.presheaf.stalk ((pullback.fst f g) x')))).mapHomologicalComplex (.up ℤ)).obj Q
  have hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i) := by
    obtain ⟨b, hb⟩ := hbounded
    refine ⟨b, fun i hi ↦ ?_⟩
    exact (ModuleCat.restrictScalars _).map_isZero
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace _).map_isZero (hb i hi))
  have hf : ∀ i : ℤ,
      Module.Flat (S.presheaf.stalk (f ((pullback.fst f g) x'))) (P.X i) := by
    intro i
    exact relative_flat_module_stalk f (G.X i) (hflat i) _ hRA
  have hK := CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat P hb hf
  have hC := pullback_stalk_tensor_flat g f x' hRA hRB hAC hBC
  exact ModuleCat.localizedComparison_isIso_of_kFlat_flat Q hK hC M

end AlgebraicGeometry
