module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.OpenFlatLocus
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.PointwiseModuleFlatnessBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback

/-! # Relative module flat loci and arbitrary parameter base change

Source: Stacks Project, More on Morphisms, Tag 05VJ,
`lemma-base-change-criterion-flatness-fibre`
(blueprint: lem-sfb-relative-module-flat-locus-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The flat locus of a finitely presented quasi-coherent module flat over the parameter
scheme is open, and its formation commutes with arbitrary parameter base change.
Source: Stacks Project, More on Morphisms, Tag 05VJ
(blueprint: lem-sfb-relative-module-flat-locus-base-change).

Proof:
1. By lem-a1-map-over-base-finite-presentation, f is locally of finite presentation.
   Choose compatible affine neighbourhoods Spec B in Z and Spec C in X using
   lem-weil-pbc-affine-opens-basis. The map B to C is finitely presented by
   lem-weil-pbc-lfp-affine-opens-finite-presentation. The affine tilde counit
   (lem-weil-pbc-affine-tilde-gamma-adjunction) identifies M with the tilde of its
   sections N, finitely presented by lem-weil-pbc-finite-presentation-affine-sections.
2. The affine stalk identifications lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-spec-tilde-stalk-localization identify the locus with flatness of
   N localized at a prime of C over the corresponding localization of B.
   By lem-weil-pbc-flat-over-localization this is equivalent to B-flatness, whose
   locus is open by lem-weil-pbc-openness-of-flatness. These affine opens cover X.
3. M is flat over S by def-pc-scheme-module-flat-over. For a nonzero stalk,
   lem-sfb-fibrewise-module-flatness-criterion and clause (1) of
   lem-sfb-pointwise-module-flatness-base-change identify relative flatness with
   flatness on the residue fibre. The fibre square is cartesian by
   def-pc-fibre-product. For a zero stalk, lem-weil-pbc-module-stalk-pullback gives
   a zero pulled-back stalk, and both modules are flat. Thus the fibrewise
   characterization holds at every point, including zero stalks.
4. After any v, local finite presentation and local finite type persist by
   lem-weil-pbc-qcqs-morphism-permanence and lem-weil-pbc-lft-base-change.
   The pullback module is quasi-coherent by lem-weil-pbc-module-pullback-quasi-coherent,
   finitely presented by lem-pc-tensor-pullback-finite-presentation, and flat over
   the new base by lem-pc-relatively-flat-module-pullback. Repeat step 3 there.
5. For s' over s, lem-sfb-flat-residue-fibre-square identifies the cartesian square
   of residue fibres with flat horizontal maps, compatibly with their projections.
   The composition comparison of def-pc-module-pullback identifies the two iterated
   pullbacks of M. Its residue-fibre pullback is quasi-coherent by
   lem-weil-pbc-module-pullback-quasi-coherent. Both implications of
   lem-sfb-pointwise-module-flatness-base-change now equate the fibrewise flatness
   conditions. Steps 3 and 4 give precisely the inverse-image equality below.
-/
theorem isOpen_moduleFlatLocus_and_baseChange {S X Z : Scheme.{u}}
    (p : X ⟶ S) (a : Z ⟶ S) (f : X ⟶ Z) (hf : f ≫ a = p)
    [LocallyOfFinitePresentation p] [LocallyOfFiniteType a]
    (M : X.Modules) [SheafOfModules.IsQuasicoherent.{u} M]
    [SheafOfModules.IsFinitePresentation.{u} M] (hflat : M.IsFlatOver p) :
    IsOpen {x : X |
      Module.Flat (Z.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M))} ∧
    ∀ (S' : Scheme.{u}) (v : S' ⟶ S),
      {x' : ↥(pullback p v) |
        Module.Flat
          ((pullback a v).presheaf.stalk
            ((pullback.map p v a v f (𝟙 S') (𝟙 S)
              (by simpa only [Category.comp_id] using hf.symm) (by simp)) x'))
          ((ModuleCat.restrictScalars
            ((pullback.map p v a v f (𝟙 S') (𝟙 S)
              (by simpa only [Category.comp_id] using hf.symm) (by simp)).stalkMap x').hom).obj
            ((RingedSpace.moduleStalkFunctor (pullback p v).toRingedSpace x').obj
              ((Scheme.Modules.tensorPullback (pullback.fst p v)).obj M)))} =
        (pullback.fst p v) ⁻¹' {x : X |
          Module.Flat (Z.presheaf.stalk (f x))
            ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M))} := by
  sorry

end AlgebraicGeometry
