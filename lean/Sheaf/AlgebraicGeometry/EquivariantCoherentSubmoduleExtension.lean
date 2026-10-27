/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.GroupoidModuleLimitsColimits
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeAffineGenerators
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Extending a coherent equivariant submodule from an invariant open

Source: agent-formulated consequence of Stacks Project, Groupoids, Tags 07TU,
09VH, 077S and 077R, and Cohomology of Schemes, Tag 01Y1.
(blueprint: lem-sfb-equivariant-coherent-submodule-extension)

The ambient object is a quasi-coherent groupoid module, with no coherence
hypothesis. Submodules are specified by monomorphisms of the underlying sheaves.
An isomorphism over the restricted ambient sheaf expresses equality of submodules,
and its equivariance retains the prescribed linearization.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.EquivariantCoherent

/-- A coherent equivariant submodule on an invariant open extends inside a
quasi-coherent equivariant ambient module. The open immersion `j` is equivariant;
for a group action this is equivalent to invariance of its image, including the
reverse inclusion obtained by inversion. `DY` and `DU` present the given action
groupoids, with composition fixed on every test scheme by `group_coordinate`.
The equation `hn` is the equivariance square for the given inclusion into `j^*M`.
Its comparison maps are the section-normalized tensor-pullback comparisons.

Source: agent assembly of Stacks Project, Groupoids, Tags 07TU, 09VH, 077S, 077R;
Cohomology of Schemes, Tag 01Y1. These supply ingredients, not this exact theorem.
(blueprint: lem-sfb-equivariant-coherent-submodule-extension)

Proof plan:
1. The field spectrum is Noetherian. Finite type makes Y and G times Y Noetherian
(lem-weil-pbc-finite-type-over-noetherian). Projection is flat by lem-pc-flat-field
and lem-weil-pbc-flat-morphism-base-change, and affine, quasi-compact and
quasi-separated by lem-weil-pbc-affine-morphism-permanence. The automorphism
(g,y) -> (g,gy) identifies action and projection, giving the same properties for
both source and target. Finite type uses lem-sfb-finite-type-composition-base-change.
2. The action groupoid has source projection, target action, identity (1,y),
inverse (g,y) -> (g^-1,gy), and composition (g,hy),(h,y) -> (gh,y).
These are precisely def-a1-scheme-groupoid-laws and def-sfb-scheme-groupoid-module,
with descent directed from target pullback to source pullback.
3. The open immersion is quasi-compact by lem-sfb-noetherian-open-immersion-qc,
and quasi-separated. Its source and target squares are Cartesian by invariance.
The restricted groupoid is flat by base change. Apply
lem-sfb-cartesian-groupoid-pushforward-adjunction: pushforward preserves
quasi-coherent equivariant modules, its adjunction transposes are equivariant,
and restriction of its counit is an equivariant isomorphism. The open is
quasi-compact by lem-weil-pbc-qcqs-morphism-permanence, so choose a finite affine cover.
4. Form Q=(j^*M)/N and the adjoint equivariant map v:M -> j_*Q. Put P=ker(v).
By lem-sfb-groupoid-module-limits-colimits these are computed on underlying
modules, so restriction gives j^*P=N, equivariantly as submodules of j^*M.
5. By lem-sfb-flat-noetherian-groupoid-coherent-approximation write P as a small
nonempty filtered colimit of coherent linearized P_i with equivariant maps to P.
The colimit is underlying by lem-sfb-groupoid-module-limits-colimits, and evaluates
on each affine of the finite cover by lem-weil-pbc-quasi-coherent-module-colimit-evaluation.
6. Choose finitely many generators on each affine by
lem-weil-pbc-module-finite-type-affine-generators and lem-weil-pbc-affine-scheme-qcqs.
Lift them to stages using lem-weil-pbc-filtered-colimit-modules-elementwise.
Filteredness supplies one stage capturing all generators, hence surjecting onto N
on U. For an empty list or empty U use any object of the nonempty index category.
7. Take L to be the image of P_i -> P -> M. Images are quasi-coherent and
equivariant by lem-sfb-groupoid-module-limits-colimits. The coherent source P_i
has quasi-coherent kernel, so its quotient L is coherent by
lem-weil-pbc-coherent-kernel-cokernel-locnoeth; M need not be coherent.
8. Open restriction preserves kernels, cokernels and images. Thus j^*L is the
image of the restricted map, exactly N by steps 4 and 6. The induced isomorphism
is equivariant by reflection of isomorphisms in
lem-sfb-groupoid-module-limits-colimits, and commutes with the specified inclusions.
-/
theorem exists_equivariant_coherent_submodule_extension
    {F : Type u} [Field F]
    (G Y U : Over (Spec (.of F))) [GrpObj G] [ModObj G Y] [ModObj G U]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (j : U ⟶ Y) [IsModHom G j] [IsOpenImmersion j.left]
    (DY : ActionGroupoidModel G Y) (DU : ActionGroupoidModel G U)
    (M : Scheme.GroupoidModule (source G Y) (target G Y)
      (identityArrow G Y) (inverseArrow G Y) DY.comp DY.laws)
    (N : Coherent DU)
    (n : underlying N ⟶ (Scheme.Modules.tensorPullback j.left).obj M.moduleObj)
    [Mono n]
    (hn : ∀ (ha : target G U ≫ j.left = (G ◁ j).left ≫ target G Y)
      (hp : source G U ≫ j.left = (G ◁ j).left ≫ source G Y),
      (Scheme.Modules.tensorPullback (target G U)).map n ≫
          (mixedCompComparison (target G U) (G ◁ j).left
            j.left (target G Y) ha M.moduleObj).hom ≫
          (Scheme.Modules.tensorPullback (G ◁ j).left).map
            ((pullbackIso (target G Y)).inv.app M.moduleObj ≫ M.beta.hom ≫
              (pullbackIso (source G Y)).hom.app M.moduleObj) ≫
          (mixedCompComparison (source G U) (G ◁ j).left
            j.left (source G Y) hp M.moduleObj).inv =
        (linearization N).hom ≫ (Scheme.Modules.tensorPullback (source G U)).map n) :
    ∃ (L : Coherent DY) (l : L.obj ⟶ M), Mono l.val ∧
      ∃ e : (Scheme.Modules.tensorPullback j.left).obj (underlying L) ≅ underlying N,
        IsPullbackMap j L N e.hom ∧
          (Scheme.Modules.tensorPullback j.left).map l.val = e.hom ≫ n := by
  sorry

end AlgebraicGeometry.EquivariantCoherent
