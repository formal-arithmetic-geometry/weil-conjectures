module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.FibreFlatnessCompatibleStalkData
import WeilConjectures.AlgebraicGeometry.FinitePresentationStalkOfLocalPresentation
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Sheaf.RingTheory.FiniteTypeLocalClosedFibreApproximation
import WeilConjectures.RingTheory.FlatOfFlatClosedFiber
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Fibrewise flatness criterion for a finitely presented module

Source: Stacks Project, More on Morphisms, Tag 039C,
`theorem-criterion-flatness-fibre`, implication (1) to (2), without the openness clause.
(blueprint: lem-sfb-fibrewise-module-flatness-criterion).

The fibre module is the actual tensor pullback along the fibre projection. All
relative module structures are restrictions along the displayed scheme stalk maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonzero finitely presented module stalk, flat over the base and flat on the
fibre over the target, is flat over the target, which is itself flat over the base
at the image point.

Source: Stacks Project, More on Morphisms, Tag 039C,
`theorem-criterion-flatness-fibre`, implication (1) to (2).
(blueprint: lem-sfb-fibrewise-module-flatness-criterion).

Proof:
1. Set R = O_{S,p(x)}, B = O_{Y,f(x)}, C = O_{X,x}, M = F_x. The compatible
   stalk-data lemma gives the local tower R -> B -> C, C essentially finitely
   presented over R, B essentially of finite type over R, and the compatible
   quotient descriptions of fibre stalks. A finite local presentation of F makes
   M finitely presented, hence finite, over C by the finite-presentation stalk
   lemma. It is nonzero and R-flat by hypothesis.
2. The pullback-stalk formula and the quotient-tensor equivalence identify the
   stalk of the fibre pullback with M/m_R M. Indeed, (m_R C)M = m_R M, since both
   consist of finite sums of products of images of elements of m_R with vectors.
   Compatibility of fibre stalk maps identifies its B/m_R B-action with
   [b][m] = [beta(b)m]. The fibre hypothesis is flatness for this action.
3. The finite-type local closed-fibre approximation gives a local surjection
   u : T -> B, with T essentially finitely presented over R and T/m_R T
   isomorphic to B/m_R B by [t] -> [u(t)]. Give C and M the actions through B.
   The composite T -> C is local; transport step 2 across this quotient
   isomorphism. The closed-fibre criterion applied to R -> T -> C and M gives
   T flat over R and M flat over T. Its other hypotheses are those in step 1.
4. Since T -> C is local, m_T M is contained in m_C M. If m_T M = M, Nakayama
   over C would make the finite C-module M zero. Thus M/m_T M is nonzero, and
   the maximal-ideal criterion makes the flat T-module M faithfully flat.
5. K = ker(u) annihilates M. Tensoring K -> T with M is injective by flatness
   and zero because K kills M. Thus K tensor_T M = 0, and faithful flatness
   gives K = 0. The surjection u is an isomorphism. Transporting step 3 along
   u gives B flat over R and M flat over B with the original stalk actions.
   The former is exactly flatness of q at f(x).

The inputs, in order, are `lem-sfb-fibre-flatness-compatible-stalk-data`,
`lem-weil-pbc-stalk-finite-presentation-of-local-presentation`,
`lem-weil-pbc-module-stalk-pullback`, `lem-weil-pbc-tensor-over-quotient-ring`,
`lem-sfb-finite-type-local-closed-fibre-approximation`,
`lem-weil-pbc-criterion-flatness-fibre`, `lem-weil-pbc-nakayama-local-generators`,
`lem-weil-pbc-flat-module-faithfully-flat-maximal-ideals`,
`def-weil-pbc-flat-ring-map`, `def-weil-pbc-faithfully-flat-ring-map`, and
`def-weil-flat-morphism`.
-/
theorem Scheme.Hom.module_flatAt_and_base_flatAt_of_fiber_module_flatAt
    {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p)
    [LocallyOfFinitePresentation p] [LocallyOfFiniteType q]
    (F : X.Modules) [SheafOfModules.IsQuasicoherent.{u} F]
    [SheafOfModules.IsFinitePresentation.{u} F]
    (x : X) [Nontrivial ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)]
    (hbase : Module.Flat (S.presheaf.stalk (p x))
      ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)))
    (hfibre : Module.Flat
      ((q.fiber (p x)).presheaf.stalk
        ((pullback.map p (S.fromSpecResidueField (p x))
          q (S.fromSpecResidueField (p x)) f (𝟙 _) (𝟙 S)
          ((Category.comp_id p).trans hf.symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (p.asFiber x)))
      ((ModuleCat.restrictScalars
        ((pullback.map p (S.fromSpecResidueField (p x))
          q (S.fromSpecResidueField (p x)) f (𝟙 _) (𝟙 S)
          ((Category.comp_id p).trans hf.symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm)).stalkMap
            (p.asFiber x)).hom).obj
        ((RingedSpace.moduleStalkFunctor (p.fiber (p x)).toRingedSpace (p.asFiber x)).obj
          ((Scheme.Modules.tensorPullback (p.fiberι (p x))).obj F)))) :
    Module.Flat (Y.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) ∧
      (q.stalkMap (f x)).hom.Flat := by
  sorry

end AlgebraicGeometry
