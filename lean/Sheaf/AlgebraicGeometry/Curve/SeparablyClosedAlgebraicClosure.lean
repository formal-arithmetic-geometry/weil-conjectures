module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Passage to an algebraic closure of a separably closed field

Source: blueprint `det-curve-invariance-inseparable-closure` (the node and its
proof), based on the Stacks Project étale topological invariance result, Tag 03SI.
(blueprint: det-curve-invariance-inseparable-closure)

## Main statements

* `AlgebraicGeometry.Etale.cohomology_invariance_of_isSepClosed_algebraicClosure`
  states universal-homeomorphism and étale-cohomology invariance after passing to
  an algebraic closure, together with functoriality for a further extension.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map from the pullback over `kbar'` to the pullback over `kbar`.
Source: blueprint `det-curve-invariance-inseparable-closure`, first and second proof
paragraphs (blueprint: det-curve-invariance-inseparable-closure).
-/
noncomputable def algebraicClosurePullbackToClosure
    {k kbar kbar' : Type u} [Field k] [Field kbar] [Field kbar']
    [Algebra k kbar] [Algebra k kbar']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (e : kbar →ₐ[k] kbar')
    (h_e : Spec.map (CommRingCat.ofHom (algebraMap k kbar')) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k kbar))) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar'))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) :=
  pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k kbar'))) f
    (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (𝟙 C)
    (Spec.map (CommRingCat.ofHom e.toRingHom)) (𝟙 _) (by
      simp only [Category.comp_id, Category.id_comp]) h_e

/-- The canonical map from the pullback over `kbar'` to the pullback over `k'`.
Source: blueprint `det-curve-invariance-inseparable-closure`, second proof paragraph
(blueprint: det-curve-invariance-inseparable-closure).
-/
noncomputable def algebraicClosurePullbackToExtension
    {k k' kbar' : Type u} [Field k] [Field k'] [Field kbar']
    [Algebra k k'] [Algebra k' kbar'] [Algebra k kbar']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (h_tower : Spec.map (CommRingCat.ofHom (algebraMap k kbar')) =
      Spec.map (CommRingCat.ofHom (algebraMap k' kbar')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k'))) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar'))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k kbar'))) f
    (Spec.map (CommRingCat.ofHom (algebraMap k k'))) (𝟙 C)
    (Spec.map (CommRingCat.ofHom (algebraMap k' kbar'))) (𝟙 _) (by
      simp only [Category.comp_id, Category.id_comp]) h_tower

namespace Etale

/-- Passage to an algebraic closure over a separably closed field preserves the
small étale cohomology of every abelian sheaf, and the resulting pullback maps are
functorial for a further separably closed extension.

Source: blueprint `det-curve-invariance-inseparable-closure`, node and proof,
using the Stacks Project Tags 03SI and 04DF.
(blueprint: det-curve-invariance-inseparable-closure)

Proof plan: the algebraic closure of a separably closed field is purely inseparable;
the induced spectrum map is therefore integral, radicial, and surjective, hence a
universal homeomorphism. Base change preserves this property, and topological
invariance gives bijectivity of every étale cohomology pullback. For compatible
closures over `k ⊆ k'`, the two composites to `C` agree and the composition law
for étale cohomology pullback identifies the two paths in the square.
-/
theorem cohomology_invariance_of_isSepClosed_algebraicClosure
    {k k' kbar kbar' : Type u}
    [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] [Algebra k k']
    [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
    [Algebra.IsAlgebraic k kbar]
    [Field kbar'] [IsAlgClosed kbar'] [Algebra k' kbar'] [Algebra k kbar']
    [IsScalarTower k k' kbar'] [Algebra.IsAlgebraic k' kbar']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (e : kbar →ₐ[k] kbar')
    (h_e : Spec.map (CommRingCat.ofHom (algebraMap k kbar')) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k kbar)))
    (h_tower : Spec.map (CommRingCat.ofHom (algebraMap k kbar')) =
      Spec.map (CommRingCat.ofHom (algebraMap k' kbar')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k')))
    (h_comp : algebraicClosurePullbackToClosure f e h_e ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) =
      algebraicClosurePullbackToExtension f h_tower ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsUniversalHomeomorphism
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) ∧
      (∀ q : ℕ, Function.Bijective (cohomologyMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) F q)) ∧
      (∀ (q : ℕ) (x : Sheaf.H F q),
        Sheaf.H.map
            ((upperStarComp AddCommGrpCat.{u + 1}
              (algebraicClosurePullbackToClosure f e h_e)
              (pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))).inv.app F) q
          (cohomologyMap (algebraicClosurePullbackToClosure f e h_e)
            ((upperStar AddCommGrpCat.{u + 1}
              (pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))).obj F) q
            (cohomologyMap (pullback.fst f
              (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) F q x)) =
        cast (congrArg (fun g ↦
            Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj F) q) h_comp).symm
          (Sheaf.H.map
            ((upperStarComp AddCommGrpCat.{u + 1}
              (algebraicClosurePullbackToExtension f h_tower)
              (pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).inv.app F) q
            (cohomologyMap (algebraicClosurePullbackToExtension f h_tower)
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst f
                  (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj F) q
              (cohomologyMap (pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F q x)))) := by
  sorry

end Etale
end AlgebraicGeometry
