/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackNaturality
import Sheaf.AlgebraicGeometry.ModuleAbelianCohomologyLargePullback

/-! # Pullback compatibility of the normalized quasi-coherent comparison

Source: Stacks Project, Tags 03P2, 03FD, 010T and 01F7.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
  RingedSpace.moduleCohomology moduleAbelianCohomologyLarge moduleCohomologyFMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The normalized comparison intertwines the canonical cohomology pullbacks.
The comparisons are given; this assertion supplies their pullback compatibility
and the structural coefficient morphism.

Source: Stacks Project, Tags 03P2, 01FD, 03AX, 010T and 0BDY.
(blueprint: lem-weil-pbc-qcoherent-normalized-pullback-square)

Proof: Structural tensor-section pullback to each base-changed etale object
commutes with restrictions by adjunction coherence. Applying coefficient lift
therefore gives theta with exactly the displayed component formula. Transport
module cohomology to large abelian Zariski cohomology by the concrete resolution
comparison. It respects pullback, by its coefficient and edge naturality and
functoriality of the change of Ext universe. The two normalized comparisons
then commute with pullback by induction on degree. Degree zero is the section
unit identity. In positive degree embed F into a quasicoherent acyclic module
using a finite affine cover. This embedding remains monic after arbitrary
pullback. Push the pulled-back embedding out along psi and take cokernels to
obtain a commuting square of short exact sequences of quasicoherent modules.
Acyclicity makes the source boundary surjective. Write the class as a boundary,
apply induction to the quotient map and use compatibility of both cohomology
maps and both normalized comparisons with boundaries. Finally undo the two
resolution comparisons and cancel cY. Empty schemes and zero coefficients
satisfy the same embedding and exact-sequence argument. -/
theorem qcoherentNormalizedComparison_pullback_square
    (X Y : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
    [CompactSpace Y] [Scheme.IsSeparated Y]
    (cX : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf F) q)
    (cY : ∀ (G : Y.Modules) [G.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj G) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf G) q)
    (hcX : IsNormalizedCoherentEtaleComparison X
      (fun F _ q ↦ (moduleAbelianCohomologyLarge X F q).symm.trans (cX F q)))
    (hcY : IsNormalizedCoherentEtaleComparison Y
      (fun G _ q ↦ (moduleAbelianCohomologyLarge Y G q).symm.trans (cY G q)))
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G) :
    ∃ θ : liftedCoherentEtaleSheaf F ⟶
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G),
      (∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
        θ.hom.app (op U) (ULift.up s) = ULift.up
          (qcoherentPullbackSection g F G ψ U
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
            (pullback.fst U.hom g) pullback.condition s)) ∧
      ∀ (q : ℕ) (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
        (cY G q).symm (Sheaf.H.map
          ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
            (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
          q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q x)) =
        moduleCohomologyFMap g
          ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ)
          q ((cX F q).symm x) := by
  classical
  let θ := qcoherentPullbackSheafMap g F G ψ
  refine ⟨θ, (fun _ _ ↦ rfl), ?_⟩
  intro q x
  apply (cY G q).injective
  rw [AddEquiv.apply_symm_apply]
  let dX (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :=
    (moduleAbelianCohomologyLarge X M n).symm.trans (cX M n)
  let dY (M : Y.Modules) [M.IsQuasicoherent] (n : ℕ) :=
    (moduleAbelianCohomologyLarge Y M n).symm.trans (cY M n)
  have h := normalizedCoherentEtale_pullback_naturality X Y dX dY hcX hcY g
    q F G ψ (moduleAbelianCohomologyLarge X F q ((cX F q).symm x))
  have hX : dX F q
      (moduleAbelianCohomologyLarge X F q ((cX F q).symm x)) = x := by
    simp only [dX, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    exact (cX F q).apply_symm_apply x
  let φ := (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ
  have hp := moduleAbelianCohomologyLarge_pullback g F G φ q ((cX F q).symm x)
  have hY : dY G q
      (moduleAbelianCohomologyLarge Y G q
        (moduleCohomologyFMap g φ q ((cX F q).symm x))) =
      cY G q (moduleCohomologyFMap g φ q ((cX F q).symm x)) := by
    simp only [dY, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rfl
  have hh := (congrArg (dY G q) hp).trans h
  have hf := hY.symm.trans
    (hh.trans (congrArg (etalePullbackCohomology g F G ψ q) hX))
  simpa only [etalePullbackCohomology,
    Sheaf.adjointCohomologyPullbackMap, Sheaf.cohomologyPullbackMap_apply,
    Etale.cohomologyMap, AddMonoidHom.comp_apply] using hf.symm

end
end AlgebraicGeometry.Scheme.Modules
