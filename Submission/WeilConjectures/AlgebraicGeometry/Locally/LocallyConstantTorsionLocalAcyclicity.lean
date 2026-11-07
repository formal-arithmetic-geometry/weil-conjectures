/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.GroupTheory.OrderOfElement
import Submission.WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalConstantComparison
import Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantTorsionAcyclicDevissage
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Local acyclicity for locally constant torsion coefficients

Source: Stacks Project, Tag 0GJR, lemma-locally-acyclic-locally-constant
(blueprint: lem-weil-pbc-locally-constant-torsion-local-acyclicity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Local acyclicity extends to locally constant abelian sheaves whose stalk elements
have finite order prime to the residue characteristic; in characteristic zero every
finite order is allowed. No finiteness of stalks or common annihilator is assumed.
Source: Stacks Project, Tag 0GJR, lemma-locally-acyclic-locally-constant
(blueprint: lem-weil-pbc-locally-constant-torsion-local-acyclicity).

Proof:
1. Fix a geometric point x and a test geometric point t, and put V equal to the
strict-local fibre. The strict henselizations are affine, so V is affine and qcqs.
The germ-compatible constant comparison identifies the pullback of G to V with the
constant sheaf on its geometric stalk M. Under this comparison the specified alpha
map is the constant-section unit followed by the sections of the comparison.
2. Apply this same comparison first to every admissible constant cyclic sheaf on X.
Its geometric stalk is canonically its coefficient group. Naturality of the
constant-section unit and invariance of cohomology under isomorphism convert the
hypothesis on f into invertibility of that unit and positive cohomology vanishing
for the constant cyclic sheaf on V itself.
3. Apply the constant-coefficient devissage lemma. The finitely generated subgroups
of M form a directed colimit and are finite because M is torsion. A finite abelian
group is a finite sum of cyclic groups; each cyclic generator retains its order in M,
so its order is admissible. Additivity of derived cohomology handles these finite sums.
Constant sheaves preserve colimits, and qcqs etale cohomology preserves filtered colimits
at the coefficient universe, including degree zero through its comparison with sections.
Thus the constant-section unit for M is invertible and its positive cohomology vanishes.
4. Transport these two conclusions along the germ-compatible comparison from step 1.
The equality for the specified alpha map gives its invertibility, and the cohomology
isomorphism gives positive vanishing. This holds for every x and t. -/
theorem isLocallyAcyclicRelative_of_locallyConstant_torsion
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : IsLocallyAcyclic f)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Scheme.IsLocallyConstantSheaf G]
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
      (m : ((Scheme.pointSmallEtale x).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G),
      IsOfFinAddOrder m ∧
        (ringChar (X.residueField (x default)) = 0 ∨
          (addOrderOf m).Coprime (ringChar (X.residueField (x default))))) :
    IsLocallyAcyclicRelative f G := by
  intro Ω _ _ x Ω' _ _ t
  let M := (Scheme.pointSmallEtale x).sheafFiber.obj G
  let V := localAcyclicityFiber f x t
  let C := constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γ := Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}
  let η := (constantSheafΓAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}).unit
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : IsAffine (Scheme.strictHenselizationScheme x) := by
    unfold Scheme.strictHenselizationScheme
    infer_instance
  have : IsAffine (Scheme.strictHenselizationScheme (x ≫ f)) := by
    unfold Scheme.strictHenselizationScheme
    infer_instance
  have : IsAffine V := by
    dsimp [V, localAcyclicityFiber]
    infer_instance
  have hcyclic (n : ℕ) (hn : 0 < n)
      (hp : ringChar (X.residueField (x default)) = 0 ∨
        n.Coprime (ringChar (X.residueField (x default)))) := hf Ω x n hn hp Ω' t
  have hunit (n : ℕ) (hn : 0 < n)
      (hp : ringChar (X.residueField (x default)) = 0 ∨
        n.Coprime (ringChar (X.residueField (x default)))) :
      IsIso (η.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) ∧
      ∀ q : ℕ, 0 < q → Limits.IsZero
        ((cohomology AddCommGrpCat.{u + 1} V (q : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (C.obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))))) := by
    let N := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
    let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N
    have hc : F.IsConstant X.smallEtaleTopology := ⟨N, ⟨Iso.refl _⟩⟩
    have : Scheme.IsLocallyConstantSheaf F := hc.isLocallyConstantSheaf
    obtain ⟨e, he⟩ := exists_strictLocalConstantComparison f x t F
    let a := (Scheme.pointSmallEtale x).sheafFiberConstantSheafIso N
    have hα := (hcyclic n hn hp).1
    rw [he] at hα
    have hη : IsIso (η.app ((Scheme.pointSmallEtale x).sheafFiber.obj F)) :=
      (isIso_comp_right_iff _ _).mp hα
    have hnatur : η.app N =
        a.inv ≫ η.app ((Scheme.pointSmallEtale x).sheafFiber.obj F) ≫
          (C ⋙ Γ).map a.hom := by
      rw [← η.naturality a.hom]
      simp
    constructor
    · rw [hnatur]
      infer_instance
    · intro q hq
      let H := DerivedCategory.singleFunctor _ 0 ⋙ cohomology AddCommGrpCat.{u + 1} V (q : ℤ)
      exact Limits.IsZero.of_iso ((hcyclic n hn hp).2 q hq)
        (H.mapIso ((C.mapIso a).symm ≪≫ e))
  obtain ⟨hη, hH⟩ := constantTorsion_acyclic_of_cyclic V
    (ringChar (X.residueField (x default))) hunit M (hG Ω x)
  obtain ⟨e, he⟩ := exists_strictLocalConstantComparison f x t G
  constructor
  · rw [he]
    infer_instance
  · intro q hq
    exact Limits.IsZero.of_iso (hH q hq)
      (((DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} V (q : ℤ)).mapIso e).symm)

end AlgebraicGeometry.Etale
