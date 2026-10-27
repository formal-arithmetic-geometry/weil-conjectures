module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar mates in a finite ordered tower

Source: blueprint sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts, iterated projective-line integration
(blueprint: lem-sp-finite-tower-scalar-mates).

The finite index type retains exactly the categories at levels zero through `d`.
The auxiliary definitions implement the recursions in the statement. In particular,
the adjunction is Mathlib's actual ordered composite, and its counit is not extra data.
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v'

namespace CategoryTheory

open CategoryTheory.Functor

/-- The left functors in the finite recursion, starting with the identity.
Source: blueprint exceptional scalar comparison, Charts, ordered iteration
(blueprint: lem-sp-finite-tower-scalar-mates). -/
def finiteScalarLeft {d : ℕ} {C : Fin (d + 1) → Type u}
    [∀ r, Category.{v} (C r)] (L : ∀ r : Fin d, C r.succ ⥤ C r.castSucc) :
    (r : Fin (d + 1)) → C r ⥤ C 0 :=
  Fin.induction (𝟭 _) (fun r F ↦ L r ⋙ F)

/-- The right functors in the finite recursion, starting with the identity.
Source: blueprint exceptional scalar comparison, Charts, ordered iteration
(blueprint: lem-sp-finite-tower-scalar-mates). -/
def finiteScalarRight {d : ℕ} {C : Fin (d + 1) → Type u}
    [∀ r, Category.{v} (C r)] (W : ∀ r : Fin d, C r.castSucc ⥤ C r.succ) :
    (r : Fin (d + 1)) → C 0 ⥤ C r :=
  Fin.induction (𝟭 _) (fun r G ↦ G ⋙ W r)

/-- The actual ordered composite adjunction, with the identity adjunction at zero.
Its successor counit is `F_r.map (e_r.app (G_r.obj K)) ≫ E_r.app K`, by
`Adjunction.comp_counit_app`; hence it has exactly the specified counit recursion.
Source: blueprint exceptional scalar comparison, Charts; Stacks 0DV0
(blueprint: lem-sp-finite-tower-scalar-mates). -/
def finiteScalarAdjunction {d : ℕ} {C : Fin (d + 1) → Type u}
    [∀ r, Category.{v} (C r)]
    {L : ∀ r : Fin d, C r.succ ⥤ C r.castSucc}
    {W : ∀ r : Fin d, C r.castSucc ⥤ C r.succ}
    (adj : ∀ r, L r ⊣ W r) :
    (r : Fin (d + 1)) → finiteScalarLeft L r ⊣ finiteScalarRight W r :=
  Fin.induction Adjunction.id (fun r composite ↦ (adj r).comp composite)

/-- The recursively pasted left comparison `B_r`, with identity components at zero.
The associators only insert the parentheses required by functor composition.
Source: blueprint exceptional scalar comparison, Charts, scalar squares
(blueprint: lem-sp-finite-tower-scalar-mates). -/
def finiteScalarLeftComparison {d : ℕ}
    {C : Fin (d + 1) → Type u} {D : Fin (d + 1) → Type u'}
    [∀ r, Category.{v} (C r)] [∀ r, Category.{v'} (D r)]
    (L : ∀ r : Fin d, C r.succ ⥤ C r.castSucc)
    (L' : ∀ r : Fin d, D r.succ ⥤ D r.castSucc)
    (T : ∀ r, C r ⥤ D r)
    (b : ∀ r, L r ⋙ T r.castSucc ≅ T r.succ ⋙ L' r) :
    (r : Fin (d + 1)) → finiteScalarLeft L r ⋙ T 0 ≅ T r ⋙ finiteScalarLeft L' r :=
  Fin.induction ((T 0).leftUnitor ≪≫ (T 0).rightUnitor.symm)
    (fun r B ↦
      associator _ _ _ ≪≫ isoWhiskerLeft (L r) B ≪≫
        (associator _ _ _).symm ≪≫
        isoWhiskerRight (b r) (finiteScalarLeft L' r.castSucc) ≪≫ associator _ _ _)

/-- The recursively pasted right comparison `A_r`, with identity components at zero.
This uses the given right squares, rather than defining them to be mates.
Source: blueprint exceptional scalar comparison, Charts, scalar squares
(blueprint: lem-sp-finite-tower-scalar-mates). -/
def finiteScalarRightComparison {d : ℕ}
    {C : Fin (d + 1) → Type u} {D : Fin (d + 1) → Type u'}
    [∀ r, Category.{v} (C r)] [∀ r, Category.{v'} (D r)]
    (W : ∀ r : Fin d, C r.castSucc ⥤ C r.succ)
    (W' : ∀ r : Fin d, D r.castSucc ⥤ D r.succ)
    (T : ∀ r, C r ⥤ D r)
    (a : ∀ r, W r ⋙ T r.succ ≅ T r.castSucc ⋙ W' r) :
    (r : Fin (d + 1)) → finiteScalarRight W r ⋙ T r ≅ T 0 ⋙ finiteScalarRight W' r :=
  Fin.induction ((T 0).leftUnitor ≪≫ (T 0).rightUnitor.symm)
    (fun r A ↦
      associator _ _ _ ≪≫ isoWhiskerLeft (finiteScalarRight W r.castSucc) (a r) ≪≫
        (associator _ _ _).symm ≪≫ isoWhiskerRight A (W' r) ≪≫ associator _ _ _)

/-- Finite ordered scalar squares paste to mates for the actual composite adjunctions,
and intertwine their actual counits. At zero, both recursive functors are identities,
the adjunction is `Adjunction.id`, and both comparisons have identity components.

Source: blueprint sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts, scalar mates and counits
(blueprint: lem-sp-finite-tower-scalar-mates).

Proof: induct on the level. Compose each next adjunction with the previous composite
using `Adjunction.comp`; its counit formula is the displayed ordered recursion.
At zero the identity adjunctions and identity comparisons satisfy the mate component
formula. Whiskering preserves the two inverse equations, so the successor comparisons
are isomorphisms, and the inverse of the successor left comparison reverses its two
factors. Apply `mateEquiv_hcomp` (lem-weil-pbc-mate-pasting, clause 2) to the step square
and the inductively pasted square: its right comparison is precisely the successor
right recursion. This proves the mate assertion at the final level. Then apply
`mateEquiv_counit` (lem-amb-mate-unit-counit) to the inverse left comparison and
precompose by the left comparison at `G_d K`. Cancel the adjacent inverse pair,
obtaining the stated counit identity. No geometric identification is used. -/
theorem finiteScalarTower_mates_counit (d : ℕ)
    {C : Fin (d + 1) → Type u} {D : Fin (d + 1) → Type u'}
    [∀ r, Category.{v} (C r)] [∀ r, Category.{v'} (D r)]
    (L : ∀ r : Fin d, C r.succ ⥤ C r.castSucc)
    (W : ∀ r : Fin d, C r.castSucc ⥤ C r.succ)
    (L' : ∀ r : Fin d, D r.succ ⥤ D r.castSucc)
    (W' : ∀ r : Fin d, D r.castSucc ⥤ D r.succ)
    (adj : ∀ r, L r ⊣ W r) (adj' : ∀ r, L' r ⊣ W' r)
    (T : ∀ r, C r ⥤ D r)
    (b : ∀ r, L r ⋙ T r.castSucc ≅ T r.succ ⋙ L' r)
    (a : ∀ r, W r ⋙ T r.succ ≅ T r.castSucc ⋙ W' r)
    (mates : ∀ r, (mateEquiv (adj r) (adj' r) (b r).inv).natTrans = (a r).hom) :
    (mateEquiv (finiteScalarAdjunction adj (Fin.last d))
      (finiteScalarAdjunction adj' (Fin.last d))
      (finiteScalarLeftComparison L L' T b (Fin.last d)).inv).natTrans =
        (finiteScalarRightComparison W W' T a (Fin.last d)).hom ∧
    ∀ K : C 0,
      (finiteScalarLeftComparison L L' T b (Fin.last d)).hom.app
          ((finiteScalarRight W (Fin.last d)).obj K) ≫
        (finiteScalarLeft L' (Fin.last d)).map
          ((finiteScalarRightComparison W W' T a (Fin.last d)).hom.app K) ≫
        (finiteScalarAdjunction adj' (Fin.last d)).counit.app ((T 0).obj K) =
      (T 0).map ((finiteScalarAdjunction adj (Fin.last d)).counit.app K) := by
  have h : ∀ r : Fin (d + 1),
      (mateEquiv (finiteScalarAdjunction adj r) (finiteScalarAdjunction adj' r)
        (finiteScalarLeftComparison L L' T b r).inv).natTrans =
          (finiteScalarRightComparison W W' T a r).hom := by
    refine Fin.induction ?_ ?_
    · ext X
      simp [finiteScalarAdjunction, finiteScalarLeftComparison,
        finiteScalarRightComparison, finiteScalarLeft, finiteScalarRight,
        mateEquiv, Adjunction.id]
    · intro r ih
      have hp := mateEquiv_hcomp (adj r) (adj' r)
        (finiteScalarAdjunction adj r.castSucc) (finiteScalarAdjunction adj' r.castSucc)
        (b r).inv (finiteScalarLeftComparison L L' T b r.castSucc).inv
      change (mateEquiv ((adj r).comp (finiteScalarAdjunction adj r.castSucc))
        ((adj' r).comp (finiteScalarAdjunction adj' r.castSucc))
        (finiteScalarLeftComparison L L' T b r.succ).inv).natTrans = _
      have hb : (finiteScalarLeftComparison L L' T b r.succ).inv =
          TwoSquare.vComp (b r).inv
            (finiteScalarLeftComparison L L' T b r.castSucc).inv := by
        ext X
        simp [finiteScalarLeftComparison, TwoSquare.vComp]
      rw [hb, hp]
      change (TwoSquare.hComp
        ((mateEquiv (finiteScalarAdjunction adj r.castSucc)
          (finiteScalarAdjunction adj' r.castSucc)
          (finiteScalarLeftComparison L L' T b r.castSucc).inv).natTrans)
        ((mateEquiv (adj r) (adj' r) (b r).inv).natTrans)).natTrans = _
      rw [ih, mates r]
      rfl
  refine ⟨h (Fin.last d), ?_⟩
  intro K
  have hc := mateEquiv_counit
    (finiteScalarAdjunction adj (Fin.last d))
    (finiteScalarAdjunction adj' (Fin.last d))
    (finiteScalarLeftComparison L L' T b (Fin.last d)).inv K
  change (finiteScalarLeft L' (Fin.last d)).map
      ((mateEquiv (finiteScalarAdjunction adj (Fin.last d))
        (finiteScalarAdjunction adj' (Fin.last d))
        (finiteScalarLeftComparison L L' T b (Fin.last d)).inv).natTrans.app K) ≫
      _ = _ at hc
  rw [h (Fin.last d)] at hc
  rw [hc]
  simp

end CategoryTheory
