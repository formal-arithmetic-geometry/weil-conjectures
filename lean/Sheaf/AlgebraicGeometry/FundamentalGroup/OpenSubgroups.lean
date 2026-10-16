/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.GroupTheory.Index
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale

/-!
# Open subgroups and connected finite étale covers

Source: blueprint, sec-smooth-purity, sk-prop-a1-kummer,
cor-galois-open-subgroups; Stacks Project, Tags 0BND, 0BNB, 0BN4, 04JJ, 02K9 and 04MH
(blueprint: cor-galois-open-subgroups).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Connected finite étale covers are classified by conjugacy classes of open subgroups;
marked covers are classified by individual open subgroups. The classification is expressed
by realization of every open subgroup and the exact isomorphism criteria, avoiding choices
of representatives. Degree is the index of the marked-point stabilizer.

Source: blueprint cor-galois-open-subgroups, corrected DAG statement; Stacks Project,
Tags 0BND, 0BNB, 0BN4, 04JJ, 02K9 and 04MH (blueprint: cor-galois-open-subgroups).

Proof:
1. By thm-galois-fundamental the fibre functor is an equivalence to finite continuous
   actions. By lem-galois-finite-etale-connected-object and def-galois-connected-object,
   a connected cover has nonempty transitive fibre: each orbit is an invariant subobject.
2. Conversely a transitive nonempty fibre gives a connected nonempty cover. By
   lem-galois-coproduct-copies-morphisms-clopen a clopen partition defines a morphism to
   two copies of the base. Its fibre map is constant by transitivity. Faithfulness and
   the clopen decomposition criterion make the partition trivial (def-weil-connected-scheme).
3. Evaluation is continuous into a discrete finite fibre (def-galois-fibre-functor),
   so the stabilizer H is open. The orbit map identifies G/H with the fibre: equality
   of orbit points is precisely equality of cosets, and transitivity gives surjectivity.
4. Compactness makes G/H finite for every open H. Its discrete transitive action is
   continuous, since the inverse images under orbit maps are translates of H.
   thm-galois-fundamental realizes this action by a connected cover with a marked point.
5. Point-preserving equivariant bijections preserve stabilizers. Equal stabilizers
   identify both pointed fibres with (G/H,H); fullness and faithfulness lift the resulting
   pointed isomorphism. Moving the point by g conjugates its stabilizer by g, giving
   precisely the unpointed isomorphism criterion and independence of the chosen point.
6. By def-weil-etale-morphism and def-pc-finite-locally-free the cover is finite locally
   free. By lem-weil-pbc-finite-locally-free-degree-locally-constant its rank is constant
   on the connected base. Scalar extension preserves dimension and
   lem-galois-geometric-fibre splits the geometric fibre into copies of Spec Ω.
   Hence its cardinality equals the rank, and step 3 identifies it with the index. -/
theorem connected_cover_open_subgroups
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    (∀ (P : Y.FiniteEtale), ConnectedSpace P.obj.left →
      ∀ p : (fiber s).obj P,
        IsOpen (MulAction.stabilizer (Aut (fiber s)) p : Set (Aut (fiber s))) ∧
        P.obj.hom.IsFiniteLocallyFreeOfDegree
          (MulAction.stabilizer (Aut (fiber s)) p).index) ∧
    (∀ H : Subgroup (Aut (fiber s)), IsOpen (H : Set (Aut (fiber s))) →
      ∃ (P : Y.FiniteEtale), ConnectedSpace P.obj.left ∧
        ∃ p : (fiber s).obj P, MulAction.stabilizer (Aut (fiber s)) p = H) ∧
    (∀ (P Q : Y.FiniteEtale), ConnectedSpace P.obj.left → ConnectedSpace Q.obj.left →
      ∀ (p : (fiber s).obj P) (q : (fiber s).obj Q),
        (∃ e : P ≅ Q, (fiber s).map e.hom p = q) ↔
          MulAction.stabilizer (Aut (fiber s)) p = MulAction.stabilizer (Aut (fiber s)) q) ∧
    (∀ (P Q : Y.FiniteEtale), ConnectedSpace P.obj.left → ConnectedSpace Q.obj.left →
      ∀ (p : (fiber s).obj P) (q : (fiber s).obj Q),
        Nonempty (P ≅ Q) ↔ ∃ g : Aut (fiber s),
          ∀ h : Aut (fiber s),
            h ∈ MulAction.stabilizer (Aut (fiber s)) p ↔
              g⁻¹ * h * g ∈ MulAction.stabilizer (Aut (fiber s)) q) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
