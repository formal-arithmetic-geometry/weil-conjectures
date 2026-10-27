module

public import Sheaf.CategoryTheory.Triangulated.PostnikovSystem

/-! # Countable Postnikov extension and comparison

Source: Stacks Project, derived.tex, Tags 0D83, 0D82, 014A, and example-key-postnikov
(blueprint: lem-sfb-countable-postnikov-extension-comparison).

A bound `N = ⊤` gives the countable statement. Finite bounds give the same assertions on
finite initial complexes, without imposing conditions on the unused tail of a chain complex.
The conclusions preserve prescribed finite systems and comparison maps by actual restriction
and equality, including their connecting arrows.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [hC : IsTriangulated C]

include hC

/-- Every finite initial Postnikov system extends to the next term and to the whole
specified segment; at `N = ⊤` this is the countable extension assertion.
Source: Stacks Tags 0D83, 0D81 and example-key-postnikov
(blueprint: lem-sfb-countable-postnikov-extension-comparison).

Proof: First propagate the hypothesis to Hom(X_i[i-j-2],Y_j)=0 by induction on j.
Inverse rotation and Hom exactness (`lem-weil-pbc-hom-into-triangle-exact`) factor any map
into Y_j that is zero in X_j through Y_{j-1}[-1]; shift both arguments and use induction.
At lengths one and two, complete d_1 to a triangle, or lift d_2 by Hom exactness, respectively.
At length n at least three the obstruction b_{n-1} d_n factors through Y_{n-3}[-1].
The propagated vanishing with i=n and j=n-3 kills that factor. Hom exactness then lifts d_n
to b_n, and TR1 and TR2 complete it to the required distinguished triangle. None of the
previous objects or arrows changes. Start with Y_0=X_0 and a_0=1 for existence. Recursive
choice of these one-term extensions gives the countable system, starting with any prescribed
finite segment. Its connecting sequence uses the actual arrows c_{r+1}[r]. For finite N
stop the same recursion, equivalently append zero terms and restrict again. -/
theorem exists_postnikovSystem_extension (K : ChainComplex C ℕ) (N : WithTop ℕ)
    (hvan : ∀ (i j : ℕ), (i : WithTop ℕ) ≤ N → j + 2 < i →
      Subsingleton ((K.X i)⟦((i : ℤ) - (j : ℤ) - 2)⟧ ⟶ K.X j)) :
    Nonempty (PostnikovSystem K N) ∧
      (∀ (n : ℕ) (hn : ((n + 1 : ℕ) : WithTop ℕ) ≤ N)
        (P : PostnikovSystem K (n : WithTop ℕ)),
        ∃ Q : PostnikovSystem K ((n + 1 : ℕ) : WithTop ℕ),
          Q.restrict (by exact_mod_cast Nat.le_succ n) = P) ∧
      (∀ (n : ℕ) (hn : (n : WithTop ℕ) ≤ N)
        (P : PostnikovSystem K (n : WithTop ℕ)),
        ∃ Q : PostnikovSystem K N, Q.restrict hn = P) := by
  sorry

/-- A prescribed finite comparison extends by one term. The bound may be finite or
countable, and the target Postnikov systems are fixed throughout.
Source: Stacks Tag 0D82
(blueprint: lem-sfb-countable-postnikov-extension-comparison).

Proof: Propagate Hom(X_i[i-j-1],X'_j)=0 to Hom(X_i[i-j-1],Y'_j)=0 by the same
inverse-rotation and Hom-exactness induction as for existence, now with shift parameter one.
For extension to degree n+1 form the difference g_n b_{n+1} - b'_{n+1} u_{n+1}.
For n=0 it vanishes by the chain-map equation and the normalized degree-zero component.
For n at least one its composite into X'_n vanishes by the chain-map equation and the
already prescribed first square. Hom exactness factors it through Y'_{n-1}[-1].
After shifting, the propagated vanishing for i=n+1 and j=n-1 makes this factor zero.
The second square therefore commutes. Apply `lem-weil-pbc-tr3-second-square` to obtain
g_{n+1} satisfying the first and third squares, keeping every earlier component. -/
theorem exists_postnikovSystem_comparison_step {K L : ChainComplex C ℕ} (u : K ⟶ L)
    (N : WithTop ℕ) (P : PostnikovSystem K N) (Q : PostnikovSystem L N)
    (hvan : ∀ (i j : ℕ), (i : WithTop ℕ) ≤ N → j + 1 < i →
      Subsingleton ((K.X i)⟦((i : ℤ) - (j : ℤ) - 1)⟧ ⟶ L.X j))
    (n : ℕ) (hn : ((n + 1 : ℕ) : WithTop ℕ) ≤ N)
    (g : PostnikovSystem.Hom u
      (P.restrict (le_trans (by exact_mod_cast Nat.le_succ n) hn))
      (Q.restrict (le_trans (by exact_mod_cast Nat.le_succ n) hn))) :
    ∃ G : PostnikovSystem.Hom u (P.restrict hn) (Q.restrict hn),
      G.restrict (M := (n : WithTop ℕ)) (by exact_mod_cast Nat.le_succ n) = g := by
  sorry

/-- There is a comparison of the full specified systems, extending any prescribed finite
comparison. If the chain-map components are isomorphisms, its vertex maps are isomorphisms.
Source: Stacks Tags 0D82 and 014A, and countable recursive assembly
(blueprint: lem-sfb-countable-postnikov-extension-comparison).

Proof: Start with g_0=u_0, using the degree-zero transports, or with the given finite
comparison. Repeatedly apply the one-term comparison extension of Tag 0D82: propagate
shifted Hom vanishing to Y'_j by Hom exactness, kill the difference of the second square
through Y'_{n-2}[-1], and apply TR3 in its second-square form to complete the other squares.
Recursion fixes each component when its index is first reached; hence restriction retains
the prescribed comparison exactly. If all u_i are isomorphisms, g_0 is one. Inductively
`lem-sf-triangle-morphism-iso` applied to (g_n,u_n,g_{n-1}) implies g_n is one as well.
This also proves that a prescribed finite comparison is already componentwise invertible.
For finite N stop the recursion; equivalently append zeros, extend the chain map by the
isomorphisms of zero objects, and restrict the countable comparison to the original segment.
All three triangle squares, including the square of connecting arrows, hold at each step. -/
theorem exists_postnikovSystem_comparison {K L : ChainComplex C ℕ} (u : K ⟶ L)
    (N : WithTop ℕ) (P : PostnikovSystem K N) (Q : PostnikovSystem L N)
    (hvan : ∀ (i j : ℕ), (i : WithTop ℕ) ≤ N → j + 1 < i →
      Subsingleton ((K.X i)⟦((i : ℤ) - (j : ℤ) - 1)⟧ ⟶ L.X j)) :
    (∃ G : PostnikovSystem.Hom u P Q,
      (∀ i : ℕ, (i : WithTop ℕ) ≤ N → IsIso (u.f i)) →
        ∀ (r : ℕ) (hr : (r : WithTop ℕ) ≤ N), IsIso (G.app r hr)) ∧
    (∀ (n : ℕ) (hn : (n : WithTop ℕ) ≤ N)
      (g : PostnikovSystem.Hom u (P.restrict hn) (Q.restrict hn)),
      ∃ G : PostnikovSystem.Hom u P Q, G.restrict hn = g ∧
        ((∀ i : ℕ, (i : WithTop ℕ) ≤ N → IsIso (u.f i)) →
          ∀ (r : ℕ) (hr : (r : WithTop ℕ) ≤ N), IsIso (G.app r hr))) := by
  sorry

end CategoryTheory.Triangulated
