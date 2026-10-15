/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.EssentiallyConstantSystem
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Mittag-Leffler systems in a short exact sequence

Source: Stacks Project, Homology, Lemma 12.31.6, Tag 070D
(blueprint: lem-weil-pbc-exact-sequence-ml).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.ShortComplex

/-- In a termwise short exact sequence of inverse systems of abelian groups, an essentially
constant quotient makes the kernel Mittag-Leffler exactly when the middle system is
Mittag-Leffler (Stacks Project, Homology, Lemma 12.31.6, Tag 070D).
The index `n : ℕ` denotes the positive index `n + 1`; composing with `forget AddCommGrpCat`
expresses ML by the existing underlying-set definition, equivalently stabilization of images
as subgroups.

Proof (following the nine steps of the node):
1. By injectivity of the first map, identify each A_i with the kernel inside B_i. Naturality
identifies its transitions with restrictions of those of B. Dropping finitely many indices
preserves ML: witnesses on the tail work there, and for an earlier i use the witness at the
first retained index N and factor all transitions through N.
2. Apply `lem-weil-pbc-essentially-constant-splitting` to the cone and retraction provided by
`def-weil-pbc-essentially-constant-system`. After dropping a finite initial segment,
C_j = π_j(X) ⊕ Z_j, with compatible projections p_j to X and transitions on Z_j that are
zero eventually into each fixed term. The projection q_j(c) = c - π_j(p_j(c)) onto Z_j
is surjective, has kernel π_j(X), and commutes with transitions.
3. For an essentially zero quotient Z', choose m* ≥ m whose transition into Z'_m is zero.
Then B'_{m*} maps into A'_m. For k ≥ m* and i ≤ m this gives, inside B'_i,
Im(A'_k → A'_i) ⊆ Im(B'_k → B'_i) ⊆ Im(A'_m → A'_i).
4. If A' is ML at i with witness c, choose c* as in step 3. For k ≥ c*, both outer
images in the inclusion chain equal Im(A'_c → A'_i), so the middle images stabilize.
Conversely, if B' is ML with witness c, for k ≥ c use step 3 with m = k and k* ≥ k.
The two B' images surrounding the A'_k image equal the stabilized B' image. Thus A' is ML.
5. Put B'_i = v_i⁻¹(π_i(X)). Naturality makes these subgroups a tower. The composite
q_i v_i is surjective with kernel B'_i and gives an exact sequence B' → B → Z.
Steps 3 and 4 imply that B' is ML exactly when B is ML.
6. Restrict p_i v_i to B'_i to obtain s_i : B'_i → X. Its kernel is A_i, since
π_i(X) ∩ Z_i = 0; it is surjective by lifting π_i(x) along v_i. These maps commute
with transitions into the constant system X, giving 0 → A_i → B'_i → X → 0.
7. Write I_{k,i} and J_{k,i} for the transition images of A and B'. For k ≥ i,
s_i(J_{k,i}) = X since s_i b_{k,i} = s_k is surjective. Also J_{k,i} ∩ A_i = I_{k,i}:
a lift b of an element in that intersection satisfies s_k(b) = 0, hence lies in A_k.
Thus 0 → I_{k,i} → J_{k,i} → X → 0 is exact.
8. If I stabilizes at c, take y ∈ J_{c,i} and k ≥ c. Surjectivity in step 7 gives
y' ∈ J_{k,i} with s_i(y') = s_i(y). Then y - y' lies in I_{c,i} = I_{k,i}, hence
in J_{k,i}, so J stabilizes. Conversely, if J stabilizes, intersect with A_i and use
step 7 to see that I stabilizes.
9. Combining tail invariance, step 8, step 5, and tail invariance again gives the stated
ML equivalence for A and B. ML throughout is `def-weil-pbc-mittag-leffler-system`.
(blueprint: lem-weil-pbc-exact-sequence-ml) -/
theorem isMittagLeffler_iff_of_isEssentiallyConstant
    (S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hS : ∀ n : ℕᵒᵖ, (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact)
    (hC : S.X₃.IsEssentiallyConstant) :
    (S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler ↔
      (S.X₂ ⋙ forget AddCommGrpCat).IsMittagLeffler := by
  classical
  -- Work with the factorization through the constant summand directly, rather than
  -- constructing the auxiliary subgroup towers in the nine-step proof plan.
  obtain ⟨X, π, hπ, i₀, r, hr, hfactor⟩ := hC
  have htrans (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) {i j k : ℕ}
      (hij : i ≤ j) (hjk : j ≤ k) :
      F.map (homOfLE (hij.trans hjk)).op =
        F.map (homOfLE hjk).op ≫ F.map (homOfLE hij).op := by
    rw [← F.map_comp]
    congr 1
  have hcone {j k : ℕ} (hjk : j ≤ k) :
      π k ≫ S.X₃.map (homOfLE hjk).op = π j := by
    induction k, hjk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [htrans S.X₃ hk (Nat.le_succ k), ← Category.assoc, hπ, ih]
  have hnat {F G : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (η : F ⟶ G)
      {i j : ℕᵒᵖ} (f : i ⟶ j) (x : F.obj i) :
      η.app j (F.map f x) = G.map f (η.app i x) :=
    ConcreteCategory.congr_hom (η.naturality f) x
  have hcomp (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) {i j k : ℕᵒᵖ}
      (f : i ⟶ j) (g : j ⟶ k) (x : F.obj i) :
      F.map (f ≫ g) x = F.map g (F.map f x) :=
    ConcreteCategory.congr_hom (F.map_comp f g) x
  have hsurj (n : ℕᵒᵖ) : Function.Surjective (S.g.app n) :=
    (hS n).ab_surjective_g
  have hzero (n : ℕᵒᵖ) (a : S.X₁.obj n) : S.g.app n (S.f.app n a) = 0 :=
    (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ab_zero_apply a
  have hexact (n : ℕᵒᵖ) (b : S.X₂.obj n) (hb : S.g.app n b = 0) :
      ∃ a : S.X₁.obj n, S.f.app n a = b :=
    ((S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ab_exact_iff.mp (hS n).exact) b hb
  have hfactor' (j : ℕ) : ∃ c : ℕ, ∃ (hic : i₀ ≤ c) (hjc : j ≤ c),
      ∀ (k : ℕ) (hck : c ≤ k),
        S.X₃.map (homOfLE (hjc.trans hck)).op =
          S.X₃.map (homOfLE (hic.trans hck)).op ≫ r ≫ π j := by
    obtain ⟨c, hic, hjc, hc⟩ := hfactor j
    refine ⟨c, hic, hjc, fun k hck ↦ ?_⟩
    rw [htrans S.X₃ hjc hck, hc, htrans S.X₃ hic hck]
    simp only [Category.assoc]
  have hπinj (m : ℕ) (hm : i₀ ≤ m) : Function.Injective (π m) := by
    have hret : π m ≫ S.X₃.map (homOfLE hm).op ≫ r = 𝟙 X := by
      rw [← Category.assoc, hcone hm, hr]
    have hleft (x : X) : r (S.X₃.map (homOfLE hm).op (π m x)) = x :=
      ConcreteCategory.congr_hom hret x
    intro x y hxy
    rw [← hleft x, ← hleft y, hxy]
  constructor
  · intro hA j
    -- Lift the stable quotient part at a common later index; the difference is in A.
    obtain ⟨i, f, hf⟩ := hA j
    obtain ⟨c, hic, hIc, hc⟩ := hfactor' i.unop
    refine ⟨Opposite.op c, (homOfLE hIc).op ≫ f, fun k g ↦ ?_⟩
    rintro _ ⟨b, rfl⟩
    let l := max c k.unop
    have hcl : c ≤ l := Nat.le_max_left _ _
    have hkl : k.unop ≤ l := Nat.le_max_right _ _
    let x : X := r (S.X₃.map (homOfLE hic).op (S.g.app (Opposite.op c) b))
    obtain ⟨d, hd⟩ := hsurj (Opposite.op l) (π l x)
    have hz : S.g.app i
        (S.X₂.map (homOfLE hIc).op b -
          S.X₂.map (homOfLE (hIc.trans hcl)).op d) = 0 := by
      rw [map_sub, hnat, hnat, hd]
      have hb := ConcreteCategory.congr_hom (hc c (le_refl c))
        (S.g.app (Opposite.op c) b)
      have hd' := ConcreteCategory.congr_hom (hcone (hIc.trans hcl)) x
      change S.X₃.map (homOfLE hIc).op (S.g.app (Opposite.op c) b) = π i.unop x at hb
      change S.X₃.map (homOfLE (hIc.trans hcl)).op (π l x) = π i.unop x at hd'
      rw [hb, hd', sub_self]
    obtain ⟨a, ha⟩ := hexact i _ hz
    obtain ⟨a', ha'⟩ := hf g ⟨a, rfl⟩
    refine ⟨S.X₂.map (homOfLE hkl).op d + S.f.app k a', ?_⟩
    change S.X₁.map g a' = S.X₁.map f a at ha'
    change S.X₂.map g (_ + _) = S.X₂.map ((homOfLE hIc).op ≫ f) b
    rw [map_add, ← hnat, ha', hnat, ha, map_sub]
    have hcomm : (homOfLE hkl).op ≫ g = (homOfLE (hIc.trans hcl)).op ≫ f :=
      Subsingleton.elim _ _
    rw [← hcomp, hcomm, hcomp, hcomp]
    abel
  · intro hB j
    -- Test at a split index m. A B-lift has zero stable quotient component there,
    -- hence maps into A at every prescribed index after a further transition.
    let m := max j.unop i₀
    have hjm : j.unop ≤ m := Nat.le_max_left _ _
    have h₀m : i₀ ≤ m := Nat.le_max_right _ _
    obtain ⟨i, f, hf⟩ := hB (Opposite.op m)
    let c := max i.unop m
    have hic : i.unop ≤ c := Nat.le_max_left _ _
    have hmc : m ≤ c := Nat.le_max_right _ _
    refine ⟨Opposite.op c, (homOfLE (hjm.trans hmc)).op, fun k g ↦ ?_⟩
    rintro _ ⟨a, rfl⟩
    obtain ⟨cK, h₀K, hkK, hK⟩ := hfactor' k.unop
    obtain ⟨cM, h₀M, hmM, hM⟩ := hfactor' m
    let l := max (max c cK) cM
    have hKl : cK ≤ l := (Nat.le_max_right c cK).trans (Nat.le_max_left _ _)
    have hMl : cM ≤ l := Nat.le_max_right _ _
    have hkl : k.unop ≤ l := hkK.trans hKl
    have hml : m ≤ l := hmM.trans hMl
    obtain ⟨b, hb⟩ := hf (homOfLE hml).op
      ⟨S.X₂.map (homOfLE hic).op (S.f.app (Opposite.op c) a), rfl⟩
    change S.X₂.map (homOfLE hml).op b =
      S.X₂.map f (S.X₂.map (homOfLE hic).op (S.f.app (Opposite.op c) a)) at hb
    have hcm : (homOfLE hic).op ≫ f = (homOfLE hmc).op := Subsingleton.elim _ _
    rw [← hcomp, hcm, ← hnat] at hb
    have hz : S.X₃.map (homOfLE hml).op (S.g.app (Opposite.op l) b) = 0 := by
      rw [← hnat, hb, hzero]
    let x : X := r (S.X₃.map (homOfLE (h₀M.trans hMl)).op
      (S.g.app (Opposite.op l) b))
    have hx : π m x = 0 := by
      have he := ConcreteCategory.congr_hom (hM l hMl) (S.g.app (Opposite.op l) b)
      change S.X₃.map (homOfLE hml).op (S.g.app (Opposite.op l) b) = π m x at he
      rw [← he, hz]
    have hxzero : x = 0 := hπinj m h₀m (by simpa only [map_zero] using hx)
    have hzk : S.g.app k (S.X₂.map (homOfLE hkl).op b) = 0 := by
      rw [hnat]
      have he := ConcreteCategory.congr_hom (hK l hKl) (S.g.app (Opposite.op l) b)
      change S.X₃.map (homOfLE hkl).op (S.g.app (Opposite.op l) b) = π k.unop x at he
      rw [he, hxzero, map_zero]
    obtain ⟨a', ha'⟩ := hexact k _ hzk
    refine ⟨a', ?_⟩
    change S.X₁.map g a' = S.X₁.map (homOfLE (hjm.trans hmc)).op a
    apply (hS j).ab_injective_f
    change S.f.app j (S.X₁.map g a') =
      S.f.app j (S.X₁.map (homOfLE (hjm.trans hmc)).op a)
    rw [hnat, hnat, ha', ← hcomp]
    have hlm : (homOfLE hkl).op ≫ g = (homOfLE hml).op ≫ (homOfLE hjm).op :=
      Subsingleton.elim _ _
    rw [hlm, hcomp, hb, hnat, ← hcomp]
    congr 1

end CategoryTheory.ShortComplex
