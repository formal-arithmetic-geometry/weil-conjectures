module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Order.Defs.PartialOrder

/-!
# Transport of transition associators and units

Source: blueprint, smooth purity, `sk-def-sp-tate-twist-locally-free.proof.md`,
Proof (3), final scalar convention; the general categorical argument extracted in
(blueprint: lem-pur-transition-associator-iso-transport).

The auxiliary expressions and paths make finite-chain coherence, including empty chains,
precise. They are syntax for this statement, rather than additional categorical structure.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.TransitionIsoTransport

variable {I : Type w} [Preorder I] {A : I → Type u} [∀ i, Category.{v} (A i)]

/-- The two-arrow comparison z, with the inner comparison applied first.
Source: blueprint, smooth purity, Proof (3), scalar convention
(blueprint: lem-pur-transition-associator-iso-transport). -/
def comparison
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    B hij ⋙ B hjk ≅ C hij ⋙ C hjk :=
  Functor.isoWhiskerRight (χ hij) (B hjk) ≪≫ Functor.isoWhiskerLeft (C hij) (χ hjk)

/-- The actual transported associator a = chi d z inverse.
Source: blueprint, smooth purity, Proof (3), scalar convention
(blueprint: lem-pur-transition-associator-iso-transport). -/
def associator
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    (d : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), B hij ⋙ B hjk ≅ B (le_trans hij hjk))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    C hij ⋙ C hjk ≅ C (le_trans hij hjk) :=
  (comparison B C χ hij hjk).symm ≪≫ d hij hjk ≪≫ χ (le_trans hij hjk)

/-- The actual transported unit u = lambda chi inverse, without strict identity assumptions.
Source: blueprint, smooth purity, Proof (3), scalar convention
(blueprint: lem-pur-transition-associator-iso-transport). -/
def unitIso
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    (ε : ∀ i : I, B (le_refl i) ≅ 𝟭 (A i)) (i : I) : C (le_refl i) ≅ 𝟭 (A i) :=
  (χ (le_refl i)).symm ≪≫ ε i

/-- The four-index associativity law and both actual unit laws, on components.
Source: blueprint, smooth purity, Proof (3), scalar convention
(blueprint: lem-pur-transition-associator-iso-transport). -/
def Coherent
    (C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (a : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), C hij ⋙ C hjk ≅ C (le_trans hij hjk))
    (u₀ : ∀ i : I, C (le_refl i) ≅ 𝟭 (A i)) : Prop :=
  (∀ {i j k l : I} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (K : A i),
    (C hkl).map ((a hij hjk).hom.app K) ≫ (a (le_trans hij hjk) hkl).hom.app K =
      (a hjk hkl).hom.app ((C hij).obj K) ≫ (a hij (le_trans hjk hkl)).hom.app K) ∧
  (∀ {i j : I} (hij : i ≤ j) (K : A i),
    (a (le_refl i) hij).hom.app K = (C hij).map ((u₀ i).hom.app K)) ∧
  (∀ {i j : I} (hij : i ≤ j) (K : A i),
    (a hij (le_refl j)).hom.app K = (u₀ j).hom.app ((C hij).obj K))

/-- Parenthesized finite chains, with explicit empty chains and single arrows.
Source: blueprint, smooth purity, Proof (3), finite-chain argument, steps 9--10
(blueprint: lem-pur-transition-associator-iso-transport). -/
inductive Word (I : Type w) [Preorder I] : I → I → Type w
  | nil (i : I) : Word I i i
  | edge {i j : I} (hij : i ≤ j) : Word I i j
  | comp {i j k : I} (p : Word I i j) (q : Word I j k) : Word I i k

namespace Word

/-- The endpoint inequality of a finite chain.
Source: blueprint, smooth purity, Proof (3), finite-chain argument
(blueprint: lem-pur-transition-associator-iso-transport). -/
def bounds {i j : I} : Word I i j → PLift (i ≤ j)
  | .nil i => ⟨le_refl i⟩
  | .edge h => ⟨h⟩
  | .comp p q => ⟨le_trans p.bounds.down q.bounds.down⟩

/-- Evaluate a parenthesized chain using the specified transition functors.
Source: blueprint, smooth purity, Proof (3), finite-chain argument
(blueprint: lem-pur-transition-associator-iso-transport). -/
def eval (C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    {i j : I} : Word I i j → (A i ⥤ A j)
  | .nil i => 𝟭 (A i)
  | .edge h => C h
  | .comp p q => eval C p ⋙ eval C q

/-- The canonical reduction of a parenthesized chain to its endpoint transition.
The empty chain reduces by the inverse of the actual unit; a single arrow by identity.
Source: blueprint, smooth purity, Proof (3), finite-chain argument, steps 9--10
(blueprint: lem-pur-transition-associator-iso-transport). -/
def reduction
    (C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (a : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), C hij ⋙ C hjk ≅ C (le_trans hij hjk))
    (u₀ : ∀ i : I, C (le_refl i) ≅ 𝟭 (A i))
    {i j : I} (p : Word I i j) : eval C p ≅ C p.bounds.down :=
  match p with
  | .nil i => (u₀ i).symm
  | .edge h => Iso.refl (C h)
  | .comp p q =>
    Functor.isoWhiskerRight (reduction C a u₀ p) (eval C q) ≪≫
      Functor.isoWhiskerLeft (C p.bounds.down) (reduction C a u₀ q) ≪≫ a p.bounds.down q.bounds.down

end Word

/-- Finite paths of reassociations, contractions, unit insertions/deletions and their
inverses, also inside subexpressions.
Source: blueprint, smooth purity, Proof (3), finite-chain argument, steps 9--10
(blueprint: lem-pur-transition-associator-iso-transport). -/
inductive Path (I : Type w) [Preorder I] : ∀ {i j : I}, Word I i j → Word I i j → Type w
  | refl {i j : I} (p : Word I i j) : Path I p p
  | trans {i j : I} {p q r : Word I i j} (e : Path I p q) (f : Path I q r) : Path I p r
  | symm {i j : I} {p q : Word I i j} (e : Path I p q) : Path I q p
  | whisker {i j k : I} {p p' : Word I i j} {q q' : Word I j k}
      (e : Path I p p') (f : Path I q q') : Path I (.comp p q) (.comp p' q')
  | contract {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
      Path I (.comp (.edge hij) (.edge hjk)) (.edge (le_trans hij hjk))
  | unit (i : I) : Path I (.edge (le_refl i)) (.nil i)
  | reassoc {i j k l : I} (p : Word I i j) (q : Word I j k) (r : Word I k l) :
      Path I (.comp (.comp p q) r) (.comp p (.comp q r))
  | leftUnit {i j : I} (p : Word I i j) : Path I (.comp (.nil i) p) p
  | rightUnit {i j : I} (p : Word I i j) : Path I (.comp p (.nil j)) p

/-- Evaluate a path by the actual constraints, canonical functor reassociations and unitors.
Source: blueprint, smooth purity, Proof (3), finite-chain argument, steps 9--10
(blueprint: lem-pur-transition-associator-iso-transport). -/
def Path.eval
    (C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (a : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), C hij ⋙ C hjk ≅ C (le_trans hij hjk))
    (u₀ : ∀ i : I, C (le_refl i) ≅ 𝟭 (A i))
    {i j : I} {p q : Word I i j} (e : Path I p q) : Word.eval C p ≅ Word.eval C q :=
  match e with
  | .refl _ => Iso.refl _
  | .trans e f => e.eval C a u₀ ≪≫ f.eval C a u₀
  | .symm e => (e.eval C a u₀).symm
  | .whisker (q := q) (p' := p') e f =>
    Functor.isoWhiskerRight (e.eval C a u₀) (Word.eval C q) ≪≫
      Functor.isoWhiskerLeft (Word.eval C p') (f.eval C a u₀)
  | .contract hij hjk => a hij hjk
  | .unit i => u₀ i
  | .reassoc p q r => Functor.associator (Word.eval C p) (Word.eval C q) (Word.eval C r)
  | .leftUnit p => Functor.leftUnitor (Word.eval C p)
  | .rightUnit p => Functor.rightUnitor (Word.eval C p)

/-- Finite-chain coherence says that each path is the source reduction followed by
inverse target reduction. Thus any two paths with the same endpoints agree, including
paths involving empty chains and repeated indices.
Source: blueprint, smooth purity, Proof (3), finite-chain argument, steps 9--10
(blueprint: lem-pur-transition-associator-iso-transport). -/
def FiniteCoherent
    (C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (a : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), C hij ⋙ C hjk ≅ C (le_trans hij hjk))
    (u₀ : ∀ i : I, C (le_refl i) ≅ 𝟭 (A i)) : Prop :=
  ∀ {i j : I} (p q : Word I i j) (e : Path I p q),
    e.eval C a u₀ = Word.reduction C a u₀ p ≪≫ (Word.reduction C a u₀ q).symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem comparison_associator
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    (d : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), B hij ⋙ B hjk ≅ B (le_trans hij hjk))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (K : A i) :
    (comparison B C χ hij hjk).hom.app K ≫
        (associator B C χ d hij hjk).hom.app K =
      (d hij hjk).hom.app K ≫ (χ (le_trans hij hjk)).hom.app K := by
  simp [associator]

private theorem transport_coherent
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    (d : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), B hij ⋙ B hjk ≅ B (le_trans hij hjk))
    (ε : ∀ i : I, B (le_refl i) ≅ 𝟭 (A i))
    (hB : Coherent B d ε) :
    Coherent C (associator B C χ d) (unitIso B C χ ε) := by
  rcases hB with ⟨hassoc, hleft, hright⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l hij hjk hkl K
    let a : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
        C hij ⋙ C hjk ≅ C (le_trans hij hjk) := associator B C χ d
    let z : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
        B hij ⋙ B hjk ≅ C hij ⋙ C hjk := comparison B C χ
    let T := (B hkl).map ((z hij hjk).hom.app K) ≫
      (χ hkl).hom.app ((C hjk).obj ((C hij).obj K))
    have : IsIso T := by dsimp [T]; infer_instance
    apply (cancel_epi T).mp
    have hl : T ≫ (C hkl).map ((a hij hjk).hom.app K) ≫
        (a (le_trans hij hjk) hkl).hom.app K =
        (B hkl).map ((d hij hjk).hom.app K) ≫
          (d (le_trans hij hjk) hkl).hom.app K ≫
          (χ (le_trans (le_trans hij hjk) hkl)).hom.app K := by
      dsimp [T]
      simp only [Category.assoc]
      rw [← (χ hkl).hom.naturality_assoc, ← Functor.map_comp_assoc,
        comparison_associator]
      simp only [Functor.map_comp, Category.assoc]
      have hz := comparison_associator B C χ d (le_trans hij hjk) hkl K
      dsimp [comparison] at hz
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Category.assoc] using congrArg
          ((B hkl).map ((d hij hjk).hom.app K) ≫ ·) hz
    have hr : T ≫ (a hjk hkl).hom.app ((C hij).obj K) ≫
        (a hij (le_trans hjk hkl)).hom.app K =
        (d hjk hkl).hom.app ((B hij).obj K) ≫
          (d hij (le_trans hjk hkl)).hom.app K ≫
          (χ (le_trans hij (le_trans hjk hkl))).hom.app K := by
      have hz := congrArg
        (· ≫ (a hij (le_trans hjk hkl)).hom.app K)
        (comparison_associator B C χ d hjk hkl ((C hij).obj K))
      dsimp [comparison] at hz
      simp only [Category.assoc] at hz
      dsimp [T, z, comparison]
      simp only [Functor.map_comp, Category.assoc]
      rw [hz]
      have hn := (d hjk hkl).hom.naturality ((χ hij).hom.app K)
      simp only [Functor.comp_map] at hn
      rw [← Category.assoc ((B hkl).map ((B hjk).map ((χ hij).hom.app K))), hn]
      simp only [Category.assoc]
      have hz := comparison_associator B C χ d hij (le_trans hjk hkl) K
      dsimp [comparison] at hz
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Category.assoc] using congrArg
          ((d hjk hkl).hom.app ((B hij).obj K) ≫ ·) hz
    have hd := congrArg (· ≫ (χ (le_trans hij (le_trans hjk hkl))).hom.app K)
      (hassoc hij hjk hkl K)
    simp only [Category.assoc] at hd
    simpa only [Category.assoc] using hl.trans (hd.trans hr.symm)
  · intro i j hij K
    apply (cancel_epi ((comparison B C χ (le_refl i) hij).hom.app K)).mp
    rw [comparison_associator, hleft]
    dsimp [comparison, unitIso]
    simp only [Category.assoc]
    rw [← (χ hij).hom.naturality]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  · intro i j hij K
    apply (cancel_epi ((comparison B C χ hij (le_refl j)).hom.app K)).mp
    rw [comparison_associator, hright]
    dsimp [comparison, unitIso]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    exact (ε j).hom.naturality ((χ hij).hom.app K) |>.symm

private theorem path_reduction
    (C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (a : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), C hij ⋙ C hjk ≅ C (le_trans hij hjk))
    (u₀ : ∀ i : I, C (le_refl i) ≅ 𝟭 (A i))
    (h : Coherent C a u₀)
    {i j : I} {p q : Word I i j} (e : Path I p q) (K : A i) :
    (e.eval C a u₀).hom.app K ≫ (Word.reduction C a u₀ q).hom.app K =
      (Word.reduction C a u₀ p).hom.app K := by
  induction e with
  | refl p => simp [Path.eval]
  | trans e f he hf =>
    simpa only [Path.eval, Iso.trans_hom, NatTrans.comp_app, Category.assoc, hf] using he K
  | symm e he =>
    dsimp [Path.eval]
    rw [← he]
    simp
  | whisker e f he hf =>
    dsimp [Path.eval, Word.reduction, Word.eval]
    simp only [Category.assoc]
    rw [← (f.eval C a u₀).hom.naturality_assoc]
    simp only [← Functor.map_comp_assoc, he]
    simp only [← Category.assoc, hf]
  | contract hij hjk => simp [Path.eval, Word.reduction, Word.eval]
  | unit i => simp [Path.eval, Word.reduction, Word.eval]
  | reassoc p q r =>
    dsimp [Path.eval, Word.reduction, Word.eval]
    simp only [Category.id_comp, Functor.map_comp, Category.assoc]
    rw [(Word.reduction C a u₀ r).hom.naturality_assoc]
    rw [← h.1]
    rw [← (Word.reduction C a u₀ r).hom.naturality_assoc,
      ← (Word.reduction C a u₀ r).hom.naturality_assoc]
  | leftUnit p =>
    dsimp [Path.eval, Word.reduction, Word.eval]
    simp only [Category.id_comp, h.2.1]
    rw [← Category.assoc, (Word.reduction C a u₀ p).hom.naturality]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp only [Functor.id_obj, Functor.map_id, Category.comp_id]
  | rightUnit p =>
    dsimp [Path.eval, Word.reduction, Word.eval]
    simp only [Category.id_comp, h.2.2, Iso.inv_hom_id_app]
    simp only [Functor.id_obj, Category.comp_id]

private theorem finite_coherent
    (C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (a : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), C hij ⋙ C hjk ≅ C (le_trans hij hjk))
    (u₀ : ∀ i : I, C (le_refl i) ≅ 𝟭 (A i))
    (h : Coherent C a u₀) : FiniteCoherent C a u₀ := by
  intro i j p q e
  apply Iso.ext
  ext K
  apply (cancel_mono ((Word.reduction C a u₀ q).hom.app K)).mp
  simpa using path_reduction C a u₀ h e K

omit [Preorder I] in
private theorem normalized_unit {i : I} (F G : A i ⥤ A i)
    (u₀ : F ≅ 𝟭 (A i)) (ρ : F ≅ G)
    (hG : G = 𝟭 (A i)) (hρ : HEq ρ u₀) :
    HEq (ρ.symm ≪≫ u₀) (Iso.refl (𝟭 (A i))) := by
  subst G
  rw [eq_of_heq hρ]
  exact heq_of_eq (Iso.symm_self_id u₀)

omit [Preorder I] in
private theorem normalized_left {i j : I}
    (F : A i ⥤ A i) (G : A i ⥤ A j) (α : F ⋙ G ≅ G) (v₀ : F ≅ 𝟭 (A i))
    (hF : F = 𝟭 (A i)) (hv : HEq v₀ (Iso.refl (𝟭 (A i))))
    (hα : ∀ K, α.hom.app K = G.map (v₀.hom.app K)) :
    HEq α (Functor.leftUnitor G) := by
  subst F
  have hv' : v₀ = Iso.refl _ := eq_of_heq hv
  subst v₀
  apply heq_of_eq
  apply Iso.ext
  ext K
  simpa using hα K

omit [Preorder I] in
private theorem normalized_right {i j : I}
    (F : A j ⥤ A j) (G : A i ⥤ A j) (α : G ⋙ F ≅ G) (v₀ : F ≅ 𝟭 (A j))
    (hF : F = 𝟭 (A j)) (hv : HEq v₀ (Iso.refl (𝟭 (A j))))
    (hα : ∀ K, α.hom.app K = v₀.hom.app (G.obj K)) :
    HEq α (Functor.rightUnitor G) := by
  subst F
  have hv' : v₀ = Iso.refl _ := eq_of_heq hv
  subst v₀
  apply heq_of_eq
  apply Iso.ext
  ext K
  simpa using hα K

/-- Transport the coherent associators and actual units along the specified chi.
The conclusion retains the comparison equations, arbitrary finite-chain coherence,
and normalization using these same units. In the normalization, `HEq` only accounts for
replacing self-transition functors by equal identity functors; its maps are canonical unitors.

Source: blueprint, smooth purity, `sk-def-sp-tate-twist-locally-free.proof.md`,
Proof (3), final scalar convention (blueprint: lem-pur-transition-associator-iso-transport).

Proof plan (the node's ten elementary steps):
1. Functors preserve inverses. Naturality is stable under inverses and composition.
2. Apply naturality of chi twice to z. Its inverse is B(chi inverse) chi inverse.
3. Compose these natural isomorphisms to obtain a and u, and cancel inverses to get
   a z = chi d and u chi = lambda.
4. For a three-arrow chain precompose both associativity paths by the invertible
   T = chi_lk B_lk(chi_kj) B_lk B_kj(chi_ji).
5. Naturality of chi_lk changes the left path into chi_li d_lki B_lk(d_kji).
6. Naturality of d_lkj changes the right path into chi_li d_lji d_lkj.
   The assumed associativity of d identifies them; cancel T.
7. Naturality of chi_ji at u_i and the source-unit law give a_jii = C_ji(u_i).
8. Naturality of lambda_j at chi_ji and the target-unit law give a_jji = u_j C_ji.
   Both calculations include the fully repeated case.
9. Define the left-comb reduction R recursively. Induction on the length above a
   split gives R_st = a_srt (R_sr * R_rt), using naturality and step 6.
   Structural induction on parenthesizations gives the same reduction for each tree;
   equivalently, each elementary path commutes with Word.reduction. Induct on Path
   to get FiniteCoherent, using inverse cancellation for reversed paths.
10. Put N_ii = identity and N_ji = C_ji otherwise, rho_ii = u_i and rho_ji = identity
    otherwise. Transport a and u once more along rho by steps 1--8. The new unit is
    u_i u_i inverse = identity, so both repeated-index associators are canonical
    identity unitors. Delete identity arrows and use step 9. Empty and single-arrow
    chains have their specified identity reductions. Transport back along rho.
-/
theorem transport
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    (d : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), B hij ⋙ B hjk ≅ B (le_trans hij hjk))
    (ε : ∀ i : I, B (le_refl i) ≅ 𝟭 (A i))
    (hB : Coherent B d ε) :
    Coherent C (associator B C χ d) (unitIso B C χ ε) ∧
    (∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (K : A i),
      (comparison B C χ hij hjk).hom.app K ≫
          (associator B C χ d hij hjk).hom.app K =
        (d hij hjk).hom.app K ≫ (χ (le_trans hij hjk)).hom.app K) ∧
    (∀ (i : I) (K : A i),
      (χ (le_refl i)).hom.app K ≫ (unitIso B C χ ε i).hom.app K = (ε i).hom.app K) ∧
    FiniteCoherent C (associator B C χ d) (unitIso B C χ ε) ∧
    ∃ (N : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
      (ρ : ∀ {i j : I} (h : i ≤ j), C h ≅ N h),
      (∀ i : I, N (le_refl i) = 𝟭 (A i)) ∧
      (∀ {i j : I} (hij : i ≤ j), i ≠ j → N hij = C hij) ∧
      (∀ i : I, HEq (ρ (le_refl i)) (unitIso B C χ ε i)) ∧
      (∀ {i j : I} (hij : i ≤ j), i ≠ j → HEq (ρ hij) (Iso.refl (C hij))) ∧
      Coherent N (associator C N ρ (associator B C χ d))
        (unitIso C N ρ (unitIso B C χ ε)) ∧
      FiniteCoherent N (associator C N ρ (associator B C χ d))
        (unitIso C N ρ (unitIso B C χ ε)) ∧
      (∀ i : I, HEq (unitIso C N ρ (unitIso B C χ ε) i) (Iso.refl (𝟭 (A i)))) ∧
      (∀ {i j : I} (hij : i ≤ j),
        HEq (associator C N ρ (associator B C χ d) (le_refl i) hij)
          (Functor.leftUnitor (N hij))) ∧
      (∀ {i j : I} (hij : i ≤ j),
        HEq (associator C N ρ (associator B C χ d) hij (le_refl j))
          (Functor.rightUnitor (N hij))) := by
  classical
  have hC := transport_coherent B C χ d ε hB
  refine ⟨hC, comparison_associator B C χ d, ?_,
    finite_coherent C _ _ hC, ?_⟩
  · intro i K
    simp [unitIso]
  · let u₀ := unitIso B C χ ε
    let S : ∀ {i j : I} (hij : i ≤ j), Σ F : A i ⥤ A j, C hij ≅ F :=
      fun {i j} hij ↦ if e : i = j then by
        subst j
        exact ⟨𝟭 (A i), u₀ i⟩
      else ⟨C hij, Iso.refl _⟩
    let N : ∀ {i j : I}, i ≤ j → (A i ⥤ A j) := fun hij ↦ (S hij).1
    let ρ : ∀ {i j : I} (hij : i ≤ j), C hij ≅ N hij := fun hij ↦ (S hij).2
    have hN (i : I) : N (le_refl i) = 𝟭 (A i) := by simp [N, S]
    have hS (i : I) : S (le_refl i) = ⟨𝟭 (A i), u₀ i⟩ := by
      simp only [S, dif_pos rfl]
    have hρ (i : I) : HEq (ρ (le_refl i)) (u₀ i) := by
      dsimp only [ρ]
      exact congr_arg_heq Sigma.snd (hS i)
    have hv (i : I) : HEq (unitIso C N ρ u₀ i) (Iso.refl (𝟭 (A i))) := by
      exact normalized_unit (C (le_refl i)) (N (le_refl i)) (u₀ i)
        (ρ (le_refl i)) (hN i) (hρ i)
    have hcoh := transport_coherent C N ρ _ u₀ hC
    refine ⟨N, ρ, hN, ?_, hρ, ?_, hcoh, finite_coherent N _ _ hcoh, hv, ?_, ?_⟩
    · intro i j hij hne
      simp [N, S, hne]
    · intro i j hij hne
      have hh : S hij = ⟨C hij, Iso.refl _⟩ := by simp only [S, dif_neg hne]
      dsimp only [ρ]
      exact congr_arg_heq Sigma.snd hh
    · intro i j hij
      exact normalized_left (N (le_refl i)) (N hij) _ _ (hN i) (hv i)
        (hcoh.2.1 hij)
    · intro i j hij
      exact normalized_right (N (le_refl j)) (N hij) _ _ (hN j) (hv j)
        (hcoh.2.2 hij)

end CategoryTheory.TransitionIsoTransport
