module

public import Sheaf.CategoryTheory.TransitionAssociatorIsoTransport
public import Mathlib.Data.Int.Basic

/-!
# Transport of transition twist and inverse evaluation comparisons

Source: blueprint, smooth purity, `sk-def-sp-tate-twist-locally-free.proof.md`,
Proof (3), inverse tensor pair and final coefficient convention. This is the categorical
cancellation argument extracted in (blueprint: lem-pur-transition-twist-evaluation-iso-transport).

`twistIso` constructs the specified comparison. `transportTwistEvaluation` states its tower,
inverse evaluation and actual unit equations. `twistIso_normalization` states the general
normalization clause on a common category, keeping the two twist functors distinct.
-/

@[expose] public section

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory.TransitionIsoTransport

/-- Conjugate the ordinary comparison by the specified transition isomorphism.
Its component is chi inverse at P(K), then b at K, then Q(chi at K).
Source: blueprint, smooth purity, Proof (3), inverse tensor pair, component construction
(blueprint: lem-pur-transition-twist-evaluation-iso-transport). -/
def twistIso
    {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    (F G : D ⥤ E) (χ : F ≅ G) (P : D ⥤ D) (Q : E ⥤ E)
    (b : P ⋙ F ≅ F ⋙ Q) : P ⋙ G ≅ G ⋙ Q :=
  Functor.isoWhiskerLeft P χ.symm ≪≫ b ≪≫ Functor.isoWhiskerRight χ Q

variable {I : Type w} [Preorder I] {A : I → Type u} [∀ i, Category.{v} (A i)]

-- Keep the original named integer binder and coherence hypothesis in the interface.
set_option linter.unusedVariables false in
/-- The transported twist comparisons satisfy the tower, inverse evaluation and unit equations.
Both the input and output use the actual associators and units of the dependency module.

Source: blueprint, smooth purity, `sk-def-sp-tate-twist-locally-free.proof.md`,
Proof (3), inverse tensor pair and final coefficient convention
(blueprint: lem-pur-transition-twist-evaluation-iso-transport).

Proof plan (node steps 1--6 and 8):
1. Apply `transport` to B, C, chi, d and lambda. It gives a z = chi d and u chi = lambda
   for `associator` and `unitIso`, as well as their coherence.
2. The three factors of `twistIso` are natural isomorphisms. Componentwise its inverse
   is chi at P(K), then b inverse, then Q(chi inverse). Naturality follows by applying
   naturality of chi inverse, b and chi, in that order.
3. Write F = B_ji, G = B_kj, x = chi_ji, y = chi_kj, and P, Q, R for the three twists.
   Naturality of y at the transported inner comparison p, then its definition and
   naturality of the outer ordinary comparison c at x, give
   q at C_ji(K) composed with C_kj(p_K) composed with z at P(K)
   = R(z_K) composed with c at F(K) composed with G(b_K).
4. Precompose the desired tower equation by z at P(K). Substitute step 3, then
   a z = chi d, then the ordinary tower equation at K, then the definition of the
   direct transported comparison. Both sides agree; cancel the invertible z at P(K).
5. For evaluation put N = T_i,-m and M = T_j,-m. Expanding the two transported
   comparisons cancels M(chi inverse at P(K)) with M(chi at P(K)). Naturality of
   epsilon_j,m at chi_K moves the remaining M Q(chi_K) past epsilon.
6. The ordinary evaluation hypothesis reduces the result to chi_K F(epsilon_i,m,K)
   chi inverse at N P(K). Naturality of chi at epsilon_i,m,K cancels the last two
   factors and gives C(epsilon_i,m,K). No triangle identity or sign symmetry is used.
8. Apply the general normalization calculation of `twistIso_normalization` with
   F = B_ii, G = C_ii, P = Q = T_i,m and lambda = lambda_i. Its transported unit
   chi inverse followed by lambda is precisely `unitIso B C chi lambda i`.
-/
theorem transportTwistEvaluation
    (B C : ∀ {i j : I}, i ≤ j → (A i ⥤ A j))
    (χ : ∀ {i j : I} (h : i ≤ j), B h ≅ C h)
    (d : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k), B hij ⋙ B hjk ≅ B (le_trans hij hjk))
    (lam : ∀ i : I, B (le_refl i) ≅ 𝟭 (A i))
    (hB : Coherent B d lam)
    (T : ∀ (i : I) (m : ℤ), A i ⥤ A i)
    (ε : ∀ (i : I) (m : ℤ), T i m ⋙ T i (-m) ≅ 𝟭 (A i))
    (b : ∀ {i j : I} (h : i ≤ j) (m : ℤ), T i m ⋙ B h ≅ B h ⋙ T j m)
    (hTower : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (m : ℤ) (K : A i),
      (B hjk).map ((b hij m).hom.app K) ≫ (b hjk m).hom.app ((B hij).obj K) ≫
          (T k m).map ((d hij hjk).hom.app K) =
        (d hij hjk).hom.app ((T i m).obj K) ≫ (b (le_trans hij hjk) m).hom.app K)
    (hEvaluation : ∀ {i j : I} (h : i ≤ j) (m : ℤ) (K : A i),
      (b h (-m)).hom.app ((T i m).obj K) ≫ (T j (-m)).map ((b h m).hom.app K) ≫
          (ε j m).hom.app ((B h).obj K) =
        (B h).map ((ε i m).hom.app K)) :
    (∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (m : ℤ) (K : A i),
      (C hjk).map ((twistIso (B hij) (C hij) (χ hij) (T i m) (T j m) (b hij m)).hom.app K) ≫
          (twistIso (B hjk) (C hjk) (χ hjk) (T j m) (T k m) (b hjk m)).hom.app
            ((C hij).obj K) ≫
          (T k m).map ((associator B C χ d hij hjk).hom.app K) =
        (associator B C χ d hij hjk).hom.app ((T i m).obj K) ≫
          (twistIso (B (le_trans hij hjk)) (C (le_trans hij hjk)) (χ (le_trans hij hjk))
            (T i m) (T k m) (b (le_trans hij hjk) m)).hom.app K) ∧
    (∀ {i j : I} (h : i ≤ j) (m : ℤ) (K : A i),
      (twistIso (B h) (C h) (χ h) (T i (-m)) (T j (-m)) (b h (-m))).hom.app
          ((T i m).obj K) ≫
          (T j (-m)).map ((twistIso (B h) (C h) (χ h) (T i m) (T j m) (b h m)).hom.app K) ≫
          (ε j m).hom.app ((C h).obj K) =
        (C h).map ((ε i m).hom.app K)) ∧
    (∀ (i : I) (m : ℤ) (K : A i),
      (unitIso B C χ lam i).inv.app ((T i m).obj K) ≫
          (twistIso (B (le_refl i)) (C (le_refl i)) (χ (le_refl i))
            (T i m) (T i m) (b (le_refl i) m)).hom.app K ≫
          (T i m).map ((unitIso B C χ lam i).hom.app K) =
        (lam i).inv.app ((T i m).obj K) ≫ (b (le_refl i) m).hom.app K ≫
          (T i m).map ((lam i).hom.app K)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k hij hjk m K
    -- Precompose by the two-arrow comparison and cancel it after the calculation.
    apply (cancel_epi ((comparison B C χ hij hjk).hom.app ((T i m).obj K))).mp
    simp only [twistIso, associator, comparison, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
    rw [(χ hjk).hom.naturality_assoc]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
    simp only [Functor.map_comp, Category.assoc]
    -- Move the transition isomorphism past each ordinary twist comparison.
    have hn₁ := (χ hjk).hom.naturality ((b hij m).hom.app K)
    have hn₂ := NatIso.naturality_2 (χ hjk) ((T j m).map ((χ hij).hom.app K))
    have hn₃ := (b hjk m).hom.naturality ((χ hij).hom.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn₁ hn₂ hn₃
    rw [← reassoc_of% hn₁, reassoc_of% hn₂, reassoc_of% hn₃]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ (T k m).map ((χ (le_trans hij hjk)).hom.app K))
      (hTower hij hjk m K)
  · intro i j h m K
    simp only [twistIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
    simp only [Functor.map_comp, Category.assoc]
    -- Naturality of evaluation moves the remaining transition to the output.
    have hn := (ε j m).hom.naturality ((χ h).hom.app K)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn]
    rw [← Category.assoc ((T j (-m)).map ((b h m).hom.app K)),
      ← Category.assoc ((b h (-m)).hom.app ((T i m).obj K)), hEvaluation]
    exact NatIso.naturality_1 (χ h) ((ε i m).hom.app K)
  · intro i m K
    simp [unitIso, twistIso, Functor.map_comp, Category.assoc,
      ← Functor.map_comp_assoc]

/-- General normalization on a common category, with distinct source and target twists.
Apply this with F = B_ji, G = C_ji, P = T_i,m and Q = T_j,m whenever A_i = A_j;
no equality of indices or of P and Q is required. The second clause retains the identity
case after any specified identification of the two twists.

Source: blueprint, smooth purity, `sk-def-sp-tate-twist-locally-free.proof.md`,
Proof (3), final coefficient convention
(blueprint: lem-pur-transition-twist-evaluation-iso-transport).

Proof plan (node steps 7--8): set v = chi inverse followed by lambda. Its inverse at
P(K) is lambda inverse followed by chi. Expand the definition of `twistIso` between
v inverse at P(K) and Q(v_K). Cancel chi followed by chi inverse at P(K), and cancel
Q(chi_K) followed by Q(chi inverse at K), using the functor laws. What remains is
lambda inverse at P(K), then b_K, then Q(lambda_K), which is the ordinary normalized
comparison. The equality holds as maps P(K) to Q(K), retaining nonidentity comparisons.
Postcompose both sides with the inverse of any specified identification P iso Q;
if the ordinary side is identity, the transported side is identity as well.
-/
theorem twistIso_normalization
    {D : Type u₁} [Category.{v₁} D]
    (F G : D ⥤ D) (χ : F ≅ G) (P Q : D ⥤ D)
    (b : P ⋙ F ≅ F ⋙ Q) (lam : F ≅ 𝟭 D) :
    (∀ K : D,
      (χ.symm ≪≫ lam).inv.app (P.obj K) ≫ (twistIso F G χ P Q b).hom.app K ≫
          Q.map ((χ.symm ≪≫ lam).hom.app K) =
        lam.inv.app (P.obj K) ≫ b.hom.app K ≫ Q.map (lam.hom.app K)) ∧
    (∀ (e : P ≅ Q) (K : D),
      lam.inv.app (P.obj K) ≫ b.hom.app K ≫ Q.map (lam.hom.app K) ≫ e.inv.app K =
          𝟙 (P.obj K) →
        (χ.symm ≪≫ lam).inv.app (P.obj K) ≫ (twistIso F G χ P Q b).hom.app K ≫
            Q.map ((χ.symm ≪≫ lam).hom.app K) ≫ e.inv.app K = 𝟙 (P.obj K)) := by
  have h : ∀ K : D,
      (χ.symm ≪≫ lam).inv.app (P.obj K) ≫ (twistIso F G χ P Q b).hom.app K ≫
          Q.map ((χ.symm ≪≫ lam).hom.app K) =
        lam.inv.app (P.obj K) ≫ b.hom.app K ≫ Q.map (lam.hom.app K) := by
    intro K
    simp [twistIso, Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc]
  refine ⟨h, ?_⟩
  intro e K he
  simpa only [← Category.assoc, h K] using he

end CategoryTheory.TransitionIsoTransport
