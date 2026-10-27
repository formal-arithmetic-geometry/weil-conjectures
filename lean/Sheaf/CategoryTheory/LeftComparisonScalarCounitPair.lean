module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Scalar-counit pairs under compatible left comparisons

Source: Weil conjectures blueprint, `sec-smooth-purity`, `sk-lem-sp-reduction`,
`sk-lem-sp-reduction-exceptional.proof.md`, Charts and compactification refinement
(blueprint: lem-sp-left-comparison-scalar-counit-pair).

The maps are arbitrary natural maps; only the left comparisons are isomorphisms.
Finite chains are indexed by `Fin (n + 1)`, including the length-zero chain.
For actual adjunctions the final counit assertion is the existing
`Adjunction.ofNatIsoLeft_counit`: its right side is exactly `leftComparisonCounit`.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {X_A : Type u₁} {X_B : Type u₂} {Y_A : Type u₃} {Y_B : Type u₄}
  [Category.{v₁} X_A] [Category.{v₂} X_B] [Category.{v₃} Y_A] [Category.{v₄} Y_B]

/-- The specified left-isomorphism transport of a natural counit-shaped map.
Source: blueprint, Charts and refinement cancellation
(blueprint: lem-sp-left-comparison-scalar-counit-pair). -/
def leftComparisonCounit {F F' : X_A ⥤ Y_A} {H : Y_A ⥤ X_A}
    (ε : H ⋙ F ⟶ 𝟭 Y_A) (e : F ≅ F') : H ⋙ F' ⟶ 𝟭 Y_A :=
  Functor.whiskerLeft H e.inv ≫ ε

/-- The left member D of the scalar-counit equation, with its specified coefficient map.
Source: blueprint, Charts and refinement cancellation
(blueprint: lem-sp-left-comparison-scalar-counit-pair). -/
def scalarCounitPairLeft {F_A : X_A ⥤ Y_A} {F_B : X_B ⥤ Y_B}
    {H_A : Y_A ⥤ X_A} {H_B : Y_B ⥤ X_B}
    {T_X : X_A ⥤ X_B} {T_Y : Y_A ⥤ Y_B}
    (q : F_A ⋙ T_Y ⟶ T_X ⋙ F_B) (a : H_A ⋙ T_X ⟶ T_Y ⋙ H_B)
    (ε_B : H_B ⋙ F_B ⟶ 𝟭 Y_B) (K : Y_A) :
    T_Y.obj (F_A.obj (H_A.obj K)) ⟶ T_Y.obj K :=
  q.app (H_A.obj K) ≫ F_B.map (a.app K) ≫ ε_B.app (T_Y.obj K)

/-- Both individual conjugacy identities and the resulting equivalence of scalar-counit
 equations. Source: blueprint, Charts and refinement cancellation
(blueprint: lem-sp-left-comparison-scalar-counit-pair).
This packages the conclusion, without imposing adjunctions or invertible coefficient maps. -/
def ScalarCounitPairConjugacy
    {F_A F'_A : X_A ⥤ Y_A} {F_B F'_B : X_B ⥤ Y_B}
    {H_A : Y_A ⥤ X_A} {H_B : Y_B ⥤ X_B}
    {T_X : X_A ⥤ X_B} {T_Y : Y_A ⥤ Y_B}
    (ε_A : H_A ⋙ F_A ⟶ 𝟭 Y_A) (ε_B : H_B ⋙ F_B ⟶ 𝟭 Y_B)
    (e_A : F_A ≅ F'_A) (e_B : F_B ≅ F'_B)
    (q : F_A ⋙ T_Y ⟶ T_X ⋙ F_B) (q' : F'_A ⋙ T_Y ⟶ T_X ⋙ F'_B)
    (a : H_A ⋙ T_X ⟶ T_Y ⋙ H_B) : Prop :=
  ∀ K : Y_A,
    (T_Y.map (e_A.hom.app (H_A.obj K)) ≫
        scalarCounitPairLeft q' a (leftComparisonCounit ε_B e_B) K =
      scalarCounitPairLeft q a ε_B K) ∧
    (T_Y.map (e_A.hom.app (H_A.obj K)) ≫
        T_Y.map ((leftComparisonCounit ε_A e_A).app K) = T_Y.map (ε_A.app K)) ∧
    (scalarCounitPairLeft q a ε_B K = T_Y.map (ε_A.app K) ↔
      scalarCounitPairLeft q' a (leftComparisonCounit ε_B e_B) K =
        T_Y.map ((leftComparisonCounit ε_A e_A).app K))

/-- Conjugacy of both maps, also in the inverse direction.
Source: blueprint, Charts and refinement cancellation
(blueprint: lem-sp-left-comparison-scalar-counit-pair).

Proof: Fix K. The coefficient square moves the comparison past q; naturality of e_B
at a_K moves it past F_B(a_K). The inverse component in the transported ε_B then
cancels it. This proves D' L = D using only category associativity and inverse laws
(def-nagata-category). Functoriality and the defining inverse component give E' L = E.
Since L is invertible, precomposition by L gives the equivalence of the two equations.
Multiply the coefficient square by the inverse components to obtain the reversed
square; the transported map followed by e_R(H_R K) is ε_R. The same two calculations
with primed and unprimed data exchanged give the two inverse identities. -/
theorem leftComparison_scalarCounitPair
    {F_A F'_A : X_A ⥤ Y_A} {F_B F'_B : X_B ⥤ Y_B}
    {H_A : Y_A ⥤ X_A} {H_B : Y_B ⥤ X_B}
    {T_X : X_A ⥤ X_B} {T_Y : Y_A ⥤ Y_B}
    (ε_A : H_A ⋙ F_A ⟶ 𝟭 Y_A) (ε_B : H_B ⋙ F_B ⟶ 𝟭 Y_B)
    (e_A : F_A ≅ F'_A) (e_B : F_B ≅ F'_B)
    (q : F_A ⋙ T_Y ⟶ T_X ⋙ F_B) (q' : F'_A ⋙ T_Y ⟶ T_X ⋙ F'_B)
    (a : H_A ⋙ T_X ⟶ T_Y ⋙ H_B)
    (h : ∀ M : X_A, T_Y.map (e_A.hom.app M) ≫ q'.app M =
      q.app M ≫ e_B.hom.app (T_X.obj M)) :
    ScalarCounitPairConjugacy ε_A ε_B e_A e_B q q' a ∧
    (∀ K : Y_A,
      (T_Y.map (e_A.inv.app (H_A.obj K)) ≫ scalarCounitPairLeft q a ε_B K =
        scalarCounitPairLeft q' a (leftComparisonCounit ε_B e_B) K) ∧
      (T_Y.map (e_A.inv.app (H_A.obj K)) ≫ T_Y.map (ε_A.app K) =
        T_Y.map ((leftComparisonCounit ε_A e_A).app K))) := by
  have hd (K : Y_A) :
      T_Y.map (e_A.hom.app (H_A.obj K)) ≫
          scalarCounitPairLeft q' a (leftComparisonCounit ε_B e_B) K =
        scalarCounitPairLeft q a ε_B K := by
    dsimp [scalarCounitPairLeft, leftComparisonCounit]
    rw [← Category.assoc, ← Category.assoc, h]
    simp only [Category.assoc]
    erw [← e_B.hom.naturality_assoc (a.app K)]
    simp
  have he (K : Y_A) :
      T_Y.map (e_A.hom.app (H_A.obj K)) ≫
          T_Y.map ((leftComparisonCounit ε_A e_A).app K) = T_Y.map (ε_A.app K) := by
    dsimp [leftComparisonCounit]
    simp [← Functor.map_comp]
  constructor
  · intro K
    refine ⟨hd K, he K, ?_⟩
    rw [← cancel_epi (T_Y.map (e_A.hom.app (H_A.obj K))), hd, he]
  · intro K
    constructor
    · apply (cancel_epi (T_Y.map (e_A.hom.app (H_A.obj K)))).1
      simpa [← Functor.map_comp, ← Category.assoc] using (hd K).symm
    · apply (cancel_epi (T_Y.map (e_A.hom.app (H_A.obj K)))).1
      simpa [← Functor.map_comp, ← Category.assoc] using (he K).symm

/-- The composite of a finite chain of natural left comparisons, with the identity
for a length-zero chain. Source: blueprint, refinement-chain cancellation
(blueprint: lem-sp-left-comparison-scalar-counit-pair). -/
def scalarCounitComparisonChain : (n : ℕ) → (F : Fin (n + 1) → X_A ⥤ Y_A) →
    (∀ i : Fin n, F i.castSucc ≅ F i.succ) → (F 0 ≅ F (Fin.last n))
  | 0, F, _ => Iso.refl (F 0)
  | n + 1, F, e =>
    scalarCounitComparisonChain n (fun i ↦ F i.castSucc) (fun i ↦ e i.castSucc) ≪≫
      e (Fin.last n)

/-- Successive specified counit transports along a finite chain, including no transport
at length zero. Source: blueprint, refinement-chain cancellation
(blueprint: lem-sp-left-comparison-scalar-counit-pair). -/
def scalarCounitTransportChain {H : Y_A ⥤ X_A} :
    (n : ℕ) → (F : Fin (n + 1) → X_A ⥤ Y_A) →
    (∀ i : Fin n, F i.castSucc ≅ F i.succ) →
    (H ⋙ F 0 ⟶ 𝟭 Y_A) → (H ⋙ F (Fin.last n) ⟶ 𝟭 Y_A)
  | 0, _, _, ε => ε
  | n + 1, F, e, ε => leftComparisonCounit
      (scalarCounitTransportChain n (fun i ↦ F i.castSucc) (fun i ↦ e i.castSucc) ε)
      (e (Fin.last n))

private theorem leftComparisonCounit_trans
    {F F' F'' : X_A ⥤ Y_A} {H : Y_A ⥤ X_A}
    (ε : H ⋙ F ⟶ 𝟭 Y_A) (e : F ≅ F') (f : F' ≅ F'') :
    leftComparisonCounit (leftComparisonCounit ε e) f =
      leftComparisonCounit ε (e ≪≫ f) := by
  ext K
  simp [leftComparisonCounit]

private theorem scalarCounitTransportChain_eq {H : Y_A ⥤ X_A}
    (n : ℕ) (F : Fin (n + 1) → X_A ⥤ Y_A)
    (e : ∀ i : Fin n, F i.castSucc ≅ F i.succ) (ε : H ⋙ F 0 ⟶ 𝟭 Y_A) :
    scalarCounitTransportChain n F e ε =
      leftComparisonCounit ε (scalarCounitComparisonChain n F e) := by
  induction n with
  | zero =>
    ext K
    simp [scalarCounitTransportChain, scalarCounitComparisonChain, leftComparisonCounit]
  | succ n ih =>
    dsimp only [scalarCounitTransportChain, scalarCounitComparisonChain]
    rw [ih, leftComparisonCounit_trans]

/-- A finite chain has the coefficient square of its composite, the transported counits
are exactly the transport by that composite, and both scalar-counit formulas hold for it.
Source: blueprint, Charts and refinement cancellation
(blueprint: lem-sp-left-comparison-scalar-counit-pair).

Proof: Induct on the length. At zero the comparison is the identity, the counit is
unchanged and the square is an identity. For the induction step, apply functoriality
to the composite comparison and use the preceding square followed by the next square.
Associativity and (f e)⁻¹ = e⁻¹ f⁻¹ identify the successive counit transport with
transport by the composite. Apply the two cancellations of leftComparison_scalarCounitPair
to this composite square. In particular length two is the stated f_R e_R formula. -/
theorem leftComparison_scalarCounitPair_chain
    {H_A : Y_A ⥤ X_A} {H_B : Y_B ⥤ X_B}
    {T_X : X_A ⥤ X_B} {T_Y : Y_A ⥤ Y_B}
    (n : ℕ) (F_A : Fin (n + 1) → X_A ⥤ Y_A) (F_B : Fin (n + 1) → X_B ⥤ Y_B)
    (e_A : ∀ i : Fin n, F_A i.castSucc ≅ F_A i.succ)
    (e_B : ∀ i : Fin n, F_B i.castSucc ≅ F_B i.succ)
    (q : ∀ i : Fin (n + 1), F_A i ⋙ T_Y ⟶ T_X ⋙ F_B i)
    (a : H_A ⋙ T_X ⟶ T_Y ⋙ H_B)
    (ε_A : H_A ⋙ F_A 0 ⟶ 𝟭 Y_A) (ε_B : H_B ⋙ F_B 0 ⟶ 𝟭 Y_B)
    (h : ∀ (i : Fin n) (M : X_A),
      T_Y.map ((e_A i).hom.app M) ≫ (q i.succ).app M =
        (q i.castSucc).app M ≫ (e_B i).hom.app (T_X.obj M)) :
    (∀ M : X_A,
      T_Y.map ((scalarCounitComparisonChain n F_A e_A).hom.app M) ≫
          (q (Fin.last n)).app M =
        (q 0).app M ≫ (scalarCounitComparisonChain n F_B e_B).hom.app (T_X.obj M)) ∧
    scalarCounitTransportChain n F_A e_A ε_A =
      leftComparisonCounit ε_A (scalarCounitComparisonChain n F_A e_A) ∧
    scalarCounitTransportChain n F_B e_B ε_B =
      leftComparisonCounit ε_B (scalarCounitComparisonChain n F_B e_B) ∧
    ScalarCounitPairConjugacy ε_A ε_B
      (scalarCounitComparisonChain n F_A e_A) (scalarCounitComparisonChain n F_B e_B)
      (q 0) (q (Fin.last n)) a := by
  have hs : ∀ M : X_A,
      T_Y.map ((scalarCounitComparisonChain n F_A e_A).hom.app M) ≫
          (q (Fin.last n)).app M =
        (q 0).app M ≫ (scalarCounitComparisonChain n F_B e_B).hom.app (T_X.obj M) := by
    induction n with
    | zero =>
      intro M
      simp [scalarCounitComparisonChain]
    | succ n ih =>
      intro M
      dsimp only [scalarCounitComparisonChain, Iso.trans_hom, NatTrans.comp_app]
      simp only [Functor.map_comp, Category.assoc]
      erw [h (Fin.last n) M]
      have hi := ih (fun i ↦ F_A i.castSucc) (fun i ↦ F_B i.castSucc)
        (fun i ↦ e_A i.castSucc) (fun i ↦ e_B i.castSucc)
        (fun i ↦ q i.castSucc) ε_A ε_B (fun i ↦ h i.castSucc) M
      simpa only [Category.assoc, Fin.castSucc_zero, Fin.succ_last, Functor.comp_obj] using
        congrArg
        (fun t ↦ t ≫ (e_B (Fin.last n)).hom.app (T_X.obj M)) hi
  exact ⟨hs, scalarCounitTransportChain_eq n F_A e_A ε_A,
    scalarCounitTransportChain_eq n F_B e_B ε_B,
    (leftComparison_scalarCounitPair ε_A ε_B _ _ (q 0) (q (Fin.last n)) a hs).1⟩

/-- Two refinement chains with the same composite have identical specified counit
transports. Their conjugating morphism T_Y(e_A(H_A K)) is therefore the same as well.
Endpoint equalities identify the starting and ending functors of the two chain encodings.
Source: blueprint, Charts and refinement cancellation
(blueprint: lem-sp-left-comparison-scalar-counit-pair).

Proof: The chain normalization identifies each transport with the original map
precomposed by the inverse of the composite comparison. Substitute the equality of
composites. The conjugacy formulas for the two chains consequently use the same
comparison component and the same transported counits. -/
theorem leftComparison_scalarCounitPair_refinement
    {H : Y_A ⥤ X_A} (n m : ℕ)
    (F : Fin (n + 1) → X_A ⥤ Y_A) (G : Fin (m + 1) → X_A ⥤ Y_A)
    (e : ∀ i : Fin n, F i.castSucc ≅ F i.succ)
    (f : ∀ i : Fin m, G i.castSucc ≅ G i.succ)
    (hs : F 0 = G 0) (ht : F (Fin.last n) = G (Fin.last m))
    (h : scalarCounitComparisonChain n F e ≪≫ eqToIso ht =
      eqToIso hs ≪≫ scalarCounitComparisonChain m G f)
    (ε : H ⋙ F 0 ⟶ 𝟭 Y_A) :
    leftComparisonCounit (scalarCounitTransportChain n F e ε) (eqToIso ht) =
      scalarCounitTransportChain m G f (leftComparisonCounit ε (eqToIso hs)) := by
  rw [scalarCounitTransportChain_eq, scalarCounitTransportChain_eq,
    leftComparisonCounit_trans, leftComparisonCounit_trans, h]

end CategoryTheory
