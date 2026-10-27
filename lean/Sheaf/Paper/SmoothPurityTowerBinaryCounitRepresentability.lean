/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates
import Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair
import Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift
import Sheaf.Paper.SmoothPurityTowerOpenHomComparison
import Mathlib.Algebra.FiveLemma

/-! # Binary coefficient-tower counit gluing steps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₀ v₁ w₀ w₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerBinaryCounit

open SpTowerShriek SpTowerBinaryCtfFibre

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : Base l E) (o : Operations l E b) (q : SpTowerCalculus.Coordinates l E b)

private theorem unique_representing_iso
    {C₀ : Type v₀} {C₁ : Type v₁} [Category.{w₀} C₀] [Category.{w₁} C₁]
    (F₀ : C₀ ⥤ C₁) (good₀ : C₀ → Prop) {P Q : C₀} {K : C₁}
    (eP : F₀.obj P ⟶ K) (eQ : F₀.obj Q ⟶ K)
    (hP : good₀ P) (hQ : good₀ Q)
    (rP : ∀ N, good₀ N → Function.Bijective (fun a : N ⟶ P ↦ F₀.map a ≫ eP))
    (rQ : ∀ N, good₀ N → Function.Bijective (fun a : N ⟶ Q ↦ F₀.map a ≫ eQ)) :
    ∃ c : P ≅ Q, F₀.map c.hom ≫ eQ = eP ∧
      ∀ c' : P ≅ Q, F₀.map c'.hom ≫ eQ = eP → c' = c := by
  obtain ⟨f, hf⟩ := (rQ P hP).surjective eP
  obtain ⟨g, hg⟩ := (rP Q hQ).surjective eQ
  have hfg : f ≫ g = 𝟙 P := by
    apply (rP P hP).injective
    change F₀.map (f ≫ g) ≫ eP = F₀.map (𝟙 P) ≫ eP
    calc
      F₀.map (f ≫ g) ≫ eP = F₀.map f ≫ (F₀.map g ≫ eP) := by
        rw [F₀.map_comp, Category.assoc]
      _ = F₀.map f ≫ eQ := congrArg (fun a ↦ F₀.map f ≫ a) hg
      _ = eP := hf
      _ = F₀.map (𝟙 P) ≫ eP :=
        ((congrArg (fun a ↦ a ≫ eP) (F₀.map_id P)).trans (Category.id_comp eP)).symm
  have hgf : g ≫ f = 𝟙 Q := by
    apply (rQ Q hQ).injective
    change F₀.map (g ≫ f) ≫ eQ = F₀.map (𝟙 Q) ≫ eQ
    calc
      F₀.map (g ≫ f) ≫ eQ = F₀.map g ≫ (F₀.map f ≫ eQ) := by
        rw [F₀.map_comp, Category.assoc]
      _ = F₀.map g ≫ eP := congrArg (fun a ↦ F₀.map g ≫ a) hf
      _ = eQ := hg
      _ = F₀.map (𝟙 Q) ≫ eQ :=
        ((congrArg (fun a ↦ a ≫ eQ) (F₀.map_id Q)).trans (Category.id_comp eQ)).symm
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro c' hc'
  apply Iso.ext
  exact (rQ P hP).injective (hc'.trans hf.symm)

private theorem central_bijective
    {C₀ : Type v₀} {C₁ : Type v₁} [Category.{w₀} C₀] [Preadditive C₀]
    [HasShift C₀ ℤ] [Category.{w₁} C₁] [Preadditive C₁]
    (F₀ : C₀ ⥤ C₁) [F₀.Additive] {A B M G : C₀} {K : C₁}
    (s : A ⟶ B) (t : B ⟶ M) (d : M ⟶ (shiftFunctor C₀ (1 : ℤ)).obj A)
    (e : F₀.obj G ⟶ K) (hrow : HomFiveExact s t d G)
    (himage : ImageHomFiveExact F₀ s t d K)
    (houter : OuterBijective (A := A) (B := B) F₀ e) :
    Function.Bijective (fun a : M ⟶ G ↦ F₀.map a ≫ e) := by
  let r := -(shiftFunctor C₀ (1 : ℤ)).map s
  let theta (X : C₀) : (X ⟶ G) →+ (F₀.obj X ⟶ K) :=
    (Preadditive.rightComp (F₀.obj X) e).comp F₀.mapAddHom
  have square {X Y : C₀} (v : X ⟶ Y) :
      (Preadditive.leftComp K (F₀.map v)).comp (theta Y) =
        (theta X).comp (Preadditive.leftComp G v) := by
    ext a
    exact (Category.assoc _ _ _).symm.trans ((F₀.map_comp v a).symm ▸ rfl)
  rcases houter with ⟨hB, hA, hAs, hBs⟩
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.leftComp G r) (Preadditive.leftComp G d)
    (Preadditive.leftComp G t) (Preadditive.leftComp G s)
    (Preadditive.leftComp K (F₀.map r)) (Preadditive.leftComp K (F₀.map d))
    (Preadditive.leftComp K (F₀.map t)) (Preadditive.leftComp K (F₀.map s))
    (theta _) (theta _) (theta _) (theta _) (theta _)
    (square r) (square d) (square t) (square s)
    (by
      change Function.Exact (fun f ↦ r ≫ f) (fun f ↦ d ≫ f)
      simpa only [r, Preadditive.neg_comp] using hrow.1)
    hrow.2.1 hrow.2.2 himage.1 himage.2.1 himage.2.2
    hBs.surjective hAs hB hA.injective

/-- Binary local representing pairs admit a global representing counit, with restriction,
overlap uniqueness, signed factorization and the exact five-term Hom comparison.

Source: blueprint, latest, det-sp-tower-gluing, Gluing paragraph, retained proof
steps 7,9,10 (blueprint: lem-sp-tower-binary-counit-representability).

Proof:
1. For D contained in U, compose the exact open adjunction with the representing
bijection of P. The result is b |-> F_D(b) followed by restrictedCounit. The
calculus lem-sp-coefficient-tower-shriek-calculus identifies nested extension and
its counit, and preserves the unnormalized constructible finite-Tor categories.
Do the same inside V, in particular at W=U intersection V.
2. Representability on W tested on the other representing object supplies c and
its inverse. Injectivity of the two representing bijections makes their composites
identities and proves uniqueness among counit-preserving isomorphisms.
3. By lem-pur-sequence-site-open-extension, the strict sequence-site categories
are the open slices of the sequence topos. Apply clause (2) of
lem-sp-ringed-topos-binary-descent to its constant open subterminals. They cover
at every level, giving the displayed natural signed triangle A_M -> B_M -> M.
Exact open extension and shifts preserve the uniform intervals, enlarged by
finite unions as necessary; the calculus identifies F_h j_D! with F_D.
4. The overlap equation and preservation of counits give F_h(s_G) beta=0:
the two components cancel with precisely the sign in coverS. Apply clause (i)
of lem-weil-pbc-hom-out-of-triangle-exact to the image distinguished triangle.
It supplies e with F_h(t_G)e=beta, which gives both local equations.
5. For any such e, the open adjunction identifies theta on j_D!N with the local
representing bijection followed by a_D. On W use the nested U equation. This
also applies to shifted restrictions. Finite direct sums turn Hom into products,
so all four outer maps for B_M[1],A_M[1],B_M,A_M are bijective.
6. Apply clauses (i),(ii) of lem-weil-pbc-hom-out-of-triangle-exact to the triangle
and clause (ii) to its signed rotation. Consecutive composites vanish, so both
five-term rows are exact at all three interior terms. In the lower row leave
F_h(A[1]) as written, equivalently conjugate by the exact functor's shift iso.
7. Functoriality gives theta_T(f a)=F_h(f)theta_(T')(a) for every arrow f,
including the connecting map and the negative shifted s. Additivity makes these
maps homomorphisms; hence this is a morphism of exact five-term Hom rows.
8. The four outer bijections satisfy the hypotheses of lem-weil-pbc-five-lemma
in abelian groups. Thus the central theta_M is bijective. The same composition
equation proves naturality. Only the local equations were used, so every lift
represents; this asserts no uniqueness of arbitrary glued derived morphisms. -/
theorem binary_counit_representability
    (p : ℕ) (hp : 0 < p) (hlp : l ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (Z Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (h : Z ⟶ Y) (c₀ : Compactification h.left)
    (U V : Z.left.Opens) (hcover : U ⊔ V = ⊤)
    (_hF : ∀ M : D l E Z.left, good l E b q Z.left M →
      good l E b q Y.left ((F l E b o c₀).obj M))
    (_hFD : ∀ (D₀ : Z.left.Opens) (N : D l E D₀.toScheme),
      good l E b q D₀.toScheme N →
      good l E b q Y.left ((support l E b o c₀ D₀).obj N))
    (K : D l E Y.left) (_hK : good l E b q Y.left K)
    (P : D l E U.toScheme) (_hP : good l E b q U.toScheme P)
    (Q : D l E V.toScheme) (_hQ : good l E b q V.toScheme Q)
    (eU : (support l E b o c₀ U).obj P ⟶ K)
    (eV : (support l E b o c₀ V).obj Q ⟶ K)
    (hU : Represents l E b q (support l E b o c₀ U) P K eU)
    (hV : Represents l E b q (support l E b o c₀ V) Q K eV) :
    (∀ (D₀ : Z.left.Opens) (i : D₀ ≤ U),
      good l E b q D₀.toScheme ((restrictionBetween l E b o i).obj P) ∧
      Represents l E b q (support l E b o c₀ D₀)
        ((restrictionBetween l E b o i).obj P) K
        (restrictedCounit l E b o c₀ i P K eU)) ∧
    (∀ (D₀ : Z.left.Opens) (i : D₀ ≤ V),
      good l E b q D₀.toScheme ((restrictionBetween l E b o i).obj Q) ∧
      Represents l E b q (support l E b o c₀ D₀)
        ((restrictionBetween l E b o i).obj Q) K
        (restrictedCounit l E b o c₀ i Q K eV)) ∧
    ∃ c : (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).obj P ≅
        (restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).obj Q,
      ((support l E b o c₀ (U ⊓ V)).map c.hom ≫
          restrictedCounit l E b o c₀ (inf_le_right : U ⊓ V ≤ V) Q K eV =
        restrictedCounit l E b o c₀ (inf_le_left : U ⊓ V ≤ U) P K eU) ∧
      (∀ c' : (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).obj P ≅
          (restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).obj Q,
        (support l E b o c₀ (U ⊓ V)).map c'.hom ≫
            restrictedCounit l E b o c₀ (inf_le_right : U ⊓ V ≤ V) Q K eV =
          restrictedCounit l E b o c₀ (inf_le_left : U ⊓ V ≤ U) P K eU → c' = c) ∧
      ∀ (G : D l E Z.left) (_hG : good l E b q Z.left G)
        (aU : (restriction l E b o U).obj G ≅ P)
        (aV : (restriction l E b o V).obj G ≅ Q),
        (restrictionComp l E b o (inf_le_left : U ⊓ V ≤ U)).hom.app G ≫
            (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).map aU.hom ≫ c.hom =
          (restrictionComp l E b o (inf_le_right : U ⊓ V ≤ V)).hom.app G ≫
            (restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).map aV.hom →
        (∃ e : (F l E b o c₀).obj G ⟶ K,
          LiftEquations l E b o c₀ U V eU eV aU aV e) ∧
        ∀ (e : (F l E b o c₀).obj G ⟶ K),
          LiftEquations l E b o c₀ U V eU eV aU aV e →
          Represents l E b q (F l E b o c₀) G K e ∧
          OpenThetaEquation l E b o q c₀ U eU aU e ∧
          OpenThetaEquation l E b o q c₀ V eV aV e ∧
          OpenThetaEquation l E b o q c₀ (U ⊓ V)
            (restrictedCounit l E b o c₀ (inf_le_left : U ⊓ V ≤ U) P K eU)
            ((restrictionComp l E b o (inf_le_left : U ⊓ V ≤ U)).app G ≪≫
              (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).mapIso aU) e ∧
          (F l E b o c₀).map (coverS l E b o U V G) ≫
              beta l E b o c₀ U V eU eV aU aV = 0 ∧
          (F l E b o c₀).map (coverT l E b o U V G) ≫ e =
            beta l E b o c₀ U V eU eV aU aV ∧
          (∀ (M M' : D l E Z.left) (v : M' ⟶ M) (a : M ⟶ G),
            (F l E b o c₀).map (v ≫ a) ≫ e =
              (F l E b o c₀).map v ≫ ((F l E b o c₀).map a ≫ e)) ∧
          ∀ M : D l E Z.left, good l E b q Z.left M →
            ∃ δ : M ⟶ (shiftFunctor _ (1 : ℤ)).obj (coverA l E b o U V M),
              Triangle.mk (coverS l E b o U V M) (coverT l E b o U V M) δ ∈
                distTriang _ ∧
              good l E b q Z.left (coverA l E b o U V M) ∧
              good l E b q Z.left (coverB l E b o U V M) ∧
              good l E b q Z.left
                ((shiftFunctor _ (1 : ℤ)).obj (coverA l E b o U V M)) ∧
              good l E b q Z.left
                ((shiftFunctor _ (1 : ℤ)).obj (coverB l E b o U V M)) ∧
              HomFiveExact (coverS l E b o U V M) (coverT l E b o U V M) δ G ∧
              ImageHomFiveExact (F l E b o c₀)
                (coverS l E b o U V M) (coverT l E b o U V M) δ K ∧
              OuterBijective (A := coverA l E b o U V M) (B := coverB l E b o U V M)
                (F l E b o c₀) e := by
  have rU := restricted_representing_pair l E b o q p hp hlp k Z Y h c₀ U K P _hP eU hU
  have rV := restricted_representing_pair l E b o q p hp hlp k Z Y h c₀ V K Q _hQ eV hV
  obtain ⟨c, hc, huniq⟩ := unique_representing_iso
    (support l E b o c₀ (U ⊓ V)) (good l E b q (U ⊓ V).toScheme)
    (restrictedCounit l E b o c₀ (inf_le_left : U ⊓ V ≤ U) P K eU)
    (restrictedCounit l E b o c₀ (inf_le_right : U ⊓ V ≤ V) Q K eV)
    (rU (U ⊓ V) inf_le_left).1 (rV (U ⊓ V) inf_le_right).1
    (rU (U ⊓ V) inf_le_left).2 (rV (U ⊓ V) inf_le_right).2
  refine ⟨rU, rV, c, hc, huniq, ?_⟩
  intro G hG aU aV hcompat
  obtain ⟨hex, hzero, hfactor⟩ := compatible_counit_lift l E b o q p hp hlp k Z Y h c₀
    U V hcover _hF _hFD K _hK P _hP Q _hQ eU eV hU hV c hc G hG aU aV hcompat
  refine ⟨hex, ?_⟩
  intro e he
  obtain ⟨hthetaU, hthetaV, hthetaW, hcomparison⟩ :=
    open_hom_comparison l E b o q p hp hlp k Z Y h c₀ U V hcover _hF _hFD
      K _hK P _hP Q _hQ eU eV hU hV G hG aU aV e he
  refine ⟨?_, hthetaU, hthetaV, hthetaW, hzero, hfactor e he, ?_, hcomparison⟩
  · intro M hM
    obtain ⟨d, _, _, _, _, _, hrow, himage, houter⟩ := hcomparison M hM
    exact central_bijective (F l E b o c₀) (coverS l E b o U V M)
      (coverT l E b o U V M) d e hrow himage houter
  · intro M M' v a
    rw [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ProEtale.SpTowerBinaryCounit
