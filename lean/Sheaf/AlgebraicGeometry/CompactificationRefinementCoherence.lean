/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenCalculus
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import WeilConjectures.Compactification.CategoryBaseChange

/-!
# Refinement independence and staircase coherence

Source: Stacks Project, Tags 0F7J and 0F7K, common-refinement and three-square
calculations (blueprint: lem-sp-compactification-refinement-coherence).

This is a formal statement for the supplied proper/open calculus on any collection A
of schemes. `Geometry A` supplies all geometric existence assumptions; no qcqs
hypothesis is imposed. Existing `Compactification`, `Triangle` and `Tower` supply the
geometric objects. Arbitrary refinements are retained, including noncartesian ones.
-/

@[expose] public section
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperOpenCalculus

/-- Refinement identities, composition, independence, cocycle, compatibility of binary
composition with common refining towers, the staircase associativity equation, and both
identity towers. The third and fourth clauses quantify independently over every common
refinement and every arrow. Thus the fifth and sixth clauses also compare arbitrary
choices of towers using the same comparisons; no chosen comparison is added as data.

Source: Stacks 0F7J/0F7K, formal P,J,gamma extraction
(blueprint: lem-sp-compactification-refinement-coherence).

Proof plan, following the node:
1. We compose transformations right to left. All formulas below are between fixed
parenthesizations; juxtaposed functors are connected using the supplied proper/open compositors.
Their assumed associativity and unit laws identify the different parenthesizations appearing in
each displayed formula. For a refinement $v:c'\to c$, write $\tau_v:J_j\to P_vJ_{j'}$ for its
square's $\gamma$ after inserting $P_{\mathrm{id}_X}\simeq\mathrm{id}$. Thus $\rho_v$ is
$P_p\tau_v$ followed by $P_pP_v\simeq P_{pv}$. All its factors are natural isomorphisms. The
identity-square axiom gives $\tau_{\mathrm{id}}=\mathrm{id}$ and
$\rho_{\mathrm{id}}=\mathrm{id}$. For $w:c''\to c'$, vertical pasting of the two refinement
squares gives
$$\tau_{vw}=(P_v\tau_w)\circ\tau_v.$$
Apply $P_p$ and its associative compositor
to obtain
$$\rho_{vw}=\rho_w\circ\rho_v.$$
This uses only the pasting and composition identities
assumed in the statement.
2. Let $v,v':c'\to c$ be parallel refinement arrows. The cofilteredness hypothesis (also stated
for precisely this compactification category in [lem-cbc-compactifiable-cofiltered]) gives
$t:e\to c'$ with $vt=v't$. Step 1 gives $\rho_t\rho_v=\rho_{vt}=\rho_{v't}=\rho_t\rho_{v'}$.
Cancel the isomorphism $\rho_t$ to obtain $\rho_v=\rho_{v'}$. This argument does not assume that
refinement arrows are unique or that their open squares are cartesian.
3. For $v_i:d\to c_i$ put $T_{12}^{d}=\rho_{v_1}^{-1}\rho_{v_2}:H_{c_2}\to H_{c_1}$. A further
$t:e\to d$ changes this expression to
$$(\rho_t\rho_{v_1})^{-1}(\rho_t\rho_{v_2})=T_{12}^{d}.$$
For a second common refinement $v_i':d'\to c_i$, choose $s:e\to d$ and $s':e\to d'$ by [lem-cbc-
compactifiable-cofiltered]. Step 2 applied to the parallel arrows $v_i s,v_i's'$ gives
$\rho_s\rho_{v_i}=\rho_{s'}\rho_{v_i'}$ for each $i$. Substituting these two equalities into the
preceding cancellation shows $T_{12}^{d}=T_{12}^{d'}$. This also handles different arrows out of
the same common refinement.
4. For three compactifications, take a common refinement $e$ of all three by applying the
pairwise cofilteredness assumption twice. If its arrows are $a_i:e\to c_i$, step 3 lets every
comparison be computed on $e$. Hence
$$T_{12}T_{23}=(\rho_{a_1}^{-1}\rho_{a_2})(\rho_{a_2}^{-
1}\rho_{a_3})=\rho_{a_1}^{-1}\rho_{a_3}=T_{13}.$$
The same formula gives $T_{ii}=\mathrm{id}$
and $T_{21}=T_{12}^{-1}$. No existence of a categorical limit or smallness of an indexing
category is used.
5. Consider a refining tower $T_+\to T_-$, writing its proper maps as $h:\overline
X_+\to\overline X_-$, $k:\overline Y_+\to\overline Y_-$ and $t:V_+\to V_-$. The exact statement
[lem-cbc-compactifiable-compatible-tower] supplies properness of all three maps and the
equations
$$h a_+=a_-,\quad k i_+=i_-,\quad t j_+=j_-,\quad h b_+=b_-t,\quad p_-h=kp_+,\quad
r_-t=r_+,\quad q_-k=q_+.$$
Let $A$ be the square $(j_+,j_-;\mathrm{id}_X,t)$, $F$ the square
$(b_+,b_-;t,h)$, $D$ the square $(i_+,i_-;\mathrm{id}_Y,k)$, and $E$ the square
$(a_+,a_-;\mathrm{id}_X,h)$; in this notation the first pair is the top/bottom open maps and the
second is the left/right proper maps. Let $B=Q_-$ and $C=Q_+$ be the tower squares
$(b_-,i_-;r_-,p_-)$ and $(b_+,i_+;r_+,p_+)$. Every square has open horizontal and proper
vertical maps, so its supplied $\gamma$ applies. In particular, no pullback property is needed
for $A,D,E,F$.
6. The square $E$ is the horizontal paste of $A,F$, since $b_\pm j_\pm=a_\pm$. Horizontal
pasting therefore gives
$$\gamma_E=(\gamma_FJ_{j_+})\circ(J_{b_-}\gamma_A).$$
The vertical
pastes of $F$ above $B$ and of $C$ above $D$ have the same boundary: top $b_+$, bottom $i_-$,
left $r_+$, right $p_-h=kp_+$. Vertical pasting gives the equality
$$(P_{p_-}\gamma_F)\circ(\gamma_BP_t)=(P_k\gamma_C)\circ(\gamma_DP_{r_+}).$$
These are direct
instances of the assumed axioms for the squares just listed, including the proper compositors
for the equality of the right boundary maps.
7. Let $\alpha_\pm:H_{g,\pm}H_{f,\pm}\to H_{gf,\pm}$ denote the displayed tower transformations
in the statement. Their ingredients are respectively $\gamma_B,\gamma_C$. The refinement
comparisons for $f,g,gf$ use respectively $\gamma_A,\gamma_D,\gamma_E$. Naturality of $\gamma_B$
at the morphism $(\gamma_A)_M:J_{j_-}M\to P_tJ_{j_+}M$, for each $M\in\mathcal D_X$, is exactly
$$(P_{p_-}J_{b_-}\gamma_A)\circ(\gamma_BJ_{j_-})=(\gamma_BP_tJ_{j_+})\circ(J_{i_-}P_{r_-
}\gamma_A).$$
Expand $\rho_h\alpha_-$ using the first equality of step 6, use this naturality
equation, and then use the second equality of step 6, whiskered by $P_{q_-}$ and $J_{j_+}$. The
result is
$$\rho_h\alpha_-=\alpha_+\circ(\rho_k\star\rho_t),$$
where $\star$ is the horizontal
composite: first change the $f$ factor by $\rho_t$ and then the $g$ factor by $\rho_k$. The
identity $q_-k=q_+$ identifies the outer proper functors. The remaining proper and open
compositors agree by their supplied associativity and naturality. Thus this is an equality of
natural transformations, proved componentwise, not inferred from objectwise invertibility.
8. Given two arbitrary towers, choose a common refining tower as in [lem-cbc-compactifiable-
compatible-tower]. Apply step 7 to its maps to the two towers, and invert the refinement
comparisons on the input and output factors. The resulting equation identifies the two $\alpha$
maps under $T$ on each of the three compactification factors. These $T$ maps are independent of
the common tower and its arrows by step 3, and compose by step 4. Thus the equation proves the
asserted compatibility with all common-refinement comparisons, rather than only with a fixed
refining arrow.
9. For $X\xrightarrow fY\xrightarrow gZ\xrightarrow hT$, use the three-map staircase whose
existence is assumed. Write its ambient proper chain as $\overline X\xrightarrow p\overline
Y\xrightarrow q\overline Z\xrightarrow sT$, with opens $a:X\to\overline X$, $e:Y\to\overline Y$,
$o:Z\to\overline Z$. Write $W$ for the inverse image of $Z$ in $\overline Y$, with maps
$k:W\hookrightarrow\overline Y$, $u:W\to Z$, and $i:Y\hookrightarrow W$, so $e=ki$. Write
$U\subset V\subset\overline X$ for the inverse images of $Y\subset W\subset\overline Y$, with
opens $c:U\to V$, $b:V\to\overline X$, $j:X\to U$ and proper maps $r:U\to Y$, $t:V\to W$. Thus
$a=bcj$. The staircase supplies properness of $r,t,u,p,q,s$ and the three squares
$$A=(c,i;r,t),\qquad B=(b,k;t,p),\qquad C=(k,o;u,q).$$
They satisfy $tc=ir$, $pb=kt$, $qk=ou$.
Their horizontal paste $A+B$ and vertical paste $B+C$ are exactly the squares used for the two
composite morphisms. This is the staircase of Tag 0F7K; no geometric existence result is being
deduced from the $P,J,\gamma$ axioms.
10. Work first before the final compositors, from $P_sJ_oP_uJ_iP_rJ_j$ to $P_sP_qP_pJ_bJ_cJ_j$.
The two iterated tower maps use $A$ then $B+C$, or $C$ then $A+B$. Pasting gives
$$\gamma_{A+B}=
(\gamma_BJ_c)\circ(J_k\gamma_A),\qquad\gamma_{B+C}=(P_q\gamma_B)\circ(\gamma_CP_t).$$
After
substituting these formulas, the two maps have the common final factor $P_sP_q\gamma_BJ_cJ_j$.
Their preceding factors agree by
$$(\gamma_CP_tJ_c)\circ(J_oP_u\gamma_A)=(P_qJ_k\gamma_A)\circ(\gamma_CJ_iP_r),$$
whiskered by
$P_s$ and $J_j$. At $M\in\mathcal D_U$ this is precisely naturality of $\gamma_C:J_oP_u\to
P_qJ_k$ at the morphism $(\gamma_A)_M:J_iP_rM\to P_tJ_cM$ in $\mathcal D_W$. Composing with the
proper/open compositors to $P_{sqp}J_a$ preserves the equality; their two parenthesizations
agree by the assumed associativity. This proves the three-map identity on the chosen staircase
by two pasting equations and one naturality square.
11. If either iterated construction uses other compatible towers, compare each binary tower with
the one induced by the fixed staircase using step 8. Insert those comparison equations in the
two composites; every internal $T^{-1}T$ cancels, and step 4 identifies the outside comparisons.
Step 10 then identifies the two maps. Thus the identity holds under the stated comparisons for
arbitrary choices. For an identity morphism use its trivial compactification and an identity
tower. Its interchange square has either both vertical maps identities or both horizontal maps
identities, so the identity-square axiom makes $\gamma$ the identity after the supplied unitors.
The resulting tower map is the unitor on the other factor. Step 8 transports this statement to
other identity towers. This proves both identity laws. -/
theorem compactification_refinement_coherence {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A) : Geometry A →
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (hc : A c.Z),
      F.rho X Y hc hc (Compactification.Refinement.id c) = Iso.refl (F.H X Y c hc)) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c d e : Compactification f) (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
      (r : d.Refinement c) (s : e.Refinement d),
      F.rho X Y hc he (s.comp r) = F.rho X Y hc hd r ≪≫ F.rho X Y hd he s) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c₁ c₂ d e : Compactification f)
      (h₁ : A c₁.Z) (h₂ : A c₂.Z) (hd : A d.Z) (he : A e.Z)
      (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
      (s₁ : e.Refinement c₁) (s₂ : e.Refinement c₂),
      F.compare X Y h₁ h₂ hd r₁ r₂ = F.compare X Y h₁ h₂ he s₁ s₂) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ : Compactification f)
      (h₁ : A c₁.Z) (h₂ : A c₂.Z) (h₃ : A c₃.Z)
      (h₁₂ : A d₁₂.Z) (h₂₃ : A d₂₃.Z) (h₁₃ : A d₁₃.Z)
      (r₁ : d₁₂.Refinement c₁) (r₂ : d₁₂.Refinement c₂)
      (s₂ : d₂₃.Refinement c₂) (s₃ : d₂₃.Refinement c₃)
      (t₁ : d₁₃.Refinement c₁) (t₃ : d₁₃.Refinement c₃),
      F.compare X Y h₂ h₃ h₂₃ s₂ s₃ ≪≫ F.compare X Y h₁ h₂ h₁₂ r₁ r₂ =
        F.compare X Y h₁ h₃ h₁₃ t₁ t₃) ∧
    (∀ (X Y Z : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      (T S R : Compactification.Triangle f g)
      (hT : TriangleObjects (A := A) T) (hS : TriangleObjects (A := A) S)
      (hR : TriangleObjects (A := A) R) (r : TowerRefinement R T) (s : TowerRefinement R S),
      (F.towerIso X Y Z T hT).hom ≫
          (F.compare X Z hS.2.2 hT.2.2 hR.2.2 s.rfg r.rfg).hom =
        NatTrans.hcomp (F.compare X Y hS.1 hT.1 hR.1 s.rf r.rf).hom
            (F.compare Y Z hS.2.1 hT.2.1 hR.2.1 s.rg r.rg).hom ≫
          (F.towerIso X Y Z S hS).hom) ∧
    (∀ (X Y Z W : {X : Scheme.{u} // A X})
      (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Tower f g h) (hT : TowerObjects (A := A) T),
      Functor.whiskerRight
          (F.towerIso X Y Z T.fg ⟨hT.1, hT.2.1, hT.2.2.2.1⟩).hom
          (F.H Z W T.ch hT.2.2.1) ≫
          (F.towerIso X Z W T.fg_h ⟨hT.2.2.2.1, hT.2.2.1, hT.2.2.2.2.2⟩).hom =
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (F.H X Y T.cf hT.1)
            (F.towerIso Y Z W T.gh ⟨hT.2.1, hT.2.2.1, hT.2.2.2.2.1⟩).hom ≫
          (F.towerIso X Y W T.f_gh ⟨hT.1, hT.2.2.2.2.1, hT.2.2.2.2.2⟩).hom) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (hc : A c.Z),
      (F.towerIso X X Y (Compactification.Triangle.unitLeft c) ⟨X.2, hc, hc⟩).hom =
        Functor.whiskerRight (F.identityIso X).hom (F.H X Y c hc) ≫
          (Functor.leftUnitor (F.H X Y c hc)).hom) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (hc : A c.Z),
      (F.towerIso X Y Y (Compactification.Triangle.unitRight c) ⟨hc, Y.2, hc⟩).hom =
        Functor.whiskerLeft (F.H X Y c hc) (F.identityIso Y).hom ≫
          (Functor.rightUnitor (F.H X Y c hc)).hom) := by
  sorry

end AlgebraicGeometry.ProperOpenCalculus
