module

public import Sheaf.SixFunctors.SfCategories
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Right adjoints inherit coefficient comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-unique-adjoint/
sk-prop-sp-unique-adjoint-coefficients.md (blueprint: det-sp-unique-adjoint-coefficients).

The four cases below select the categories already defined by `def-sf-categories`.
In particular the integral category is derived complete and the field categories are
localization/common-stage categories. They are not ordinary constant-ring categories.
The compact-support and scalar functors are the given functors of the node's statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u vC vD vC' vD' uC uD uC' uD'

open CategoryTheory AlgebraicGeometry
open WeilConjectures

namespace WeilConjectures

/-- An index for the four admissible coefficient stages in the standing conventions.
The finite level is positive. Each extension lies inside the fixed coefficient closure.
This is only an index; it introduces no new category or coefficient construction.
Source: def-sf-categories and def-pur-conventions
(blueprint: det-sp-unique-adjoint-coefficients). -/
inductive AdjointCoefficientStage (P : PurityFiniteSetting.{u}) where
  | finite (E : IntermediateField (Padic P.coefficients.l) P.coefficients.Qbar)
      (hE : FiniteDimensional (Padic P.coefficients.l) E) (n : ℕ) (hn : 1 ≤ n)
  | integral (E : IntermediateField (Padic P.coefficients.l) P.coefficients.Qbar)
      (hE : FiniteDimensional (Padic P.coefficients.l) E)
  | rational (E : IntermediateField (Padic P.coefficients.l) P.coefficients.Qbar)
      (hE : FiniteDimensional (Padic P.coefficients.l) E)
  | algebraicClosure

/-- Select exactly the recorded finite-Tor constructible coefficient category. The
integral case retains a uniform Tor interval, and the two field cases use Dctf = Dc.
Source: def-sf-categories (blueprint: det-sp-unique-adjoint-coefficients). -/
abbrev AdjointCoefficientStage.category {P : PurityFiniteSetting.{u}}
    (Λ : AdjointCoefficientStage P) (T : Scheme.{u}) :=
  match Λ with
  | .finite E hE n hn =>
      letI := hE
      sfFiniteConstructibleFiniteTorCategory P.coefficients.l E n hn T
  | .integral E hE =>
      letI := hE
      finiteTorConstructibleIntegralCategory P.coefficients.l E T
  | .rational E hE =>
      letI := hE
      sfRationalConstructibleFiniteTorCategory P.coefficients.l E T
  | .algebraicClosure =>
      sfCommonStageConstructibleFiniteTorCategory P.coefficients.l P.coefficients.Qbar T

/-- Reuse the inherited category structure in each recorded coefficient stage.
Source: def-sf-categories (blueprint: det-sp-unique-adjoint-coefficients). -/
instance adjointCoefficientStageCategory {P : PurityFiniteSetting.{u}}
    (Λ : AdjointCoefficientStage P) (T : Scheme.{u}) :
    Category (Λ.category T) := by
  cases Λ <;> dsimp [AdjointCoefficientStage.category] <;> infer_instance

end WeilConjectures

namespace CategoryTheory

/-- The objectwise transpose of the extended counit. All four hom universes are
independent. `b.inv` has the orientation F' TX → TY F required by the source.
Source: det-sp-unique-adjoint-coefficients, displayed definition of c_J
(blueprint: det-sp-unique-adjoint-coefficients). -/
noncomputable def coefficientRightMate
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {C' : Type uC'} [Category.{vC'} C'] {D' : Type uD'} [Category.{vD'} D']
    (F : C ⥤ D) (F' : C' ⥤ D') (TX : C ⥤ C') (TY : D ⥤ D')
    (b : F ⋙ TY ≅ TX ⋙ F') (G' : D' ⥤ C') (J : D ⥤ C)
    (adj : F' ⊣ G') (adjJ : F ⊣ J) (K : D) :
    TX.obj (J.obj K) ⟶ G'.obj (TY.obj K) :=
  adj.homEquiv _ _ (b.inv.app (J.obj K) ≫ TY.map (adjJ.counit.app K))

private theorem coefficientRightMate_conjugation
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {C' : Type uC'} [Category.{vC'} C'] {D' : Type uD'} [Category.{vD'} D']
    (F : C ⥤ D) (F' : C' ⥤ D') (TX : C ⥤ C') (TY : D ⥤ D')
    (G J : D ⥤ C) (G' J' : D' ⥤ C')
    (adjG : F ⊣ G) (adjJ : F ⊣ J) (adjG' : F' ⊣ G') (adjJ' : F' ⊣ J')
    (b : F ⋙ TY ≅ TX ⋙ F') (K : D) :
    coefficientRightMate F F' TX TY b J' J adjJ' adjJ K =
      TX.map ((adjG.rightAdjointUniq adjJ).inv.app K) ≫
        coefficientRightMate F F' TX TY b G' G adjG' adjG K ≫
        (adjG'.rightAdjointUniq adjJ').hom.app (TY.obj K) := by
  apply (adjJ'.homEquiv _ _).symm.injective
  change _ = F'.map _ ≫ adjJ'.counit.app _
  rw [coefficientRightMate, Equiv.symm_apply_apply]
  simp only [Functor.map_comp, Category.assoc,
    Adjunction.rightAdjointUniq_hom_app_counit]
  have hm := (adjG'.homEquiv _ _).symm_apply_apply
    (b.inv.app (G.obj K) ≫ TY.map (adjG.counit.app K))
  change F'.map (coefficientRightMate F F' TX TY b G' G adjG' adjG K) ≫
    adjG'.counit.app (TY.obj K) = _ at hm
  rw [hm, ← Category.assoc]
  have hn := b.inv.naturality ((adjG.rightAdjointUniq adjJ).inv.app K)
  simp only [Functor.comp_map] at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← TY.map_comp, Adjunction.rightAdjointUniq_inv_app,
    Adjunction.rightAdjointUniq_hom_app_counit]

private theorem coefficientRightMate_naturality
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {C' : Type uC'} [Category.{vC'} C'] {D' : Type uD'} [Category.{vD'} D']
    (F : C ⥤ D) (F' : C' ⥤ D') (TX : C ⥤ C') (TY : D ⥤ D')
    (G : D ⥤ C) (G' : D' ⥤ C') (adjG : F ⊣ G) (adjG' : F' ⊣ G')
    (b : F ⋙ TY ≅ TX ⋙ F') (K L : D) (k : K ⟶ L) :
    TX.map (G.map k) ≫ coefficientRightMate F F' TX TY b G' G adjG' adjG L =
      coefficientRightMate F F' TX TY b G' G adjG' adjG K ≫ G'.map (TY.map k) := by
  unfold coefficientRightMate
  rw [← adjG'.homEquiv_naturality_left, ← adjG'.homEquiv_naturality_right]
  congr 1
  have hn := b.inv.naturality (G.map k)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← TY.map_comp, ← TY.map_comp, adjG.counit_naturality k]

/-- Coefficient comparison for the given compact-support functors on the actual
admissible coefficient categories. The source explicitly assumes that scalar extension
supplies TX and TY on Dctf, and gives F, F' and their right adjoints; these are data here.
Source: blueprint det-sp-unique-adjoint-coefficients and its proof file.

Proof (all seven steps of the node, in mathematical composition order):
1. Write $\varepsilon_f$ for the counit of $F\dashv G$ and $\varepsilon'_f$ for that of $F'\dashv
G'$. Applying [det-sp-unique-right-adjoint] to $(F,G,J)$ and $(F',G',J')$ gives natural isomorphisms
with
$$\varepsilon^J_K\circ F(\gamma_K)=\varepsilon_{f,K},\qquad \varepsilon^{J'}_B\circ
F'(\gamma'_B)=\varepsilon'_{f,B}.$$
Precompose the first equality with $F(\gamma_K^{-1})$ and use
$F(\gamma_K\circ\gamma_K^{-1})=\mathrm{id}$ to obtain $\varepsilon_{f,K}\circ
F(\gamma_K^{-1})=\varepsilon^J_K$.

2. Use [def-weil-pbc-adjunction-mate] with $L_1=F$, $L_2=F'$, the vertical functors $T^X,T^Y$, and
$\alpha=b^{-1}:F'T^X\to T^YF$. Its mate for right adjoints $J,J'$ is $c_J$, and its mate for $G,G'$
is $c_f$: the transpose formula in that node is precisely the definition in the statement. Thus both
are natural transformations. Applying [lem-weil-pbc-adjunct-counit-identity] to these objectwise
transposes gives
$$\varepsilon^{J'}_{T^YK}\circ F'(c_J(K))=T^Y(\varepsilon^J_K)\circ b(JK)^{-1},$$
$$\varepsilon'_{f,T^YK}\circ F'(c_f(K))=T^Y(\varepsilon_{f,K})\circ b(GK)^{-1}.$$
All objects are in the supplied coefficient categories and each transpose is under the supplied
target-stage adjunction.

3. Put $t=\gamma_K^{-1}:JK\to GK$. Naturality of the given $b$ says $F'(T^Xt)\circ b(JK)=b(GK)\circ
T^Y(Ft)$. Precompose by $b(JK)^{-1}$ and postcompose by $b(GK)^{-1}$; this gives the correctly typed
equality
$$b(GK)^{-1}\circ F'(T^Xt)=T^Y(Ft)\circ b(JK)^{-1}.$$
Only the inverse equations for the assumed isomorphisms $b(JK)$ and $b(GK)$ are used.

4. Set $q_K=\gamma'_{T^YK}\circ c_f(K)\circ T^X(\gamma_K^{-1})$. Functoriality of $F'$, Steps 1 and
2, and then Step 3 give
$$\begin{aligned}
\varepsilon^{J'}_{T^YK}\circ F'(q_K)
&=\varepsilon'_{f,T^YK}\circ F'(c_f(K))\circ F'(T^X(\gamma_K^{-1}))\\
&=T^Y(\varepsilon_{f,K})\circ b(GK)^{-1}\circ F'(T^X(\gamma_K^{-1}))\\
&=T^Y(\varepsilon_{f,K}\circ F(\gamma_K^{-1}))\circ b(JK)^{-1}\\
&=T^Y(\varepsilon^J_K)\circ b(JK)^{-1}.
\end{aligned}$$
The last equality is the inverse counit identity of Step 1. It is the transpose of $c_J(K)$ by Step
2. Explicitly, [lem-weil-pbc-adjunct-counit-identity] says that an arrow $h:T^X(JK)\to J'(T^YK)$
with this transpose must equal $J'(T^Y(\varepsilon^J_K)\circ b(JK)^{-1})\circ\eta^{J'}_{T^X(JK)}$.
Both $q_K$ and $c_J(K)$ equal that arrow. Hence $q_K=c_J(K)$.

5. If $c_f(K)$ has inverse $d_K$, then $\gamma'_{T^YK}$ and $T^X(\gamma_K^{-1})$ have inverses
$(\gamma'_{T^YK})^{-1}$ and $T^X(\gamma_K)$, respectively. Step 4 therefore supplies an inverse of
$c_J(K)$, namely
$$T^X(\gamma_K)\circ d_K\circ(\gamma'_{T^YK})^{-1}.$$
Composing in either order cancels each adjacent inverse pair; the inverse pair after $T^X$ cancels
because a functor preserves composition and identities. This proves the isomorphism implication
without asserting that a mate of every isomorphism is invertible.

6. For the chain in the statement, write $\gamma_i:G_i\to J_i$ for [det-sp-unique-right-adjoint].
Substitute Step 4 for $c_{J,12}$ and $c_{J,01}$ in the left side of the desired composition
identity. The factors $T^X_{12}(\gamma_{1,T^Y_{01}K}^{-1})$ and $T^X_{12}(\gamma_{1,T^Y_{01}K})$ are
adjacent and cancel. Naturality of $\gamma_2$ at the arrow $a^Y_K:T^Y_{12}T^Y_{01}K\to T^Y_{02}K$
says
$$J_2(a^Y_K)\circ\gamma_{2,T^Y_{12}T^Y_{01}K}=\gamma_{2,T^Y_{02}K}\circ G_2(a^Y_K).$$
The left side of the desired identity is consequently
$$\gamma_{2,T^Y_{02}K}\circ G_2(a^Y_K)\circ c_{f,12}(T^Y_{01}K)\circ T^X_{12}(c_{f,01}(K))\circ
T^X_{12}T^X_{01}(\gamma_{0,K}^{-1}).$$

7. Apply the assumed composition identity for $c_f$ to the middle three factors of Step 6. This
gives
$$\gamma_{2,T^Y_{02}K}\circ c_{f,02}(K)\circ a^X_{G_0K}\circ T^X_{12}T^X_{01}(\gamma_{0,K}^{-1}).$$
Naturality of the supplied $a^X$ at $\gamma_{0,K}^{-1}:J_0K\to G_0K$ gives
$$a^X_{G_0K}\circ T^X_{12}T^X_{01}(\gamma_{0,K}^{-1})=T^X_{02}(\gamma_{0,K}^{-1})\circ a^X_{J_0K}.$$
Use Step 4 for $02$ to identify the resulting first three factors as $c_{J,02}(K)$. The result is
$c_{J,02}(K)\circ a^X_{J_0K}$, the required right side. When the associators are identities the same
calculation is literal cancellation; no coherence or composition of $b$ beyond the assumed identity
for $c_f$ has been presumed.
(blueprint: det-sp-unique-adjoint-coefficients). -/
theorem det_sp_unique_adjoint_coefficients
    (P : PurityFiniteSetting.{u})
    (f : Arrow Scheme.{u})
    [f.left.Over (Spec (.of P.field.k))] [f.right.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (f.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (f.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (f.right ↘ Spec (.of P.field.k))]
    [QuasiCompact (f.right ↘ Spec (.of P.field.k))]
    [f.hom.IsOver (Spec (.of P.field.k))]
    [IsSeparated f.hom] [LocallyOfFiniteType f.hom] [QuasiCompact f.hom]
    (Λ Λ' : AdjointCoefficientStage P)
    (F : Λ.category f.left ⥤ Λ.category f.right)
    (F' : Λ'.category f.left ⥤ Λ'.category f.right)
    (TX : Λ.category f.left ⥤ Λ'.category f.left)
    (TY : Λ.category f.right ⥤ Λ'.category f.right)
    (G J : Λ.category f.right ⥤ Λ.category f.left)
    (G' J' : Λ'.category f.right ⥤ Λ'.category f.left)
    (adjG : F ⊣ G) (adjJ : F ⊣ J)
    (adjG' : F' ⊣ G') (adjJ' : F' ⊣ J')
    (b : F ⋙ TY ≅ TX ⋙ F') :
    (∀ K : (Λ.category f.right),
      coefficientRightMate F F' TX TY b J' J adjJ' adjJ K =
        TX.map ((adjG.rightAdjointUniq adjJ).inv.app K) ≫
          coefficientRightMate F F' TX TY b G' G adjG' adjG K ≫
          (adjG'.rightAdjointUniq adjJ').hom.app (TY.obj K)) ∧
    (∀ K : (Λ.category f.right), IsIso (coefficientRightMate F F' TX TY b G' G adjG' adjG K) →
      IsIso (coefficientRightMate F F' TX TY b J' J adjJ' adjJ K)) ∧
    (∀ (K L : (Λ.category f.right)) (k : K ⟶ L),
      TX.map (J.map k) ≫ coefficientRightMate F F' TX TY b J' J adjJ' adjJ L =
        coefficientRightMate F F' TX TY b J' J adjJ' adjJ K ≫
          J'.map (TY.map k)) ∧
    (∀ (K L : (Λ.category f.right)) (k : K ⟶ L),
      TX.map (G.map k) ≫ coefficientRightMate F F' TX TY b G' G adjG' adjG L =
        coefficientRightMate F F' TX TY b G' G adjG' adjG K ≫
          G'.map (TY.map k)) := by
  have hc := coefficientRightMate_conjugation F F' TX TY G J G' J'
    adjG adjJ adjG' adjJ' b
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro K h
    rw [hc K]
    infer_instance
  · exact coefficientRightMate_naturality F F' TX TY J J' adjJ adjJ' b
  · exact coefficientRightMate_naturality F F' TX TY G G' adjG adjG' b

/-- The coefficient-chain clause of the same node, for the same geometric morphism
and three admissible coefficient categories. The two associators are supplied by
successive scalar extension. No composition identity for b is assumed.

Proof: substitute the conjugation formula for c_J,01 and c_J,12. Functoriality of
TX12 cancels the adjacent images of gamma1 and its inverse. Naturality of gamma2
moves it past G2(aY). Apply the assumed composition equation for c_f. Naturality
of aX at gamma0 inverse moves that inverse across aX. The 02 conjugation formula
then identifies the remaining three factors with c_J,02. This is Steps 6 and 7
of the node; Steps 1--5 are recorded verbatim in the preceding theorem docstring.
Source: blueprint det-sp-unique-adjoint-coefficients, coefficient-chain paragraph
and its source proof (blueprint: det-sp-unique-adjoint-coefficients). -/
theorem det_sp_unique_adjoint_coefficients_chain
    (P : PurityFiniteSetting.{u}) (f : Arrow Scheme.{u})
    [f.left.Over (Spec (.of P.field.k))] [f.right.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (f.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (f.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (f.right ↘ Spec (.of P.field.k))]
    [QuasiCompact (f.right ↘ Spec (.of P.field.k))]
    [f.hom.IsOver (Spec (.of P.field.k))]
    [IsSeparated f.hom] [LocallyOfFiniteType f.hom] [QuasiCompact f.hom]
    (Λ₀ Λ₁ Λ₂ : AdjointCoefficientStage P)
    (F0 : Λ₀.category f.left ⥤ Λ₀.category f.right)
    (F1 : Λ₁.category f.left ⥤ Λ₁.category f.right)
    (F2 : Λ₂.category f.left ⥤ Λ₂.category f.right)
    (TX01 : Λ₀.category f.left ⥤ Λ₁.category f.left)
    (TX12 : Λ₁.category f.left ⥤ Λ₂.category f.left)
    (TX02 : Λ₀.category f.left ⥤ Λ₂.category f.left)
    (TY01 : Λ₀.category f.right ⥤ Λ₁.category f.right)
    (TY12 : Λ₁.category f.right ⥤ Λ₂.category f.right)
    (TY02 : Λ₀.category f.right ⥤ Λ₂.category f.right)
    (G0 J0 : Λ₀.category f.right ⥤ Λ₀.category f.left)
    (G1 J1 : Λ₁.category f.right ⥤ Λ₁.category f.left)
    (G2 J2 : Λ₂.category f.right ⥤ Λ₂.category f.left)
    (adjG0 : F0 ⊣ G0) (adjJ0 : F0 ⊣ J0)
    (adjG1 : F1 ⊣ G1) (adjJ1 : F1 ⊣ J1)
    (adjG2 : F2 ⊣ G2) (adjJ2 : F2 ⊣ J2)
    (b01 : F0 ⋙ TY01 ≅ TX01 ⋙ F1)
    (b12 : F1 ⋙ TY12 ≅ TX12 ⋙ F2)
    (b02 : F0 ⋙ TY02 ≅ TX02 ⋙ F2)
    (aX : TX01 ⋙ TX12 ≅ TX02) (aY : TY01 ⋙ TY12 ≅ TY02) :
    (∀ K : Λ₀.category f.right,
      TX12.map (coefficientRightMate F0 F1 TX01 TY01 b01 G1 G0 adjG1 adjG0 K) ≫
          coefficientRightMate F1 F2 TX12 TY12 b12 G2 G1 adjG2 adjG1 (TY01.obj K) ≫
          G2.map (aY.hom.app K) =
        aX.hom.app (G0.obj K) ≫
          coefficientRightMate F0 F2 TX02 TY02 b02 G2 G0 adjG2 adjG0 K) →
    ∀ K : Λ₀.category f.right,
      TX12.map (coefficientRightMate F0 F1 TX01 TY01 b01 J1 J0 adjJ1 adjJ0 K) ≫
          coefficientRightMate F1 F2 TX12 TY12 b12 J2 J1 adjJ2 adjJ1 (TY01.obj K) ≫
          J2.map (aY.hom.app K) =
        aX.hom.app (J0.obj K) ≫
          coefficientRightMate F0 F2 TX02 TY02 b02 J2 J0 adjJ2 adjJ0 K := by
  intro h K
  have h01 := coefficientRightMate_conjugation F0 F1 TX01 TY01 G0 J0 G1 J1
    adjG0 adjJ0 adjG1 adjJ1 b01 K
  have h12 := coefficientRightMate_conjugation F1 F2 TX12 TY12 G1 J1 G2 J2
    adjG1 adjJ1 adjG2 adjJ2 b12 (TY01.obj K)
  have h02 := coefficientRightMate_conjugation F0 F2 TX02 TY02 G0 J0 G2 J2
    adjG0 adjJ0 adjG2 adjJ2 b02 K
  rw [h01, h12, h02]
  simp only [Functor.map_comp, Category.assoc]
  rw [← TX12.map_comp_assoc ((adjG1.rightAdjointUniq adjJ1).hom.app _)
    ((adjG1.rightAdjointUniq adjJ1).inv.app _)]
  simp only [Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  have hy := (adjG2.rightAdjointUniq adjJ2).hom.naturality (aY.hom.app K)
  simp only [Functor.comp_obj] at hy
  rw [← hy]
  have hh := congrArg
    (fun t ↦ t ≫ (adjG2.rightAdjointUniq adjJ2).hom.app (TY02.obj K)) (h K)
  simp only [Category.assoc] at hh
  rw [hh]
  have hn := aX.hom.naturality ((adjG0.rightAdjointUniq adjJ0).inv.app K)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]

end CategoryTheory
