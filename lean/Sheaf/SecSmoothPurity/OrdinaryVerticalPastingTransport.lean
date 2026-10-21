module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.NatTrans

/-!
# Transport of an ordinary vertical pasting equation

Source: Stacks Project, Tag 0F7C (lemma-shriek-proper-and-open-compose), which
motivates the vertical proper/open pasting shape only; the abstract componentwise
transport argument is the agent proof recorded for this node
(blueprint: lem-sp-ordinary-vertical-pasting-transport).
-/

@[expose] public section
set_option autoImplicit false

universe uA uB uC uD uE uF uA' uB' uC' uD' uE' uF'

open CategoryTheory

namespace CategoryTheory

/--
Transport a vertical pasting equality through functors and coherent invertible
comparisons: if the primed cells satisfy the vertical pasting identity, then the
unprimed pasting identity holds after applying `EB`, componentwise.  No
faithfulness or equivalence of any realization functor is assumed, and the cells
`a, b, c` need not be invertible.

Source: Stacks Project, Tag 0F7C (lemma-shriek-proper-and-open-compose), the
vertical proper/open composition shape only; the proof below is the abstract
categorical transport argument for this node
(blueprint: lem-sp-ordinary-vertical-pasting-transport).

Proof (the node's steps).  Fix `N : E` and put `x = EE.obj N`.
1. Comparison components.  For a composite `HG` the stipulated comparison has
   component `e_{HG,N} = H'(e_{G,N}) ∘ e_{H,G(N)}`; iterating it defines
   `u = e_{P₁₂J,N}`, `q = e_{P₁P₂J,N}`, `z = e_{P₁IR₂,N}`, `v = e_{KR₁R₂,N}` and
   `w = e_{KR₁₂,N}`.  Both bracketings of `v` agree by preservation of
   composition, the functor associators have identity components, and each of
   `u, q, z, v, w` is invertible.
2. Left compositor.  The `cP` comparison `hP` at `J N`, followed by naturality
   of `cP'` at `e_{J,N}`, gives `q ∘ EB(cP_{JN}) = cP'_{J'x} ∘ u`.
3. Middle whiskering.  Naturality of `eP₁` at `b_N` and the respected-cell
   equation `hB` give `z ∘ EB(P₁(b_N)) = P₁'(b'_x) ∘ q`.
4. Right whiskering.  The respected-cell equation `hA` at `R₂ N` and naturality
   of `a'` at `e_{R₂,N}` give `v ∘ EB(a_{R₂N}) = a'_{R₂'x} ∘ z`.
5. Outer cell and right compositor.  The respected-cell equation `hC` is
   `w ∘ EB(c_N) = c'_x ∘ u`; naturality of `eK` at `cR_N` and the `cR`
   comparison `hR` give `v ∘ EB(K(cR_N)) = K'(cR'_x) ∘ w`.
6. Composing Steps 4, 3, 2 gives
   `v ∘ EB(L_N) = a'_{R₂'x} ∘ P₁'(b'_x) ∘ cP'_{J'x} ∘ u` for
   `L_N = a_{R₂N} ∘ P₁(b_N) ∘ cP_{JN}`, and Step 5 gives
   `v ∘ EB(H_N) = K'(cR'_x) ∘ c'_x ∘ u` for `H_N = K(cR_N) ∘ c_N`.
7. The primed pasting identity `hPasting` at `x` makes the two right-hand sides
   equal, so `v ∘ EB(L_N) = v ∘ EB(H_N)`; cancelling the invertible `v` gives
   `EB(L_N) = EB(H_N)`, the conclusion.  Only functoriality of `EB` is used.
-/
theorem ordinaryVerticalPastingTransport
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE}
    {F : Type uF} {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
    {D' : Type uD'} {E' : Type uE'} {F' : Type uF'}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    [Category A'] [Category B'] [Category C'] [Category D'] [Category E'] [Category F']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    {EE : E ⥤ E'} {EF : F ⥤ F'}
    {K : A ⥤ B} {I : C ⥤ D} {J : E ⥤ F}
    {P₁ : D ⥤ B} {P₂ : F ⥤ D} {P₁₂ : F ⥤ B}
    {R₁ : C ⥤ A} {R₂ : E ⥤ C} {R₁₂ : E ⥤ A}
    {K' : A' ⥤ B'} {I' : C' ⥤ D'} {J' : E' ⥤ F'}
    {P₁' : D' ⥤ B'} {P₂' : F' ⥤ D'} {P₁₂' : F' ⥤ B'}
    {R₁' : C' ⥤ A'} {R₂' : E' ⥤ C'} {R₁₂' : E' ⥤ A'}
    {cP : P₁₂ ≅ P₂ ⋙ P₁} {cR : R₁₂ ≅ R₂ ⋙ R₁}
    {cP' : P₁₂' ≅ P₂' ⋙ P₁'} {cR' : R₁₂' ≅ R₂' ⋙ R₁'}
    {a : I ⋙ P₁ ⟶ R₁ ⋙ K} {b : J ⋙ P₂ ⟶ R₂ ⋙ I}
    {c : J ⋙ P₁₂ ⟶ R₁₂ ⋙ K}
    {a' : I' ⋙ P₁' ⟶ R₁' ⋙ K'} {b' : J' ⋙ P₂' ⟶ R₂' ⋙ I'}
    {c' : J' ⋙ P₁₂' ⟶ R₁₂' ⋙ K'}
    (eP₁ : P₁ ⋙ EB ≅ ED ⋙ P₁') (eP₂ : P₂ ⋙ ED ≅ EF ⋙ P₂')
    (eP₁₂ : P₁₂ ⋙ EB ≅ EF ⋙ P₁₂')
    (eR₁ : R₁ ⋙ EA ≅ EC ⋙ R₁') (eR₂ : R₂ ⋙ EC ≅ EE ⋙ R₂')
    (eR₁₂ : R₁₂ ⋙ EA ≅ EE ⋙ R₁₂')
    (eK : K ⋙ EB ≅ EA ⋙ K') (eI : I ⋙ ED ≅ EC ⋙ I')
    (eJ : J ⋙ EF ≅ EE ⋙ J')
    (hP : ∀ N : F, EB.map (cP.hom.app N) ≫ eP₁.hom.app (P₂.obj N) ≫
      P₁'.map (eP₂.hom.app N) = eP₁₂.hom.app N ≫ cP'.hom.app (EF.obj N))
    (hR : ∀ N : E, EA.map (cR.hom.app N) ≫ eR₁.hom.app (R₂.obj N) ≫
      R₁'.map (eR₂.hom.app N) = eR₁₂.hom.app N ≫ cR'.hom.app (EE.obj N))
    (hA : ∀ N : C, EB.map (a.app N) ≫ eK.hom.app (R₁.obj N) ≫
      K'.map (eR₁.hom.app N) = eP₁.hom.app (I.obj N) ≫
        P₁'.map (eI.hom.app N) ≫ a'.app (EC.obj N))
    (hB : ∀ N : E, ED.map (b.app N) ≫ eI.hom.app (R₂.obj N) ≫
      I'.map (eR₂.hom.app N) = eP₂.hom.app (J.obj N) ≫
        P₂'.map (eJ.hom.app N) ≫ b'.app (EE.obj N))
    (hC : ∀ N : E, EB.map (c.app N) ≫ eK.hom.app (R₁₂.obj N) ≫
      K'.map (eR₁₂.hom.app N) = eP₁₂.hom.app (J.obj N) ≫
        P₁₂'.map (eJ.hom.app N) ≫ c'.app (EE.obj N))
    (hPasting : ∀ N : E', cP'.hom.app (J'.obj N) ≫
      P₁'.map (b'.app N) ≫ a'.app (R₂'.obj N) =
      c'.app N ≫ K'.map (cR'.hom.app N)) (N : E) :
    EB.map (cP.hom.app (J.obj N) ≫ P₁.map (b.app N) ≫ a.app (R₂.obj N)) =
      EB.map (c.app N ≫ K.map (cR.hom.app N)) := by
  sorry

end CategoryTheory
