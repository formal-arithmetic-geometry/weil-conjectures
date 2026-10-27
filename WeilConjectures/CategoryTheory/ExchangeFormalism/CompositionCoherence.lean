/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Composition
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Identity
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Pasting

/-!
# Coherence of the composition isomorphisms in an exchange formalism

Let `F` be a `CategoryTheory.ExchangeFormalism`. The composition isomorphism
`F.shriek i₁ p₁ ⋙ F.shriek i₂ p₂ ≅ F.shriek i p` of a triangle of factorizations
(`CategoryTheory.ExchangeFormalism.compIso`) satisfies the following coherences:

- **associativity** (`CategoryTheory.ExchangeFormalism.compIso_assoc`): for composable morphisms
  `A ⟶ B ⟶ C ⟶ D` with factorizations `A ⟶[i_f] Z_f ⟶[p_f] B`, `B ⟶[i_g] P_g ⟶[p_g] C`,
  `C ⟶[i_h] P_h ⟶[p_h] D` and a staircase of squares
  ```
  Z_f --a--> W_fg --e--> V
  |p_f       |b          |u
  B --i_g--> P_g --c---> W_gh
             |p_g        |d
             C ---i_h--> P_h
  ```
  the two composition isomorphisms `Rf_! ⋙ Rg_! ⋙ Rh_! ≅ R(fgh)_!` built from the four triangles
  of the staircase agree;
- **unit laws** (`CategoryTheory.ExchangeFormalism.compIso_unitLeft_hom_app`,
  `CategoryTheory.ExchangeFormalism.compIso_unitRight_hom_app`): for the triangles with the
  trivial factorization `X ⟶[𝟙] X ⟶[𝟙] X` of an identity, the composition isomorphism is
  `(𝟙)_* (𝟙)_! ≅ 𝟭`;
- **proper triangles** (`CategoryTheory.ExchangeFormalism.compIso_ofProper_hom_app`): for the
  trivial factorizations `X ⟶[𝟙] X ⟶[f] Y`, `Y ⟶[𝟙] Y ⟶[g] S` and `X ⟶[𝟙] X ⟶[f ≫ g] S`, the
  composition isomorphism is the composition isomorphism `(f ≫ g)_* ≅ f_* ⋙ g_*` of the
  pushforwards.
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section Assoc

variable {A B C D Zf Pg Ph Wfg Wgh V : 𝒞}
  (i_f : A ⟶ Zf) (p_f : Zf ⟶ B) (i_g : B ⟶ Pg) (p_g : Pg ⟶ C) (i_h : C ⟶ Ph) (p_h : Ph ⟶ D)
  (a : Zf ⟶ Wfg) (b : Wfg ⟶ Pg) (c : Pg ⟶ Wgh) (d : Wgh ⟶ Ph) (e : Wfg ⟶ V) (u : V ⟶ Wgh)
  (ifg : A ⟶ Wfg) (pfg : Wfg ⟶ C) (igh : B ⟶ Wgh) (pgh : Wgh ⟶ D) (ae : Zf ⟶ V) (ud : V ⟶ Ph)
  (i4 : A ⟶ V) (p4 : V ⟶ D)
  [Fact (𝒪 i_f)] [Fact (𝒪 i_g)] [Fact (𝒪 i_h)] [Fact (𝒪 a)] [Fact (𝒪 c)] [Fact (𝒪 e)]
  [Fact (𝒪 ifg)] [Fact (𝒪 igh)] [Fact (𝒪 ae)] [Fact (𝒪 i4)]
  (hifg : i_f ≫ a = ifg) (hpfg : b ≫ p_g = pfg) (high : i_g ≫ c = igh) (hpgh : d ≫ p_h = pgh)
  (hae : a ≫ e = ae) (hud : u ≫ d = ud) (hi4 : ifg ≫ e = i4) (hi4' : i_f ≫ ae = i4)
  (hp4 : ud ≫ p_h = p4) (hp4' : u ≫ pgh = p4)
  (S₁ : p_f ≫ i_g = a ≫ b) (S₂ : p_g ≫ i_h = c ≫ d) (S₃ : b ≫ c = e ≫ u)
  (S₃₂ : pfg ≫ i_h = e ≫ ud) (S₁₃ : p_f ≫ igh = ae ≫ u)

/-- **Associativity of the composition isomorphisms.** For a staircase of squares
```
Z_f --a--> W_fg --e--> V
|p_f       |b          |u
B --i_g--> P_g --c---> W_gh
           |p_g        |d
           C ---i_h--> P_h
```
with `S₁ : p_f ≫ i_g = a ≫ b`, `S₂ : p_g ≫ i_h = c ≫ d`, `S₃ : b ≫ c = e ≫ u`, the triangles
`T₁ = (i_f, p_f; i_g, p_g; a, b)` of `(f, g)`, `T₂ = (i_g, p_g; i_h, p_h; c, d)` of `(g, h)`,
`T₃ = (i_f ≫ a, b ≫ p_g; i_h, p_h; e, u ≫ d)` of `(f ≫ g, h)` and
`T₄ = (i_f, p_f; i_g ≫ c, d ≫ p_h; a ≫ e, u)` of `(f, g ≫ h)` give the same identification of
`F.shriek i4 p4` with `F.shriek i_f p_f ⋙ F.shriek i_g p_g ⋙ F.shriek i_h p_h`. -/
theorem compIso_assoc
    [IsIso (F.baseChange p_f a i_g b S₁).natTrans] [IsIso (F.exchange p_f a i_g b S₁).natTrans]
    [IsIso (F.baseChange p_g c i_h d S₂).natTrans] [IsIso (F.exchange p_g c i_h d S₂).natTrans]
    [IsIso (F.baseChange b e c u S₃).natTrans] [IsIso (F.exchange b e c u S₃).natTrans]
    [IsIso (F.baseChange pfg e i_h ud S₃₂).natTrans]
    [IsIso (F.exchange pfg e i_h ud S₃₂).natTrans]
    [IsIso (F.baseChange p_f ae igh u S₁₃).natTrans]
    [IsIso (F.exchange p_f ae igh u S₁₃).natTrans] (M : F.obj A) :
    (F.compIso (⟨Wfg, Ph, V, ifg, pfg, i_h, p_h, i4, p4, e, ud, hi4, hp4, S₃₂⟩ :
        ShriekTriangle 𝒪 A C D)).inv.app M ≫
      (F.shriek i_h p_h).map ((F.compIso (⟨Zf, Pg, Wfg, i_f, p_f, i_g, p_g, ifg, pfg, a, b,
        hifg, hpfg, S₁⟩ : ShriekTriangle 𝒪 A B C)).inv.app M) =
    (F.compIso (⟨Zf, Wgh, V, i_f, p_f, igh, pgh, i4, p4, ae, u, hi4', hp4', S₁₃⟩ :
        ShriekTriangle 𝒪 A B D)).inv.app M ≫
      (F.compIso (⟨Pg, Ph, Wgh, i_g, p_g, i_h, p_h, igh, pgh, c, d, high, hpgh, S₂⟩ :
        ShriekTriangle 𝒪 B C D)).inv.app ((F.shriek i_f p_f).obj M) :=
  sorry

end Assoc

section Unit

variable [𝒪.ContainsIdentities] {X Y Z : 𝒞} (i : X ⟶ Z) (p : Z ⟶ Y) [Fact (𝒪 i)]

/-- **The left unit law of the composition isomorphisms.** For the triangle
`((𝟙, 𝟙); (i, p); i, 𝟙)` of `(𝟙 X, f)`, with `X ⟶[i] Z ⟶[p] Y` a factorization of `f`, the
composition isomorphism `F.shriek (𝟙 X) (𝟙 X) ⋙ F.shriek i p ≅ F.shriek i p` is induced by
`(𝟙 X)_* (𝟙 X)_! ≅ 𝟭`. -/
theorem compIso_unitLeft_hom_app (w : 𝟙 X ≫ i = i ≫ 𝟙 Z)
    [IsIso (F.baseChange (𝟙 X) i i (𝟙 Z) w).natTrans]
    [IsIso (F.exchange (𝟙 X) i i (𝟙 Z) w).natTrans] (M : F.obj X) :
    (F.compIso (⟨X, Z, Z, 𝟙 X, 𝟙 X, i, p, i, p, i, 𝟙 Z, Category.id_comp i,
        Category.id_comp p, w⟩ : ShriekTriangle 𝒪 X X Y)).hom.app M =
      (F.shriek i p).map ((F.pf (𝟙 X)).map ((F.shId X).hom.app M) ≫ (F.pfId X).hom.app M) :=
  sorry

/-- **The right unit law of the composition isomorphisms.** For the triangle
`((i, p); (𝟙, 𝟙); 𝟙, p)` of `(f, 𝟙 Y)`, with `X ⟶[i] Z ⟶[p] Y` a factorization of `f`, the
composition isomorphism `F.shriek i p ⋙ F.shriek (𝟙 Y) (𝟙 Y) ≅ F.shriek i p` is induced by
`(𝟙 Y)_* (𝟙 Y)_! ≅ 𝟭`. -/
theorem compIso_unitRight_hom_app (w : p ≫ 𝟙 Y = 𝟙 Z ≫ p)
    [IsIso (F.baseChange p (𝟙 Z) (𝟙 Y) p w).natTrans]
    [IsIso (F.exchange p (𝟙 Z) (𝟙 Y) p w).natTrans] (M : F.obj X) :
    (F.compIso (⟨Z, Y, Z, i, p, 𝟙 Y, 𝟙 Y, i, p, 𝟙 Z, p, Category.comp_id i,
        Category.comp_id p, w⟩ : ShriekTriangle 𝒪 X Y Y)).hom.app M =
      (F.pf (𝟙 Y)).map ((F.shId Y).hom.app ((F.shriek i p).obj M)) ≫
        (F.pfId Y).hom.app ((F.shriek i p).obj M) :=
  sorry

end Unit

section Proper

variable [𝒪.ContainsIdentities] {X Y S : 𝒞} (f : X ⟶ Y) (g : Y ⟶ S) (fg : X ⟶ S)
  (hfg : f ≫ g = fg)

/-- **The composition isomorphism of trivial factorizations.** For the triangle
`((𝟙, f); (𝟙, g); 𝟙, f)` of `(f, g)` with the trivial factorizations `X ⟶[𝟙] X ⟶[f] Y`,
`Y ⟶[𝟙] Y ⟶[g] S` and `X ⟶[𝟙] X ⟶[f ≫ g] S`, the composition isomorphism is, through
`(𝟙 Y)_! ≅ 𝟭`, the composition isomorphism `(f ≫ g)_* ≅ f_* ⋙ g_*` of the pushforwards. -/
theorem compIso_ofProper_hom_app (w : f ≫ 𝟙 Y = 𝟙 X ≫ f)
    [IsIso (F.baseChange f (𝟙 X) (𝟙 Y) f w).natTrans]
    [IsIso (F.exchange f (𝟙 X) (𝟙 Y) f w).natTrans] (M : F.obj X) :
    (F.compIso (⟨X, Y, X, 𝟙 X, f, 𝟙 Y, g, 𝟙 X, fg, 𝟙 X, f, Category.id_comp _, hfg, w⟩ :
        ShriekTriangle 𝒪 X Y S)).hom.app M =
      (F.pf g).map ((F.shId Y).hom.app ((F.pf f).obj ((F.sh (𝟙 X)).obj M))) ≫
        (F.pfComp' f g fg hfg).inv.app ((F.sh (𝟙 X)).obj M) :=
  sorry

end Proper

end CategoryTheory.ExchangeFormalism
