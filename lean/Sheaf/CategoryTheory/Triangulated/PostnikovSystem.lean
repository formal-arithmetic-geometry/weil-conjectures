module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Order.WithBot

/-! # Postnikov systems of complexes in a triangulated category

Source: Stacks Project, derived.tex, Tag 0D7Z and example-key-postnikov
(blueprint: def-sfb-postnikov-system).

The bound `N : WithTop ℕ` treats finite initial segments and the countable system uniformly.
The degree-zero identification is an equality, so its structure map is the identity after
transport. Restriction retains the actual objects and arrows, including the connecting arrows.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Postnikov data through `N`, normalized at degree zero. The triangle at index `r`
corresponds to the paper's triangle at `r + 1`.
Source: Stacks Tag 0D7Z (blueprint: def-sfb-postnikov-system). -/
structure PostnikovSystem (K : ChainComplex C ℕ) (N : WithTop ℕ) where
  Y (r : ℕ) (hr : (r : WithTop ℕ) ≤ N) : C
  a (r : ℕ) (hr : (r : WithTop ℕ) ≤ N) : Y r hr ⟶ K.X r
  zero_eq : Y 0 bot_le = K.X 0
  a_zero : a 0 bot_le = eqToHom zero_eq
  b (r : ℕ) (hr : ((r + 1 : ℕ) : WithTop ℕ) ≤ N) :
    K.X (r + 1) ⟶ Y r (le_trans (by exact_mod_cast Nat.le_succ r) hr)
  c (r : ℕ) (hr : ((r + 1 : ℕ) : WithTop ℕ) ≤ N) :
    Y r (le_trans (by exact_mod_cast Nat.le_succ r) hr) ⟶ Y (r + 1) hr⟦(1 : ℤ)⟧
  distinguished (r : ℕ) (hr : ((r + 1 : ℕ) : WithTop ℕ) ≤ N) :
    Triangle.mk (a (r + 1) hr) (b r hr) (c r hr) ∈ distTriang C
  differential (r : ℕ) (hr : ((r + 1 : ℕ) : WithTop ℕ) ≤ N) :
    b r hr ≫ a r (le_trans (by exact_mod_cast Nat.le_succ r) hr) = K.d (r + 1) r

/-- Restrict a Postnikov system, retaining every object and every arrow in the segment.
Source: Stacks Tag 0D7Z (blueprint: def-sfb-postnikov-system). -/
def PostnikovSystem.restrict {K : ChainComplex C ℕ} {N M : WithTop ℕ}
    (P : PostnikovSystem K N) (h : M ≤ N) : PostnikovSystem K M where
  Y r hr := P.Y r (le_trans hr h)
  a r hr := P.a r (le_trans hr h)
  zero_eq := P.zero_eq
  a_zero := P.a_zero
  b r hr := P.b r (le_trans hr h)
  c r hr := P.c r (le_trans hr h)
  distinguished r hr := P.distinguished r (le_trans hr h)
  differential r hr := P.differential r (le_trans hr h)

/-- A map over the given chain map consists of all three commuting triangle squares,
with its degree-zero component equal to the chain map after the specified transports.
Source: Stacks Tag 0D7Z (blueprint: def-sfb-postnikov-system). -/
structure PostnikovSystem.Hom {K L : ChainComplex C ℕ} (u : K ⟶ L)
    {N : WithTop ℕ} (P : PostnikovSystem K N) (Q : PostnikovSystem L N) where
  app (r : ℕ) (hr : (r : WithTop ℕ) ≤ N) : P.Y r hr ⟶ Q.Y r hr
  zero_app : app 0 bot_le = eqToHom P.zero_eq ≫ u.f 0 ≫ eqToHom Q.zero_eq.symm
  comm_a (r : ℕ) (hr : (r : WithTop ℕ) ≤ N) :
    app r hr ≫ Q.a r hr = P.a r hr ≫ u.f r
  comm_b (r : ℕ) (hr : ((r + 1 : ℕ) : WithTop ℕ) ≤ N) :
    P.b r hr ≫ app r (le_trans (by exact_mod_cast Nat.le_succ r) hr) =
      u.f (r + 1) ≫ Q.b r hr
  comm_c (r : ℕ) (hr : ((r + 1 : ℕ) : WithTop ℕ) ≤ N) :
    P.c r hr ≫ (app (r + 1) hr)⟦(1 : ℤ)⟧' =
      app r (le_trans (by exact_mod_cast Nat.le_succ r) hr) ≫ Q.c r hr

/-- Restriction of a comparison map retains its components on the smaller segment.
Source: Stacks Tag 0D7Z (blueprint: def-sfb-postnikov-system). -/
def PostnikovSystem.Hom.restrict {K L : ChainComplex C ℕ} {u : K ⟶ L}
    {N M : WithTop ℕ} {P : PostnikovSystem K N} {Q : PostnikovSystem L N}
    (g : PostnikovSystem.Hom u P Q) (h : M ≤ N) :
    PostnikovSystem.Hom u (P.restrict h) (Q.restrict h) where
  app r hr := g.app r (le_trans hr h)
  zero_app := g.zero_app
  comm_a r hr := g.comm_a r (le_trans hr h)
  comm_b r hr := g.comm_b r (le_trans hr h)
  comm_c r hr := g.comm_c r (le_trans hr h)

/-- The actual connecting arrow between successive shifted Postnikov vertices, with
Mathlib's shift-addition isomorphism supplying the associativity identification.
Source: Stacks example-key-postnikov (blueprint: def-sfb-postnikov-system). -/
def PostnikovSystem.connecting {K : ChainComplex C ℕ} {N : WithTop ℕ}
    (P : PostnikovSystem K N) (r : ℕ) (hr : ((r + 1 : ℕ) : WithTop ℕ) ≤ N) :
    (P.Y r (le_trans (by exact_mod_cast Nat.le_succ r) hr))⟦(r : ℤ)⟧ ⟶
      (P.Y (r + 1) hr)⟦((r + 1 : ℕ) : ℤ)⟧ :=
  (P.c r hr)⟦(r : ℤ)⟧' ≫
    (shiftFunctorAdd' C (1 : ℤ) (r : ℤ) ((r + 1 : ℕ) : ℤ)
      (by omega)).inv.app (P.Y (r + 1) hr)

end CategoryTheory.Triangulated
