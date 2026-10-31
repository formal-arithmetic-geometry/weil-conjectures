/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDgModules
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Quotient
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-!
# Homotopy triangulation and quasi-isomorphism system for sheaf dg modules

Source: Stacks Project, `sdga.tex`, Tags 0FS7, 0FT2 and 0FT4, with the cone
convention of Tag 0FS5 (blueprint: lem-sfb-sheaf-dg-homotopy-system).

The declarations below record the right-module homotopy quotient, its signed
shifts and mapping-cone triangles, and the localization data used by the
sheaf dg scalar-adjunction theorem.  They use the canonical ringed-site dg
module and sheaf tensor declarations; no second module category is defined.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite CategoryTheory.Pretriangulated

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u})

variable {O}

/-- Right graded linearity of a degree `-1` homotopy. Source: Stacks `sdga.tex`,
section-homotopy (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
def homotopyRightLinear {A : Algebra O} {M N : Module A}
    {f g : M ⟶ N} (h : Homotopy ((underlying A).map f) ((underlying A).map g)) : Prop :=
  ∀ (p q : ℤ), HEq
    (actionDegree M p q (p + q) rfl ≫ h.hom (p + q) (p + q - 1))
    ((h.hom p (p - 1) ▷ A.X.X q) ≫
      actionDegree N (p - 1) q ((p - 1) + q) rfl)

/-- The action-preserving chain-homotopy relation on right dg modules. Source:
Stacks `sdga.tex`, definition-homotopy (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
def homotopyRel (A : Algebra O) : HomRel (Module A) :=
  fun _M _N f g ↦ ∃ h : Homotopy ((underlying A).map f) ((underlying A).map g),
    homotopyRightLinear h

/-- The right dg-module homotopy category `K(A)`. Source: Stacks `sdga.tex`,
section-homotopy (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
abbrev HomotopyCategory (A : Algebra O) :=
  CategoryTheory.Quotient (homotopyRel A)

/-- The quotient functor from right dg modules to `K(A)`. Source: Stacks `sdga.tex`,
section-homotopy (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
abbrev homotopyQuotient (A : Algebra O) : Module A ⥤ HomotopyCategory A :=
  CategoryTheory.Quotient.functor (homotopyRel A)

/-- Signed shifts and the specified mapping-cone triangles on `K(A)`. Source:
Stacks `sdga.tex`, Tags 0FRY, 0FS5 and 0FS7 (blueprint: lem-sfb-sheaf-dg-homotopy-system).
-/
class HomotopyStructure (A : Algebra O) where
  [preadditive : Preadditive (HomotopyCategory A)]
  [zero : HasZeroObject (HomotopyCategory A)]
  [shift : HasShift (HomotopyCategory A) ℤ]
  [shiftAdditive : ∀ n : ℤ, (shiftFunctor (HomotopyCategory A) n).Additive]
  [pretriangulated : Pretriangulated (HomotopyCategory A)]
  [triangulated : IsTriangulated (HomotopyCategory A)]
  shifts_exist (n : ℤ) (M : Module A) :
    ∃ S : Module A, Nonempty (ShiftComparison A n M S)
  cones_exist {M N : Module A} (f : M ⟶ N) :
    ∃ (K S : Module A) (s : ShiftComparison A 1 M S) (g : N ⟶ K) (h : K ⟶ S),
      Nonempty (ConeComparison A f K S s g h)
  shiftIso (n : ℤ) (M S : Module A) (e : ShiftComparison A n M S) :
    (homotopyQuotient A).obj S ≅ ((homotopyQuotient A).obj M)⟦n⟧
  shift_natural (n : ℤ) (M N S V : Module A)
      (eM : ShiftComparison A n M S) (eN : ShiftComparison A n N V)
      (f : M ⟶ N) (g : S ⟶ V)
      (comm : (underlying A).map g ≫ eN.iso.hom =
        eM.iso.hom ≫ ((underlying A).map f)⟦n⟧') :
    (homotopyQuotient A).map g ≫ (shiftIso n N V eN).hom =
      (shiftIso n M S eM).hom ≫ ((homotopyQuotient A).map f)⟦n⟧'
  distinguished_iff (t : Triangle (HomotopyCategory A)) : t ∈ distTriang (HomotopyCategory A) ↔
    ∃ (M N K S : Module A) (f : M ⟶ N) (s : ShiftComparison A 1 M S)
      (g : N ⟶ K) (h : K ⟶ S),
      Nonempty (ConeComparison A f K S s g h) ∧
      Nonempty (t ≅ Triangle.mk ((homotopyQuotient A).map f) ((homotopyQuotient A).map g)
        ((homotopyQuotient A).map h ≫ (shiftIso 1 M S s).hom))

attribute [instance_reducible] HomotopyStructure.preadditive HomotopyStructure.shift
  HomotopyStructure.pretriangulated

attribute [instance] HomotopyStructure.preadditive HomotopyStructure.zero
  HomotopyStructure.shift HomotopyStructure.shiftAdditive HomotopyStructure.pretriangulated
  HomotopyStructure.triangulated

/-- The complete sheaf dg homotopy/localization package. Its fields render the
cohomology, cone criterion, saturated triangulated calculus, and two-out-of-three
clauses of the node statement. Source: Stacks `sdga.tex`, Tags 0FS7, 0FT2 and
0FT4 (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
class HomotopySystem (A : Algebra O) extends HomotopyStructure A where
  cohomology (n : ℤ) : HomotopyCategory A ⥤ Coeff O
  cohomology_factors (n : ℤ) :
    homotopyQuotient A ⋙ cohomology n =
      underlying A ⋙ HomologicalComplex.homologyFunctor (Coeff O) (ComplexShape.up ℤ) n
  W : MorphismProperty (HomotopyCategory A)
  W_iff_cohomology (X Y : HomotopyCategory A) (f : X ⟶ Y) :
    W f ↔ ∀ n : ℤ, IsIso ((cohomology n).map f)
  W_saturated : W.IsSaturatedTriangulatedMultiplicativeSystem
  W_two_of_three {X Y Z : HomotopyCategory A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (W f ∧ W g → W (f ≫ g)) ∧
    (W f ∧ W (f ≫ g) → W g) ∧
    (W g ∧ W (f ≫ g) → W f)
  cone_criterion {M N : Module A} (f : M ⟶ N)
      (K S : Module A) (s : ShiftComparison A 1 M S)
      (g : N ⟶ K) (h : K ⟶ S) ( _hc : ConeComparison A f K S s g h) :
    W ((homotopyQuotient A).map f) ↔
      ∀ n : ℤ, IsZero ((cohomology n).obj ((homotopyQuotient A).obj K))

/-- The dg construction supplies the homotopy-category structure. This is the triangulation
part of the Stacks 0FS4--0FS7 argument, separated from cohomology and localization.
Source: Stacks `sdga.tex`, Tags 0FS4--0FS7, with dga Tags 09QY and 09QU
(blueprint: lem-sfb-sheaf-dg-homotopy-structure-existence).

Proof: (1) right dg modules form a dg category: degree-`r` maps are families
`u^j : M^j → N^{j+r}` with `u(ma) = u(m)a`, and `∂u = d_N u - (-1)^r u d_M` is again right
linear (the two `d(a)` terms cancel), `∂² = 0` and `∂` is a graded derivation of composition;
closed degree-zero maps are chain maps and boundaries are `dh + hd` with `h` right linear, so
`H⁰` is `HomotopyCategory A`. The zero module and degreewise sums give axiom (A).
(2) Axiom (B): `M[k]^j = M^{j+k}` with differential `(-1)^k d_M` and unchanged action, and
`u[k] = (-1)^{kr} u` on degree-`r` maps; this is a dg functor, the shifts compose by addition
and `Hom(M, N[k]) ≅ Hom(M, N)[k]` compatibly with composition. These are the modules `S` of
`ShiftComparison`. (3) Axiom (C): the cone `C(f)^i = N^i ⊕ M^{i+1}`,
`d(n, m) = (dn + f m, -dm)`, with componentwise action, is a right dg module; the sequence
`N → C(f) → M[1]` is graded split by `s(m) = (0, m)`, `π(n, m) = n`, with boundary
`π ∂ s = f`. These are the modules `K` of `ConeComparison`. (4) The generic ABC theorem
(Stacks dga 09QY, 09QU) makes `H⁰` triangulated with these shifts, and its distinguished
triangles are exactly those isomorphic to `M → N → C(f) → M[1]` with third map `-p`; this
gives the fields `shiftIso`, `shift_natural` and `distinguished_iff`. -/
theorem homotopy_structure_exists
    (O : Sheaf J CommRingCat.{u}) (A : Algebra O) :
    Nonempty (HomotopyStructure A) := by
  sorry

/-- The cohomology and localization fields of `HomotopySystem`, for a given
`HomotopyStructure`. Source: Stacks `sdga.tex`, Tags 0FT2 and 0FT4
(blueprint: lem-sfb-sheaf-dg-homotopy-system-fields). -/
structure HomotopySystemFields (A : Algebra O) [HomotopyStructure A] where
  cohomology (n : ℤ) : HomotopyCategory A ⥤ Coeff O
  cohomology_factors (n : ℤ) :
    homotopyQuotient A ⋙ cohomology n =
      underlying A ⋙ HomologicalComplex.homologyFunctor (Coeff O) (ComplexShape.up ℤ) n
  W : MorphismProperty (HomotopyCategory A)
  W_iff_cohomology (X Y : HomotopyCategory A) (f : X ⟶ Y) :
    W f ↔ ∀ n : ℤ, IsIso ((cohomology n).map f)
  W_saturated : W.IsSaturatedTriangulatedMultiplicativeSystem
  W_two_of_three {X Y Z : HomotopyCategory A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (W f ∧ W g → W (f ≫ g)) ∧
    (W f ∧ W (f ≫ g) → W g) ∧
    (W g ∧ W (f ≫ g) → W f)
  cone_criterion {M N : Module A} (f : M ⟶ N)
      (K S : Module A) (s : ShiftComparison A 1 M S)
      (g : N ⟶ K) (h : K ⟶ S) ( _hc : ConeComparison A f K S s g h) :
    W ((homotopyQuotient A).map f) ↔
      ∀ n : ℤ, IsZero ((cohomology n).obj ((homotopyQuotient A).obj K))

/-- The cohomological localization clauses for the homotopy category, for any
`HomotopyStructure` on it.
Source: Stacks `sdga.tex`, Tags 0FT2 and 0FT4; derived Tags 05R5 and 05RG
(blueprint: lem-sfb-sheaf-dg-homotopy-system-fields).

Proof: (0) the given structure is the standard one up to the data used below: a pretriangulated
category has finite biproducts, so its preadditive structure is the unique semiadditive one;
`shiftIso` and `shift_natural` identify `(Q M)⟦n⟧` and `(Q f)⟦n⟧` with the quotient images of
shifted modules; `distinguished_iff` identifies the distinguished triangles with the cone
triangles. (1) Underlying homology `H^n` inverts nothing but respects action-preserving
homotopies (`(f - g)x = d(hx)` on cycles), so it descends along the quotient `Q`, which is
the identity on objects and full; this gives `cohomology n` with `cohomology_factors`.
(2) Forgetting the action is an exact functor to the ordinary homotopy category of
`Coeff O`-complexes (it preserves sums, the shifts and the cone triangles), whose homology is
homological; hence `H⁰` on `HomotopyCategory A` is homological with `H^n = H⁰ ∘ ⟦n⟧`.
(3) Put `W f ↔ ∀ n, IsIso (H^n f)`. By the homological-kernel leaf the full subcategory of
acyclic objects is triangulated and its cone class is `W`; the triangulated-subcategory
cone-system theorem gives the multiplicative system, both calculi of fractions and
compatibility with the triangulation. (4) Saturation: if `fg` and `gh` lie in `W`, then in
each degree `H(g)` has a left and a right inverse, so `g ∈ W`; two-out-of-three is degreewise
for isomorphisms. (5) Cone criterion: the long exact homology sequence of
`M → N → C(f) → M[1]` shows all `H^n(f)` invertible iff all `H^n(C(f))` vanish. -/
theorem homotopy_system_fields_exists
    (O : Sheaf J CommRingCat.{u}) (A : Algebra O) [HomotopyStructure A] :
    Nonempty (HomotopySystemFields A) := by
  sorry

/-- Homotopy triangulation and quasi-isomorphism system for sheaf dg modules.
Source: Stacks `sdga.tex`, Tags 0FS7, 0FT2 and 0FT4, with the cone convention
of Tag 0FS5 (blueprint: lem-sfb-sheaf-dg-homotopy-system).

The package supplies the dg homotopy category of right modules, the signed shift
`M[k]^i = M^{i+k}` with differential `(-1)^k d_M` and unchanged action, the
specified cone `C(f)^i = N^i ⊕ M^{i+1}` with differential
`(dn + f(m), -dm)` and arrows `i` and `-p`, its cohomology functors, and the
class `W` of quasi-isomorphisms. `W_saturated` gives both fraction calculi and
triangulation compatibility; `W_two_of_three` gives two-out-of-three, and
`cone_criterion` identifies `W` with acyclic specified cones. No boundedness or
graded-commutativity assumption is imposed.

Proof plan:
1. Form the dg category of right modules: degree-`r` maps are families
`u^j : M^j → N^(j+r)` with `u(ma) = u(m)a`, and `∂u = d_N u - (-1)^r u d_M`. The two
`d(a)` terms in `∂u(ma)` cancel, `∂² = 0` and `∂` is a graded derivation. Closed
degree-zero maps are chain maps and boundaries of degree `-1` maps are `dh + hd`, so
`H^0` of this dg category is `K(A)`. The zero module and degreewise sums give dg zero
and biproducts; sets are taken in a larger universe (def-weil-size-convention,
def-weil-sheaf-of-modules-category; Stacks 0FS4).
2. Shift by `M[k]^j = M^(j+k)` with differential `(-1)^k d_M` and the same action; on a
degree-`r` map put `u[k] = (-1)^(kr) u`. Then `∂(u[k]) = (∂u)[k]`, composition and the
Hom reindexing are compatible, and closed degree-zero maps get no extra sign
(Stacks 0FRY with the corrected homogeneous-map sign; 0FS4).
3. For a chain map `f` the displayed cone with componentwise action is a right dg module;
`N → C(f) → M[1]` has graded splitting `s(m) = (0,m)`, `π(n,m) = n`, and
`π d s = f` represents `f[1]`, which is axiom (C) for this exact cone (Stacks 0FS5, 0FS6).
4. The ABC triangulation theorem gives the triangulation of `K(A)` with these shifts and
distinguished triangles those isomorphic to `(M, N, C(f), f, i, -p)` (Stacks 0FS7).
5. Forgetting the action is a triangulated functor `K(A) → K(Mod(O))`
(lem-pur-homotopy-category-triangulated); composing with the localization and derived
cohomology (def-weil-abstract-derived-category) gives the underlying cohomology sheaves,
which are functors on `K(A)`, and `H^0` is homological by lem-sf-derived-homology-long-exact
with `H^n(M) = H^0(M[n])` (Stacks 0FT2).
6. lem-sfb-homological-kernel-cone-detection identifies the kernel of `H^0`, the acyclic
modules, as a replete triangulated subcategory whose cone class is `W`;
lem-trf-triangulated-subcategory-cone-system gives multiplicativity, both calculi of
fractions and compatibility with the triangulation (Stacks 0FT4).
7. The long exact cohomology sequence of the specified cone triangle shows `f ∈ W` iff
`C(f)` is acyclic. Two-out-of-three holds degreewise for isomorphisms, and if `fg` and
`gh` lie in `W` then each `H(g)` has a left and a right inverse, so `g ∈ W`; with step 6
these are all clauses of def-pur-saturated-triangulated-localization.
-/
theorem sheaf_dg_homotopy_system
    (O : Sheaf J CommRingCat.{u}) (A : Algebra O) :
    Nonempty (HomotopySystem A) := by
  obtain ⟨hs⟩ := homotopy_structure_exists O A
  letI : HomotopyStructure A := hs
  obtain ⟨hf⟩ := homotopy_system_fields_exists O A
  exact ⟨HomotopySystem.mk hf.cohomology hf.cohomology_factors hf.W
    hf.W_iff_cohomology hf.W_saturated hf.W_two_of_three hf.cone_criterion⟩

end CategoryTheory.RingedSiteDg
