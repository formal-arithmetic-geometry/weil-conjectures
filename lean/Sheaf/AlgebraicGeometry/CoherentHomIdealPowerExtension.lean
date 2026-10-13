/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # HOM ideal-power comparison over an open complement

Source: Stacks Project, Cohomology of Schemes, Lemma 01YB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A morphism on the complement extends after multiplying its coherent source by an
ideal power. This is only the surjectivity assertion, with the complement fixed in advance.

Proof: X is Noetherian, so it is quasi-separated, U is quasi-compact, and I is of finite
type. First treat G = O_X and write s for the image of 1. The image of the map defined
by s on U is quasi-coherent of finite type. Extend it to a finite-type quasi-coherent
submodule E of F; E is coherent and s belongs to E(U). The increasing submodules E_N
annihilated by I^N stabilize at H = E_a, with I^a H = 0. Artin--Rees gives c such that
I^b E meets H in a submodule of I^(b-c) H for b >= c. Taking b = a+c gives
E' = I^b E with E' intersect H = 0 and E'|U = E|U. Every ideal-power annihilator
of E' is zero, since E_N is contained in H for every N. The sections-over-a-quasi-
compact-open comparison identifies the colimit of Hom(I^N, E'/E'_N) with E'(U).
Here E'_N = 0, so a finite-stage representative of s gives I^N -> E' -> E -> F,
with value s on 1 over U. For general coherent G, its internal
Hom into F is quasi-coherent because G is finitely presented. Apply the structure-sheaf
case to this internal Hom and use tensor--Hom adjunction to obtain a map from I^n ⊗ G.
The multiplication map to G has image I^n G, and its kernel K is killed by I^n,
as follows on affines: put J = I^n and write z = sum b_i ⊗ m_i in the kernel,
so sum b_i m_i = 0. For a in J, tensor balancing gives
 a z = sum a ⊗ (b_i m_i) = a ⊗ 0 = 0.
Artin--Rees gives an m for which I^m(I^n ⊗ G) meets K in
zero. Multiplication identifies that submodule with I^(n+m)G; restricting the lifted
map to it gives the required extension. On U multiplication by 1 shows that its
restriction is the original map. Empty complements and zero modules obey the same
argument; the exponent may be zero.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB, surjectivity paragraphs.
(blueprint: lem-weil-pbc-coherent-hom-ideal-power-extension). -/
theorem coherent_hom_ideal_power_extension {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom) :
    ∀ ψ : (SheafOfModules.overFunctor X.ringCatSheaf U).obj G ⟶
        (SheafOfModules.overFunctor X.ringCatSheaf U).obj F,
      ∃ (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F),
        (SheafOfModules.overFunctor X.ringCatSheaf U).map
            (idealModuleProductι (idealSheafPower I.toModulesι n).2 G) ≫ ψ =
          (SheafOfModules.overFunctor X.ringCatSheaf U).map χ := by sorry

end AlgebraicGeometry.Scheme
