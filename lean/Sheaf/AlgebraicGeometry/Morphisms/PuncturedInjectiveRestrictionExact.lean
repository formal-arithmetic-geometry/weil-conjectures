/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Restricting an injective module to the puncture

Source: Stacks Project, Tags 09T2 and 0A6T.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Restriction of an injective module to the puncture is surjective, with kernel
its maximal-ideal-power torsion submodule.
Source: Stacks Project, Tag 09T2, Lemma 36.8.1, and Tag 0A6T, Lemma 51.2.1.
(blueprint: lem-sbc-punctured-injective-restriction-exact).

Proof: A prime containing m equals m, so W is Spec R minus V(m). Noetherianity
provides finite generators f_i of m. For any module M, a section of M vanishes
on W exactly when its images in all the localizations M[f_i^-1] vanish. Each
vanishing gives an exponent e_i with f_i^e_i killing it. Increase each exponent
to be positive. Every monomial of degree sum e_i contains one f_i^e_i, so
m^(sum e_i) annihilates the section. Conversely, if m^N annihilates a section,
then f_i^N does, hence it vanishes on D(f_i). These opens cover W, proving the
kernel equality with Ideal.primaryComponent. Injectivity of M corresponds,
under the exact equivalence between R-modules and quasi-coherent sheaves on
Spec R, to injectivity of its associated quasi-coherent sheaf. It is flasque
by 09T2. Therefore its sections on Spec R surject onto its sections on W.
The isomorphism tilde.isoTop identifies the former with M and this restriction
with tilde.toOpen M W. When m=0, W is empty and the primary component is all
of M; both claims hold. An empty W for an Artinian local ring is likewise
covered by the kernel argument (a power of m is zero). -/
theorem injective_punctured_restriction_exact
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (M : ModuleCat.{u} R) [Injective M] :
    (tilde.toOpen M W).hom.ker = Ideal.primaryComponent M (IsLocalRing.maximalIdeal R) ∧
      Function.Surjective (tilde.toOpen M W) := by sorry

end AlgebraicGeometry.Scheme
