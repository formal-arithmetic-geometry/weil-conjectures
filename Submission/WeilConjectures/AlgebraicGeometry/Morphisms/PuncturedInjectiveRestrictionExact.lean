/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedInjectiveRestrictionKernel
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.InjectiveModuleTildeFlasque

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Restricting an injective module to the puncture

Source: Stacks Project, Tags 09T2 and 0A6T.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
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
      Function.Surjective (tilde.toOpen M W) := by
  refine ⟨injective_punctured_restriction_kernel R W hW M,
    ?_⟩
  let := injective_tilde_isFlasque R M
  let F := (modulesSpecToSheaf.obj (tilde (R := .of R) M)).presheaf
  have hs : Function.Surjective (F.map (homOfLE (show W ≤ ⊤ from le_top)).op) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have ht : Function.Surjective (tilde.toOpen (R := .of R) M ⊤) :=
    by
      change Function.Surjective (tilde.isoTop (R := .of R) M).hom
      exact (ConcreteCategory.bijective_of_isIso _).surjective
  intro s
  obtain ⟨t, ht'⟩ := hs s
  obtain ⟨x, hx⟩ := ht t
  refine ⟨x, ?_⟩
  have he := congrArg (fun f ↦ f x)
    (tilde.toOpen_res (R := .of R) M ⊤ W (homOfLE le_top))
  change F.map (homOfLE (show W ≤ ⊤ from le_top)).op
    (tilde.toOpen (R := .of R) M ⊤ x) = tilde.toOpen M W x at he
  rw [hx, ht'] at he
  exact he.symm

end AlgebraicGeometry.Scheme
