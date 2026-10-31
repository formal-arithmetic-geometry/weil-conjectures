/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

/-- Reverse half of the normalized extension-kernel criterion: if some integral
witness `h` makes `R.algebraic(M, h)` kill every `g` with
`pullbackPathHom j b (eG g) = 1`, then `M` is the pullback of a lisse module on `C`.

Source: rem-dl-a1-conventions, the unramified-at-infinity equivalence (proof steps
of lem-dl-a1-condensed-lisse-extension-inertia); steps 1-2, the converse half of
step 3 and step 4 of lem-dl-a1-condensed-lisse-extension-kernel.
(blueprint: lem-dl-a1-condensed-lisse-extension-kernel-reverse).

Proof: as in the forward half, `U` and `C` are connected regular Noetherian curves,
lisse modules have integral models, and thm-lisse-qlbar-representations gives a
correspondence `R_C` on `C` for a small profinite model `H` of `Aut (fiber (b ≫ j))`;
the finite-level comparison of the forward half shows that the normalized action
on `j^* L` is that of `L` composed with `q = pullbackPathHom j b ∘ eG`.
The map `q : G → H` is continuous and surjective by lem-wf-dense-open-pi1-surjective.
Let `V = R.algebraic(M, h)`, with action `ρ`; it lies in the essential image, so
`fieldsOfDefinition` makes it finite dimensional with continuous action. Since `ρ`
kills `ker q`, `ρ̄ (q g) = ρ g` is well defined (two lifts differ by an element of
`ker q`), multiplicative and unique. A continuous surjection of profinite groups is
a quotient map (lem-sfb-compact-hausdorff-surjection-quotient), so `x ↦ ρ̄ x v` is
continuous for each `v`; in a finite basis `e_i`, `ρ̄ x w = ∑ coord_i w • ρ̄ x e_i`,
so `ρ̄` is jointly continuous for the module topology. `R_C.fieldsOfDefinition` and
then `R_C.algebraic.image` give an integral lisse `L` on `C` with representation
`ρ̄`. Pullback preserves lisseness (lem-weil-pbc-continuous-locally-free-pullback),
normality supplies its integral witness on `U`, and the comparison gives
`R(j^* L) ≅ V`; full faithfulness of `R.algebraic` lifts this to `j^* L ≅ M`.
-/
theorem condensed_lisse_extension_kernel_reverse
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens)
    (_hl : l ≠ D.p)
    (_hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))))
    (hUC : U₀ ≤ C₀) (U C : Scheme.{u})
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)))
    (_hj₀ : j₀.left = (ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC)
    (j : U ⟶ C)
    (_hj : j = eU.hom ≫ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫ eC.inv)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U))
    (_hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (_hb : IsGenericPoint (b (IsLocalRing.closedPoint Ω)) Set.univ)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (_haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (R : LisseQlbar.Correspondence l b G) :
    (∃ h : LisseQlbar.integralClosure l U M,
      ∀ g : G, (pullbackPathHom j b) (eG g) = 1 →
        (R.algebraic.functor.obj ⟨M, h⟩).ρ g = 1) →
    ∃ L : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) C),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L ∧
        Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).obj L ≅ M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
