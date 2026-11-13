/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90Etale

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Injectivity part of geometric stalk evaluation.

Source: Stacks Project, Tags 03QU and Example 03QV (2). -/
theorem etale_units_stalk_evaluation_injective (K : Type u) [Field K] :
    let Ω := AlgebraicClosure K
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ f : (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf →+
        Field.galoisUnitsTopRep K,
      (∀ (X : S.Etale) (x : p.fiber.obj X) (z : S.gmSheaf.obj.obj (op X)),
        algebraMap (SeparableClosure K) Ω
            (Additive.toMul (f (p.toPresheafFiber X x S.gmSheaf.obj z)) :
              (SeparableClosure K)ˣ) =
          (ΓSpecIso (.of Ω)).hom
            (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)))) →
      Function.Injective f := by
  dsimp only
  intro f hf
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Ω := AlgebraicClosure K
  let S := Spec (.of K)
  let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let p := pointSmallEtale s
  intro a b hab
  obtain ⟨X, x, z₁, z₂, rfl, rfl⟩ :=
    p.toPresheafFiber_jointly_surjective₂ (P := S.gmSheaf.obj) a b
  have heval := (hf X x z₁).symm.trans ((congrArg
    (fun z ↦ algebraMap (SeparableClosure K) Ω
      (Additive.toMul z : (SeparableClosure K)ˣ)) hab).trans (hf X x z₂))
  -- A singleton open replaces the finite-field/compositum route in the docstring.
  have := discreteTopology_of_etale_of_unique X
  let t : X.left := x.left (default : Spec (.of Ω))
  let U : X.left.Opens := ⟨{t}, isOpen_discrete _⟩
  have hU : Set.range x.left ⊆ (U : Set X.left) := by
    rintro _ ⟨q, rfl⟩
    change x.left q = t
    exact congrArg x.left (Subsingleton.elim (α := Spec (.of Ω)) q default)
  obtain ⟨y, hy⟩ := exists_pointSmallEtale_fiber_ofOpens s x U hU
  let Y := Etale.ofOpens X U
  let g : Y ⟶ X := Etale.ofOpensι X U
  have : Subsingleton Y.left := ⟨fun c d ↦ Subtype.ext (c.2.trans d.2.symm)⟩
  have : Nonempty Y.left := ⟨⟨t, rfl⟩⟩
  let := (isField_of_etale_of_subsingleton Y).toField
  apply (p.toPresheafFiber_eq_iff' X x z₁ z₂).2
  refine ⟨Y, g, y, hy, ?_⟩
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  apply (show Γ(Y.left, ⊤) →+* Γ(Spec (.of Ω), ⊤) from y.left.appTop.hom).injective
  have hxy : y.left ≫ g.left = x.left := congrArg (fun z ↦ z.left) hy
  have hval : x.left.appTop
      ((Additive.toMul z₁.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)) =
      x.left.appTop ((Additive.toMul z₂.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)) :=
    (ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective heval
  change y.left.appTop (g.left.appTop
      ((Additive.toMul z₁.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))) =
    y.left.appTop (g.left.appTop
      ((Additive.toMul z₂.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)))
  change (g.left.appTop ≫ y.left.appTop)
      ((Additive.toMul z₁.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)) =
    (g.left.appTop ≫ y.left.appTop)
      ((Additive.toMul z₂.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))
  rw [← Scheme.Hom.comp_appTop, hxy]
  exact hval

end AlgebraicGeometry.Scheme
