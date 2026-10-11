module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Sheaf.FieldTheory.SeparableExtension

/-!
# Components after base change to an algebraic closure

Source: `literature/stacks-project/varieties.tex`, Lemmas 0BUG and 0FD1,
with the degree calculation from Cohomology of Schemes, Lemma 02KH
(blueprint: lem-pc-base-change-closure-components).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- Components of a smooth projective curve after extension to an algebraic closure.

Source: Varieties, Lemmas 0BUG and 0FD1; Cohomology of Schemes, Lemma 02KH
(blueprint: lem-pc-base-change-closure-components).

The proof first identifies the finite separable algebra of global sections, then uses
its primitive idempotents to obtain the clopen components and flat base change for the
Euler-characteristic degree. It uses `lem-pc-projective-proper`,
`lem-pc-h0-proper-variety`, `lem-pc-global-sections-separable`,
`lem-pc-separable-tensor-algebraic-closure`, `lem-pc-flat-base-change-cohom`,
`lem-pc-scheme-connected-iff-idempotents`, `lem-pc-proper-base-change`,
`lem-pc-dim-base-change`, `lem-pc-clopen-smooth-proper-curve`,
`lem-pc-finrank-field-base-change`, and
`lem-pc-euler-characteristic-well-defined`.
-/
theorem baseChange_closure_components
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [f.IsSmoothProjectiveCurve]
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] :
    letI := f.ΓAlgebra
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    ∃ (hfield : IsField Γ(X, ⊤)),
      letI : Field Γ(X, ⊤) := hfield.toField
      FiniteDimensional k Γ(X, ⊤) ∧
      Algebra.IsSeparableExtension k Γ(X, ⊤) ∧
      ∃ (Xj : Fin (Module.finrank k Γ(X, ⊤)) → Scheme.{u})
        (ι : ∀ j, Xj j ⟶ Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))),
        (∀ j, Nonempty (Xj j) ∧
          IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧
          Smooth (ι j ≫ Limits.pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) ∧
          IsProper (ι j ≫ Limits.pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) ∧
          IsConnectedCurve (ι j ≫ Limits.pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) ∧
          IsIso (ι j ≫ Limits.pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).appTop) ∧
        Nonempty (IsColimit
          (Cofan.mk (Limits.pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) ι)) ∧
        ∀ (L : X.Modules), L.IsInvertible →
          ∀ j, letI : (Xj j).Over (Spec (.of Ω)) := ⟨ι j ≫ Limits.pullback.snd f
              (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))⟩
            Scheme.Modules.degree Ω ((Scheme.Modules.tensorPullback (ι j)).obj
              ((Scheme.Modules.tensorPullback (Limits.pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj L)) *
                (Module.finrank k Γ(X, ⊤) : ℤ) =
              Scheme.Modules.degree k L := by
  sorry

end
end AlgebraicGeometry
