/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Canonical linear base change of additive first cohomology -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- The canonical pullback of additive structure-sheaf cohomology is extension
of scalars. The given actions are required to be induced by structural scalar
multiplication on sections; no finite-dimensionality is assumed or asserted.
Source: Stacks Project, Tags 02KH and 03P2; Tag 0A3P, first sentence of proof.
(blueprint: lem-pbc-additive-cohomology-linear-base-change)

Proof: Identify G and G' with the lifted additive structure sheaves through the
natural section coordinates a and a'. The scalar section formulas uniquely determine
all scalar endomorphisms. The natural etale/Zariski comparison, together with the
Ext/derived and coefficient-universe comparisons, therefore intertwines the given
scalar actions with the usual actions on coherent cohomology. Choose a finite affine
cover of C. It exists since IsCurve supplies quasi-compactness; separatedness over the
affine field spectrum makes all intersections affine. Pull it back to C'. On every
intersection, affine sections after base change are the tensor product of the old
sections by k'. The adjoint formula hq identifies the induced cochain map with
s mapping to 1 tensor s. Naturality of the Cech/cohomology comparisons identifies this
map with H(q) composed with the canonical etale cohomology pullback. Tensoring over a
field is exact, so cohomology of the tensor complex is tensor cohomology. This gives
the k'-linear equivalence e and its normalization on every original class. The
displayed pullback square is handled by its unique isomorphism to the chosen
categorical pullback. In degree-one-zero cases (empty schemes, affine curves, and
zero-dimensional proper curves), the same complexes give the zero equivalence. No
Frobenius, torsion, connectedness, smoothness, or algebraic closedness is used. -/
theorem exists_additive_cohomology_linear_base_change
    {k k' : Type u}
    [Field k] [Field k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : C'.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (ha' : ∀ (U V : C'.Etaleᵒᵖ) (g : U ⟶ V) (x : G'.obj.obj U),
      a' V (G'.obj.map g x) = g.unop.left.appTop (a' U x))
    (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
    (hq : (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι').homEquiv
            G G' q).hom.app U x) =
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x)))
    [Module k (Sheaf.H G 1)] [Module k' (Sheaf.H G' 1)]
    (hscalar : ∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : Sheaf.H G 1,
          Sheaf.H.map μ 1 x = c • x)
    (hscalar' : ∀ c : k', ∃ μ : G' ⟶ G',
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) ∧
        ∀ x : Sheaf.H G' 1,
          Sheaf.H.map μ 1 x = c • x) :
    ∃ e : Sheaf.H G' 1 ≃ₗ[k'] (k' ⊗[k] Sheaf.H G 1),
      ∀ x, e (Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)) = 1 ⊗ₜ[k] x := by sorry

end AlgebraicGeometry.IsCurve
