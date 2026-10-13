/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Untensored comparison of additive etale and Zariski pullback -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Coordinate-normalized additive comparisons commute with structural scalar
endomorphisms and untensored pullback. No module actions on G.H or G'.H are inputs.
Source: Stacks Project, Tag 03P2, Theorem etale-cohomology-theorem-zariski-fpqc-quasi-coherent,
and Tag 02KH, the canonical cohomology comparison before tensor extension.
(blueprint: lem-pbc-additive-cohomology-pullback-comparison)

Proof: Use natural section coordinates for the associated etale unit module to
identify G with its coefficient lift: on U send x to the lift of the inverse
unit coordinate applied to a U x. Naturality of both coordinate families gives
an isomorphism of sheaves. Do the same for G'. Compose their cohomology maps
with the natural coefficient-lift, etale/Zariski, and ordinary Ext comparisons.
Transport the target unit module through the pullback-unit isomorphism and the
unique isomorphism between the displayed cartesian square and the categorical
pullback. These give additive equivalences e and e'. For each scalar, the
section-coordinate formula determines its endomorphism uniquely. Naturality
of all comparisons for these endomorphisms therefore give the two scalar
endomorphism identities, in the ordinary structural module actions.
For pullback compatibility choose a finite affine cover of C and its inverse
image cover. All tuple intersections are affine by separatedness. The section
formula hq says that the coefficient map on each intersection is structural
pullback. The natural affine Cech inverse-image comparison thus gives the
same map on cycle classes as H.baseChangeLinear. Every cohomology class is
represented by such a cycle, giving the stated equality. Transport the equality
through the displayed-pullback isomorphism. No tensor exactness, flatness,
injectivity, surjectivity, dimension bound or properness is used. Empty schemes
and degree zero are included by the same section complexes. -/
theorem exists_additive_cohomology_pullback_comparison
    {k k' : Type u}
    [CommRing k] [CommRing k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [CompactSpace C] [IsSeparated f]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (n : ℕ)
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
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x))) :
    ∃ e : Sheaf.H G n ≃+ HOver f (SheafOfModules.unit C.ringCatSheaf) n,
      ∃ e' : Sheaf.H G' n ≃+
        HOver (baseChangeSnd (S := k') f)
          (baseChangedModule (S := k') f (SheafOfModules.unit C.ringCatSheaf)) n,
      (∀ (c : k) (μ : G ⟶ G),
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) →
        ∀ x, e (Sheaf.H.map μ n x) = c • e x) ∧
      (∀ (c : k') (μ : G' ⟶ G'),
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) →
        ∀ x, e' (Sheaf.H.map μ n x) = c • e' x) ∧
      ∀ x, e' (Sheaf.H.map q n (Etale.cohomologyMap ι' G n x)) =
        H.baseChangeLinear (S := k') f (SheafOfModules.unit C.ringCatSheaf) n (e x) := by sorry

end AlgebraicGeometry.Scheme.Modules
