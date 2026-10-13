module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry
/-- The affine reduction and generic-fibre construction supplies the dominant map;
its compatibility with the chosen residue-field embedding is handled separately.
Proof: identify the fibre coordinate ring with an affine tensor product. Scheme-theoretic
 dominance makes its map to L injective. Tensor with the finite purely inseparable field
 k' and use flatness to retain injectivity. The compatible maps to E kill exactly the
 nilradical, so the induced map from the reduction is injective. Localizing at the
 nonzero elements of the integral base and commuting localization with reduction
 identifies this reduction with the reduced generic fibre. Taking Spec of the resulting
 injection gives h and the base identity. Source: Stacks Project, Tags 0559 and 030R.
(blueprint: lem-sbc-reduced-generic-fibre-field-embedding-core-map) -/
theorem exists_reduced_generic_fibre_map_core
    {Z S S' : Scheme.{u}} [IsAffine Z] [IsAffine S] [IsAffine S'] [IsIntegral S']
    (g : Z ⟶ S) (q : S' ⟶ S) (η : S) (η' : S') (hq : q η' = η)
    (hη' : IsGenericPoint η' Set.univ)
    (L k' E : Type u) [Field L] [Field k'] [Field E]
    [Algebra (S.residueField η) L] [Algebra (S.residueField η) k']
    [Algebra L E] [Algebra k' E]
    [Module.Finite (S.residueField η) k'] [IsPurelyInseparable (S.residueField η) k']
    (j : Spec (.of L) ⟶ g.fiber η) (hj : IsSchemeTheoreticallyDominant j)
    (hjbase : j ≫ g.fiberToSpecResidueField η =
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)))
    (e : S'.residueField η' ≃+* k')
    (he : e.toRingHom.comp
      (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom) =
        algebraMap (S.residueField η) k')
    (hsquare : (algebraMap k' E).comp (algebraMap (S.residueField η) k') =
      (algebraMap L E).comp (algebraMap (S.residueField η) L))
    (aE : Algebra (S'.residueField η') E) :
    letI := aE
    ∃ h : Spec (.of E) ⟶
          ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
        IsSchemeTheoreticallyDominant h ∧
        h ≫ ((pullback g q).nilradical.subschemeι ≫
          pullback.snd g q).fiberToSpecResidueField η' =
            Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E)) := by
  sorry
end AlgebraicGeometry
