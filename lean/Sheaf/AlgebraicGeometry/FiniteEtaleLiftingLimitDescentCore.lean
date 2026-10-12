module

public import Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation
import Sheaf.AlgebraicGeometry.DescendFinite

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The limit-descent construction produces a lift together with the canonical identity
isomorphism of the proper base.  The latter records the compatibility datum used in the
limit argument.
Source: Stacks Project, Lemma 0GS2, proof, General case.
(blueprint: lem-weil-pbc-finite-etale-lifting-limit-descent-core). -/
theorem exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting_core
    (H : ∀ (B : Type u) [CommRing B], IsGRing B →
      ∀ (J : Ideal B) [HenselianRing B J] (Z : Scheme.{u})
        (g : Z ⟶ Spec (.of B)) [IsProper g]
        (W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
          (pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
        ∃ U' : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Z,
          Nonempty
            (Over.mk (pullback.snd U'.hom
              (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))) ≅
              Over.mk W.hom))
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) ∧ Nonempty (Y ≅ Y) := by
  sorry

end AlgebraicGeometry.Scheme
