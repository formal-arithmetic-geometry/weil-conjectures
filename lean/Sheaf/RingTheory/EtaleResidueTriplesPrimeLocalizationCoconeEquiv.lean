module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.Paper.EtaleFiniteDataDescent

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Cocones on pointed étale ring diagrams before and after prime localization are
naturally equivalent, with the same vertex and the same restricted base map.
Source: Stacks Project, Tags 04GW, 00CR, 01ZM and 07RP.
(blueprint: new-lem-sbc-etale-triples-prime-localization-cocone-equiv)

Proof: Write A = R_p as the filtered colimit of the principal localizations R_s for
s outside p (Tag 00CR). A finitely presented étale A-algebra descends to an étale
R_s-algebra (Tags 01ZM, 07RP). Restrict its map to K to this model. Its kernel
is a prime over p, and its map to K factors uniquely through the residue field;
composition R → R_s → B_s is étale, so this is an R-triple. Define its leg to V
using the given R-cocone. Naturality along further principal refinements inverts
all s outside p in this leg: each refinement is still an R-triple. The leg
therefore extends uniquely from B_s to its localization, identified with the
original A-algebra. Morphisms descend at a common stage, and equalities at a
later stage (01ZM); this proves independence of the model and naturality of
these extended legs. Descending both directions and the inverse relations of
a comparison isomorphism deals with different models of an object.
Conversely, localize each R-triple B at the images of R outside p; base change
preserves étaleness, and its pointing extends uniquely because these images
are units in K. Restrict the corresponding A-cocone leg along B → B localized.
These constructions are inverse: on an A-triple this follows from independence
of its model; on an R-triple use its principal refinements and naturality,
together with uniqueness of extension from a localization. Both operations
commute with postcomposition into every V → W by the same uniqueness.
Finally, the identity R-triple maps into each descended R-triple. Naturality
of the original cocone along this map gives the asserted equality on R.
No universal cocone or algebra structure on the vertex is assumed here. -/
theorem etaleResidueTriples_primeLocalization_coconeEquiv
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    : ∃ E : ∀ V : CommRingCat.{u},
        (etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V) ≃
        (etaleResidueTriplesRingDiagram
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
            (Functor.const _).obj V),
      (∀ (V W : CommRingCat.{u}) η (f : V ⟶ W),
        E W (η ≫ (Functor.const _).map f) =
          E V η ≫ (Functor.const _).map f) ∧
      ∀ (V : CommRingCat.{u}) η
          (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
          (r : R),
        (t.α ≫ (E V η).app t).hom (algebraMap R (Localization.AtPrime p.asIdeal) r) =
          (η.app ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩).hom r := by sorry

end AlgebraicGeometry.Scheme
