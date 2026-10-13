module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Existence of a compatible local component leg.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension-exists)

Proof: Put A = R_p and S = R minus p. The principal-localization colimit theorem
(00CR) expresses A as the filtered colimit of R_s for s in S. Taking spectra gives
an inverse system of affine schemes with affine transitions and limit Spec A.
Apply finite-data descent (01ZM, 07RP) to the affine etale A-scheme Spec t.B; its
structure map is finitely presented. The descended scheme is qcqs. Its base
changes on the upper tail have affine transitions and affine limit Spec t.B,
so the affine-limit theorem (01Z6) makes a later model affine, say Spec C.
Then C is etale over R_s, hence over R, and t.B is the localization S^{-1}C.
Write i : C to t.B for the canonical map. Restrict the given pointing t.B to K
along i. Its kernel is prime, and the resulting injection of C modulo the kernel
into K extends to its fraction field, giving a residue-field embedding.
The equations hψ and hK show that this prime lies over p and that the embedding
is compatible with χ. Thus C gives a global triple c and i respects both
structure maps and pointings.

For r in S the image of r in C is outside this kernel: the map R to K has kernel
p because χ is an injective field map. Unit refinement gives a global arrow
c to c_r inverting that image. Cocone naturality makes η.app c factor through
c_r.B, so it takes the image of r to a unit in V. The localization universal
property therefore extends η.app c to a ring map b : t.B to V.

For a global triple s and a compatible β : s.B to t.B, base change Spec s.B to
the stage R_s of the model C. Its structure map is finitely presented because
s.B is etale over R. Morphism descent (01ZM) descends β to a later common
principal stage, giving a map from the corresponding principal refinement of
s.B to that of C. Restrict the pointings from K to both refined rings. The map
is pointed since its composite into t.B is β; its equality on pointings can be
checked in K. These refinements are global etale triples. Naturality of η on
the two refinement arrows and the descended map identifies their legs.
The extension b restricts to the refined model leg, since it agrees on C and
principal-localization extensionality forces agreement on the refinement.
Consequently β followed by b equals η.app s, as required for every s and β.
Only existence is asserted here; no local cocone or uniqueness is assumed. -/
theorem etaleResidueTriples_primeLocalization_component_extension_exists
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (V : CommRingCat.{u})
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ) :
    ∃ b : t.B ⟶ V,
      ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
        s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
          t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        β ≫ b = η.app s := by sorry

end AlgebraicGeometry.Scheme

