module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A compatible cocone and its colimit exist for pointed étale residue triples.

Source: Stacks Project, Tag 04GW (lemma-strict-henselization-different), the ring
colimit in its statement; Mathlib `Scheme.AffineEtale.instEssentiallySmall` and
`CommRingCat.hasColimits_commRingCat` for the size and existence assertions.

Proof: Choose a small skeleton of affine etale schemes over `Spec R`. Over each
representative, the primes and their residue-field maps into `K` form a small set.
Transporting this data along affine isomorphisms gives a small full subcategory of
triples containing an isomorphic copy of every triple. Its inclusion is an equivalence:
morphisms are exactly the ring maps over `R` and `K`, so transporting the pointing
transports the morphisms as well. The ring diagram on this small category has a
colimit in `CommRingCat.{u}`. Transport its cocone and universal property along the
equivalence to obtain `c` and `IsColimit c` for the original diagram.

Let `t0` be the identity triple with ring `R`, prime `p`, and residue map the prescribed
algebra map. For each triple `t`, its structural map `t.α` is a morphism `t0 → t`:
the required equation is precisely `t.compatible`. Set `ρ = c.ι.app t0`.
Cocone naturality for this morphism gives `t.α ≫ c.ι.app t = ρ`.
For each `t` let `j_t` be the composite of the inverse affine global-sections
isomorphism, evaluation at `t.q`, and `t.φ`. A morphism of triples commutes with
these maps by its equation in the induced under-over category. Thus the `j_t` form
a cocone with vertex `CommRingCat.of K`. Its descent through `IsColimit c` is a
ring homomorphism `ψ : c.pt →+* K`; the colimit factorization equations are exactly
`ψ.comp (c.ι.app t).hom = j_t.hom`. These constructions prove every asserted clause.
Only the fixed residue map is used in this argument, so the separable-closure
hypothesis is harmless and no filteredness lemma is needed for existence.
(blueprint: lem-weil-pbc-etale-triples-filtered-colimit-colimit) -/
theorem etaleResidueTriples_exists_colimit_part
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K] :
    ∃ c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))),
      Nonempty (IsColimit c) ∧ ∃ (ρ : R ⟶ c.pt) (ψ : c.pt →+* K),
        (∀ t, t.α ≫ c.ι.app t = ρ) ∧
        (∀ t, ψ.comp (c.ι.app t).hom =
          ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) := by
  sorry

end AlgebraicGeometry.Scheme
