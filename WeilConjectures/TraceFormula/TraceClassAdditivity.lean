/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurvePieces
public import WeilConjectures.TraceFormula.TraceClass

/-!

# Correspondences with another coefficient

Let `c = (c₁, c₂) : C ⟶ X × X` be an endocorrespondence. The same support carries
correspondences with any other coefficient object `K'` and coefficient map
`u' : Lc₂^* K' ⟶ Rc₁^! K'` (`ProEtale.CondensedRing.Correspondence.withCoeff`), with the same
fixed locus; this is how the coefficient maps `u^U`, `φ_m`, `u^Z` of the open–closed triangle
`K^U = j_! Lj^* K ⟶ K ⟶ K^Z = Rx_* Lx^* K ⟶` of a fixed point of the Frobenius graph
(blueprint `d-curve-pieces`) are compared. Restriction to an open subscheme and local terms are
additive in the Borel–Moore section.

The additivity of local terms along the curve pieces at an isolated rational fixed point of the
model Frobenius (blueprint `prop-trf-trace-class-additivity`, item 2) is
`ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_add`, in
`WeilConjectures.TraceFormula.FrobeniusLocalTerm`; it is deduced there from Varshavsky's theorem
for contracting correspondences rather than from additivity of the trace classes themselves.

## Main definitions

- `ProEtale.CondensedRing.Correspondence.withCoeff`: the correspondence with the same support and
  another coefficient object and map.
- `ProEtale.CondensedRing.Correspondence.FixedLocus.traceClassWithCoeff`: its trace class on the
  fixed locus of `c`.

## Main statements

- `ProEtale.CondensedRing.BorelMooreSection.localTerm_add`: local terms are additive.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace BorelMooreSection

variable {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

/-- The restriction of Borel–Moore sections along an open immersion is additive. -/
lemma restrict_add (j : U ⟶ X) [IsOpenImmersion j.left] (α β : BorelMooreSection ℓ X) :
    (α + β).restrict j = α.restrict j + β.restrict j := by
  have := Functor.additive_of_iso (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).symm
  simp only [restrict, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

omit [LocallyOfFiniteType U.hom] [IsSeparated U.hom] in
/-- Local terms are additive (blueprint `lem-trf-integration-linear`). -/
lemma localTerm_add (j : U ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    [IsProper U.hom] (α β : BorelMooreSection ℓ X) :
    (α + β).localTerm j = α.localTerm j + β.localTerm j := by
  rw [localTerm, localTerm, localTerm, restrict_add, integral_add]

end BorelMooreSection

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The correspondence with the support `(c₁, c₂)` of `c` and another coefficient object `K'`
and coefficient map `u' : Lc₂^* K' ⟶ Rc₁^! K'` (blueprint `def-trf-correspondence`). -/
noncomputable def withCoeff (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.c₁).obj K') :
    Correspondence ℓ K' where
  C := c.C
  c₁ := c.c₁
  c₂ := c.c₂
  u := u'

variable {c}

/-- A fixed locus of `c` is a fixed locus of every correspondence with the same support. -/
noncomputable def FixedLocus.withCoeff (F : c.FixedLocus)
    (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.c₁).obj K') :
    (c.withCoeff K' u').FixedLocus where
  F := F.F
  ι := F.ι
  w := F.w
  isLimit := F.isLimit

/-- The trace class of the correspondence with the support of `c` and the coefficient map `u'`,
as a Borel–Moore section of the fixed locus `F` of `c`. -/
noncomputable def FixedLocus.traceClassWithCoeff (F : c.FixedLocus)
    (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.c₁).obj K') :
    BorelMooreSection ℓ F.F :=
  (c.withCoeff K' u').traceClass (F.withCoeff K' u')

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
