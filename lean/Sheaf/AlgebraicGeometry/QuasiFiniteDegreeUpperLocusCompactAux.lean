module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-! Auxiliary finite-generation conclusion for the successor degree locus. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- (blueprint: lem-weil-pbc-qf-degree-successor-affine-compact-aux)
The finite-generation argument on an affine open produces a compact open whose
carrier is the successor fibre-degree locus. Source: Stacks Project, More on
Morphisms, Tag 07RZ, proof, second paragraph (blueprint:
lem-weil-pbc-qf-degree-successor-affine-compact-aux).

Proof: identify the closed degree-≤r locus on the affine open with the vanishing
locus of an ideal I. Express I as the directed union of its finitely generated
subideals and apply descent of finite locally free morphisms to obtain a finitely
generated subideal J whose vanishing locus has the universal degree-r property.
The universal criterion gives V(J)=V(I), and the complement of V(J), a finite
union of principal opens, is quasi-compact. This also covers the empty, zero,
and unit ideal cases. -/
theorem exists_compact_open_successor_degree_locus_inter_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] (hf : f.IsQuasiFinite)
    (r : ℕ) (W : S.Opens) (hW : IsAffineOpen W)
    (hclosed : IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r})
    (hdegree : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
        Set.range g ⊆ {s : S | (f.fiberToSpecResidueField s).finrankΓ = r})
    (hWge : ∀ s : S, s ∈ W → r ≤ (f.fiberToSpecResidueField s).finrankΓ) :
    ∃ U : S.Opens, IsCompact (U : Set S) ∧
      (U : Set S) = {s : S | r + 1 ≤ (f.fiberToSpecResidueField s).finrankΓ} ∩
        (W : Set S) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
