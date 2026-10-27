module

public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Sheaf.RingTheory.FilteredColimitFiniteData
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.RingTheory.ColimitCategoryFpAlgebras
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Sheaf.RingTheory.IntegersExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.ExcellentRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Sheaf.AlgebraicGeometry.CompleteLocalSplitTorusHomLift
import Mathlib.RingTheory.FinitePresentation
import Sheaf.TraceFormula.ArtinApproximationEtaleLocalMap

/-! # Étale lifting of a specified split torus subgroup

Source: Conrad, Reductive group schemes (2014), Proposition 3.1.6, pp.83--84,
and Proposition B.3.4, pp.290--292.
(blueprint: lem-sfb-split-torus-etale-subgroup-lift).

All tori below are pullbacks of the recorded relative split torus over S.
The residue-field point q encodes a residually trivial pointed neighbourhood.
The final equality specifies the given embedding, rather than just its image.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A specified split torus subgroup in an algebraically closed residue fibre of a
smooth affine finitely presented group lifts over a residually trivial affine étale
neighbourhood. The pullbacks of the fixed split torus are the split tori over the
residue field and the neighbourhood, with their canonical coordinate group laws.

Source: Conrad, Reductive group schemes (2014), Proposition 3.1.6, pp.83--84,
Proposition B.3.4, pp.290--292, and Corollary B.3.5, pp.292--293.
(blueprint: lem-sfb-split-torus-etale-subgroup-lift).

Proof:
1. Write G = Spec H. Descend the smooth finitely presented algebra H to a
   finitely generated integer subalgebra A_i, using
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine and
   lem-weil-pbc-smooth-algebra-finite-type-model. Descend the Hopf structure and
   its identities by lemma-nagata-filtered-colimit-finite-data. Every enlargement
   preserves smoothness by lem-pc-proper-base-change.
2. The residue fields k_i of the contracted primes have union k. Descend the
   specified coordinate map j₀ and its Hopf identities using
   lem-weil-pbc-colimit-category-fp-algebras, then its closedness using
   lem-weil-pbc-descend-closed-immersion. This retains the map, not just its image.
3. Localize A_i at its prime and complete. Lem-trf-integers-excellent and
   lem-exc-finite-type-localization-excellent give excellence, hence the Noetherian
   and G-ring properties in def-exc-excellent-ring. The completion is Noetherian,
   local, and complete with the original residue field, by
   lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring,
   and lem-weil-pbc-module-completion-complete.
4. Apply lem-sfb-complete-local-split-torus-hom-lift over that completion. Descend
   the resulting closed Hopf homomorphism to a finite type subalgebra using the
   map and equality clauses of lem-weil-pbc-colimit-category-fp-algebras and
   lem-weil-pbc-descend-closed-immersion.
5. By lem-weil-pbc-finite-type-noetherian-finite-presentation present this algebra
   by finitely many equations. Lem-trf-artin-approximation-etale-local-map with
   precision one gives a residually trivial étale neighbourhood and a solution
   agreeing residually with the original one. Pull back the closed embedding,
   using lem-weil-pbc-closed-immersion-base-change.
6. Base change back from A_i to A. Lem-weil-pbc-etale-scheme-base-change and
   lem-weil-pbc-closed-immersion-base-change preserve the required properties.
   The distinguished point has residue k, and the fibre map equals j₀.
   Rank zero is the same empty-product construction. No henselian, connectedness,
   or reductivity assumption is used. -/
theorem splitTorus_etale_subgroup_lift
    (A : Type u) [CommRing A] (s : Spec (.of A))
    [IsAlgClosed ((Spec (.of A)).residueField s)]
    (G : Grp (Over (Spec (.of A))))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (r : ℕ)
    (j₀ : (Over.pullback ((Spec (.of A)).fromSpecResidueField s)).mapGrp.obj
        (relativeSplitTorus (Spec (.of A)) r) ⟶
      (Over.pullback ((Spec (.of A)).fromSpecResidueField s)).mapGrp.obj G)
    (hj₀ : IsClosedImmersion j₀.hom.hom.left) :
    ∃ (C : CommRingCat.{u}) (p : Spec C ⟶ Spec (.of A)), Etale p ∧
      ∃ (q : Spec ((Spec (.of A)).residueField s) ⟶ Spec C)
        (hq : (Spec (.of A)).fromSpecResidueField s = q ≫ p),
        IsIso (p.residueFieldMap
          (q (IsLocalRing.closedPoint ((Spec (.of A)).residueField s)))) ∧
        ∃ j : (Over.pullback p).mapGrp.obj (relativeSplitTorus (Spec (.of A)) r) ⟶
            (Over.pullback p).mapGrp.obj G,
          IsClosedImmersion j.hom.hom.left ∧
          pullback.map (relativeSplitTorus (Spec (.of A)) r).X.hom
              ((Spec (.of A)).fromSpecResidueField s)
              (relativeSplitTorus (Spec (.of A)) r).X.hom p (𝟙 _) q (𝟙 _)
              ((Category.comp_id _).trans (Category.id_comp _).symm)
              ((Category.comp_id _).trans hq) ≫
            j.hom.hom.left ≫ pullback.fst G.X.hom p =
              j₀.hom.hom.left ≫
                pullback.fst G.X.hom ((Spec (.of A)).fromSpecResidueField s) := by
  sorry

end AlgebraicGeometry
