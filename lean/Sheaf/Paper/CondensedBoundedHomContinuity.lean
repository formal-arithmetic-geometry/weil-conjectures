/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.Paper.ConstructibleHomContinuityDevissage
import Sheaf.Paper.CondensedSheafExtContinuity
import Sheaf.CategoryTheory.DerivedCategory.BoundedCohomologyConeWitness

/-! # Shifted Hom continuity for bounded constructible condensed complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/
lem-sfb-constructible-cocone-hom-surj.proof.md, paragraph 2.
(blueprint: lem-sfb-condensed-bounded-hom-continuity)

The cocone is a colimit degree by degree in the module category. Its image under the
ordinary derived localization need not be a colimit in the derived category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 800000 in
-- The internal-module and derived-category comparisons need extra elaboration heartbeats.
/-- The canonical additive comparison for a bounded constructible condensed complex is
an isomorphism in every integer shift, for a filtered diagram with a common termwise
lower bound and any supplied termwise colimit cocone.

Source: blueprint main-20261015, lem-sfb-constructible-cocone-hom-surj.proof.md,
paragraph 2 (blueprint: lem-sfb-condensed-bounded-hom-continuity).

Proof:
1. For the fixed diagram and cocone let P(C) assert the comparison for every integer
shift. The formal part of det-lem-constructible-ext-continuity-devissage proves closure
under shifts, isomorphisms and distinguished extensions on any scheme. Degreewise
universality identifies the supplied cocone with the chosen complex colimit: the
degreewise identifications commute with the differentials since they do so on every
colimit leg. Thus they preserve the canonical comparison (def-weil-pbc-category-colimit).
2. By def-sfb-dcons-subfield and sk-def-sfb-bounded-constructible, K has bounded,
constructible cohomology. Apply lem-weil-pbc-condensed-sheaf-ext-continuity to each
H^q(K), the same finite E, the topologically Noetherian X and the common lower bound
of N. This proves P for each cohomology module placed in degree zero, hence for its
shifts. No constructibility of the second arguments is used.
3. Apply lem-sfb-bounded-cohomology-cone-witness to K.obj. Induct along its finite list
ending in K.obj. Shifted cohomology leaves satisfy P by step 2 and isomorphism closure.
For a cone step F_i -> F_j -> F_r[s] -> F_i[1], with i,j earlier, rotate the distinguished
triangle by TR2 (def-weil-triangulated-category). Its endpoints F_j and F_i[1] satisfy P,
so extension closure gives P(F_r[s]); shift back to obtain P(F_r). This also covers K=0.
4. Evaluate P(K.obj) at n. The comparison throughout is induced by the fixed shifted
cocone legs: its value on a representative u_i is u_i followed by Q(c.ι.app i)[n].
The source colimit is in abelian groups; no derived colimit property is assumed.
-/
theorem isIso_boundedConstructible_condensed_hom_colimit
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : PadicSubfieldConstructible X ℓ E)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ)
    (c : Cocone N)
    (hc : ∀ r : ℤ, IsColimit ((HomologicalComplex.eval _ _ r).mapCocone c))
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (n : ℤ) :
    IsIso (colimit.desc _
      ((DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
        preadditiveCoyoneda.obj (op K.obj)).mapCocone c)) := by
  -- Work with all shifts of the chosen complex-colimit comparison.
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicSubfieldRingObj X ℓ E)
  let P := complexHomContinuityLocus A N
  obtain ⟨hs, hi, he, _⟩ :=
    constructibleHomContinuity_devissage (Profinite.continuousMapRingObj E.val) X N
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hi _ _ e h⟩
  let : P.IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun m ↦ ⟨fun C h ↦ hs C m h⟩ }
  have hbase (q : ℤ) : P ((DerivedCategory.singleFunctor A 0).obj
      ((DerivedCategory.homologyFunctor A q).obj K.obj)) := by
    intro m
    apply (ConcreteCategory.isIso_iff_bijective _).mp
    exact isIso_constructible_condensed_sheaf_hom_colimit X ℓ E
      ((DerivedCategory.homologyFunctor A q).obj K.obj) (K.property.2 q) N hN m
  -- Boundedness gives a finite cone construction from cohomology modules.
  obtain ⟨t, F, hlast, hF⟩ :=
    DerivedCategory.bounded_cohomology_cone_witness A K.obj K.property.1
  have hmem : ∀ r, P (F r) := by
    intro r
    induction r using WellFoundedLT.induction with
    | ind r ih =>
      rcases hF r with ⟨q, m, ⟨e⟩⟩ | ⟨i, j, hir, hjr, m, f, g, h, hT⟩
      · exact hi _ _ e.symm (hs _ m (hbase q))
      · have hcone := he _ (Pretriangulated.rot_of_distTriang _ hT) (ih j hjr)
          (hs _ 1 (ih i hir))
        exact (P.prop_shift_iff_of_isStableUnderShift (F r) m).mp hcone
  have hK : P K.obj := hlast ▸ hmem (Fin.last t)
  have hchosen : IsIso (colimit.desc _
      ((DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
        preadditiveCoyoneda.obj (op K.obj)).mapCocone (colimit.cocone N))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hK n)
  -- Transfer preservation of this colimit to the supplied degreewise colimit cocone.
  let H := DerivedCategory.Q ⋙ shiftFunctor _ n ⋙ preadditiveCoyoneda.obj (op K.obj)
  have hcol : IsColimit c := HomologicalComplex.isColimitOfEval N c hc
  obtain ⟨hchosenCol⟩ :=
    (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.mpr hchosen
  have hpres : PreservesColimit N H :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit N) hchosenCol
  exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.mp
    ⟨isColimitOfPreserves H hcol⟩

end AlgebraicGeometry.ProEtale
