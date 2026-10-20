/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.IsProperOfFieldBaseChange
import Sheaf.AlgebraicGeometry.GeometricReducednessFromGenericStalks
import WeilConjectures.AlgebraicGeometry.GenericFlatness
import WeilConjectures.AlgebraicGeometry.GenericGeometricIrreducibilityShrink
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.GenericConstancyGeometricReducedness
import Sheaf.TraceFormula.GenericFibreComponentLowerBound
import Sheaf.TraceFormula.GenericFibreDimensionNeighborhood
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.FiniteEtaleGenericComponentSplitting
import Sheaf.AlgebraicGeometry.NodalClosedPointsReduced

/-! # Enumerating contracted components after finite étale base change

Source: Stacks Project, more-morphisms.tex, Tags 0551, 0559 and 055A, with the
contracted-component refinement of Temkin, Lemma 5.1(ii), printed p. 34
(blueprint: lem-trf-contracted-component-no-extra-generic).

Schemes over a base and their morphisms use `Over`; `Over.pullback` supplies the canonical
base changes, including the closed inclusions of the component fibres.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Contracted reduced geometric components are proper. After shrinking an integral Noetherian
base and a finite étale cover, all geometric components admit a finite, nonrepeated enumeration
by flat finitely presented closed families, with a constant contracted sublist and proper
contracted generic fibres. Source: Stacks 0551, 0559, 055A; Temkin Lemma 5.1(ii), p. 34
(blueprint: lem-trf-contracted-component-no-extra-generic).

Proof, following the nine steps of the DAG:
1. A contracted reduced component maps to a closed point under the proper fibre map.
   Its residue field is the algebraically closed base field. Reducedness factors the map
   through that point, so the component is proper by proper base change and composition
   (lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-closed-point-residue-field-base).
2. Apply lem-trf-finite-etale-generic-component-splitting. Take the reduced closures of the
   finitely many generic components, using reduced_induced_closed_subscheme.
3. The fixed geometric generic fibre is reduced by lem-trf-nodal-points-reduced-algebraically-
   closed. The algebraic-closure test gives geometric reducedness of the generic fibre and
   its field extensions. Each reduced component is geometrically reduced: its generic stalk
   is a localization of the reduced ambient ring, also after any field extension. Apply
   lem-pur-geometric-reducedness-from-generic-stalks; geometric irreducibility gives integrality.
4. Over the Noetherian base the closures are finitely presented. Apply generic flatness,
   generic geometric irreducibility, and generic constancy of geometric reducedness; intersect
   the finitely many resulting opens. Every component fibre is nonempty, reduced, irreducible.
5. Chevalley's theorem removes the locus missed by the closures. The component lower-bound
   lemma and the cover by n irreducible fibres give exactly n distinct components. Reduced
   induced uniqueness identifies their scheme structures. With n = 0 the total fibre is empty.
6. Take reduced proper images Q_i in the target. Reducedness factors H_i through Q_i;
   this factorization is proper and surjective. Surjective base change identifies the image
   on every geometric fibre with the underlying set of Q_i's fibre.
7. Apply lem-trf-generic-fibre-dimension-neighborhood to each Q_i. Fibre dimension survives
   field extension. These nonempty irreducible images have dimension zero exactly when they
   are singletons; define J by this condition on the generic fibre.
8. Contracted generic components become proper after algebraic closure by step 1.
   Apply lem-pc-proper-descends-field to descend properness to the generic residue field.
9. Delete from the original affine open the finite closed image of the complement of the
   common good open in the cover. Choose a nonempty principal affine open in the remainder.
   Restricting the finite étale cover and the component families gives all the conclusions.
   Empty lists and an empty contracted sublist require no additional shrinking.
-/
theorem contracted_component_no_extra_generic
    (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (Z W : Over T)
    [Flat Z.hom] [LocallyOfFinitePresentation Z.hom] [QuasiCompact Z.hom]
    [QuasiSeparated Z.hom]
    [Flat W.hom] [LocallyOfFinitePresentation W.hom] [QuasiCompact W.hom]
    [QuasiSeparated W.hom]
    (hpureZ : ∀ t : T,
      (pullback (C := Scheme.{u}) Z.hom (Orgogozo.geometricPoint T t)).IsPureDimension 1)
    (hpureW : ∀ t : T,
      (pullback (C := Scheme.{u}) W.hom (Orgogozo.geometricPoint T t)).IsPureDimension 1)
    (hnodal : ∀ (t : T)
      (z : pullback (C := Scheme.{u}) Z.hom (Orgogozo.geometricPoint T t)),
      z ∉ (pullback.snd Z.hom (Orgogozo.geometricPoint T t)).smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal
        ((pullback (C := Scheme.{u}) Z.hom (Orgogozo.geometricPoint T t)).presheaf.stalk z))
        ((pullback (C := Scheme.{u}) Z.hom (Orgogozo.geometricPoint T t)).presheaf.stalk z) ≃+*
          Orgogozo.nodeRing (AlgebraicClosure (T.residueField t))))
    (h : Z ⟶ W) [IsProper h.left] :
    (∀ (t : T) (R : Over (Spec (.of (AlgebraicClosure (T.residueField t)))))
      (j : R ⟶ (Over.pullback (Orgogozo.geometricPoint T t)).obj Z),
      IsReduced R.left → IsClosedImmersion j.left →
      Set.range j.left ∈ irreducibleComponents
        (pullback (C := Scheme.{u}) Z.hom (Orgogozo.geometricPoint T t)) →
      (Set.range (j.left ≫ ((Over.pullback (Orgogozo.geometricPoint T t)).map h).left)
        ).Subsingleton → IsProper R.hom) ∧
    ∃ (U : T.Opens), (U : Set T).Nonempty ∧ IsAffine U.toScheme ∧
      ∃ (S : Scheme.{u}) (π : S ⟶ U.toScheme),
        IsIntegral S ∧ IsAffine S ∧ IsFinite π ∧ Etale π ∧ Surjective π ∧
        ∃ (n : ℕ) (H : Fin n → Over S)
          (ι : ∀ a : Fin n, H a ⟶ (Over.pullback (π ≫ U.ι)).obj Z) (J : Set (Fin n)),
          (∀ a : Fin n, IsClosedImmersion (ι a).left ∧ Flat (H a).hom ∧
            LocallyOfFinitePresentation (H a).hom ∧ QuasiCompact (H a).hom ∧
            QuasiSeparated (H a).hom) ∧
          (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
            (∀ a : Fin n, IsReduced (pullback (C := Scheme.{u}) (H a).hom s)) ∧
            Function.Injective (fun a : Fin n ↦ Set.range ((Over.pullback s).map (ι a)).left) ∧
            Set.range (fun a : Fin n ↦ Set.range ((Over.pullback s).map (ι a)).left) =
              irreducibleComponents
                (pullback (C := Scheme.{u}) (pullback.snd Z.hom (π ≫ U.ι)) s) ∧
            ∀ a : Fin n,
              (Set.range (((Over.pullback s).map (ι a)).left ≫
                ((Over.pullback s).map ((Over.pullback (π ≫ U.ι)).map h)).left)
                ).Subsingleton ↔ a ∈ J) ∧
          (∀ (ξ : S), IsGenericPoint ξ (Set.univ : Set S) →
            ∀ a : Fin n, a ∈ J → IsProper ((H a).hom.fiberToSpecResidueField ξ)) := by
  sorry

end AlgebraicGeometry
