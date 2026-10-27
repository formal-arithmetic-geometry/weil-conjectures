/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Open-base locality of structural and geometric-fibre conditions

Source: Stacks Project, morphisms.tex, Tags 01TP, 01TQ, 01U3, 01QO, and the
open-restriction fibre-product comparison
(blueprint: lem-trf-structural-fibrewise-open-locality).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The eight conditions in order: flatness of the curve and marking; finite presentation
of the curve and marking (including quasi-compactness and quasi-separatedness); pure
ordinary-fibre dimensions of the curve and marking; closed immersion; etaleness.
This is just an indexed list of the existing predicates, so a set of indices selects any
subset without presupposing the other conditions. Empty fibres impose no condition.
Source: Stacks 01TP, 01U3, 01QO and the node's structural-condition list
(blueprint: lem-trf-structural-fibrewise-open-locality). -/
def structuralFibrewiseConditions {S : Scheme.{u}} (C F : Over S) (j : F ⟶ C)
    (d e : ℕ) : Fin 8 → Prop :=
  ![Flat C.hom, Flat F.hom,
    LocallyOfFinitePresentation C.hom ∧ QuasiCompact C.hom ∧ QuasiSeparated C.hom,
    LocallyOfFinitePresentation F.hom ∧ QuasiCompact F.hom ∧ QuasiSeparated F.hom,
    ∀ s : S, Nonempty (C.hom.fiber s) → (C.hom.fiber s).IsPureDimension d,
    ∀ s : S, Nonempty (F.hom.fiber s) → (F.hom.fiber s).IsPureDimension e,
    IsClosedImmersion j.left, Etale F.hom]

/-- Every selected subset of structural conditions is local on an arbitrary open base cover.
Taking `A = Set.univ` gives their simultaneous locality.
Source: Stacks 01TP, 01TQ, 01U3, 01QO
(blueprint: lem-trf-structural-fibrewise-open-locality).

Proof (DAG Steps 1--5 and 7): identify base changes to opens with inverse-image opens by
the fibre-product universal property and open factorization. Local rings and residue fields
are unchanged. Flatness is consequently pointwise local. For finite presentation, use
lem-sfb-separated-lfp-target-open-locality and lem-pc-quasi-compact-local-on-target for the
map and its diagonal; base-change permanence is lem-weil-pbc-qcqs-morphism-permanence.
Use lem-weil-pbc-closed-finite-etale-zariski-local on the inverse-image cover of C for j
and on the base cover for q. Ordinary fibres are isomorphic with both projections, hence
have the same irreducible components and component dimensions. Empty fibres agree.
Each equivalence is independent of the other conditions; conjoin over A. -/
theorem structuralFibrewiseConditions_iff_openCover {S : Scheme.{u}}
    (C F : Over S) (j : F ⟶ C) (d e : ℕ) (I : Type w) (U : I → S.Opens)
    (hU : ∀ s : S, ∃ i : I, s ∈ U i) (A : Set (Fin 8)) :
    (∀ k ∈ A, structuralFibrewiseConditions C F j d e k) ↔
      ∀ i : I, ∀ k ∈ A,
        structuralFibrewiseConditions ((Over.pullback (U i).ι).obj C)
          ((Over.pullback (U i).ι).obj F) ((Over.pullback (U i).ι).map j) d e k := by
  sorry

/-- The marking's image lies in the relative smooth locus iff this holds over every open
of the base cover. Smoothness at a point means admitting a smooth open neighbourhood,
so this statement does not assume local finite presentation of the entire curve.
Source: Stacks definition-smooth and open restriction of smooth morphisms
(blueprint: lem-trf-structural-fibrewise-open-locality).

Proof (DAG Step 6): the relative smooth loci agree on the inverse-image opens.
A smooth neighbourhood restricts to a smooth neighbourhood by clause (a) of
lem-weil-pbc-smooth-restrict-open-subschemes. Conversely a neighbourhood smooth over the
base open is smooth over S by clause (b), since the target inclusion is an open immersion.
For each point of F choose an open containing its image in S. The corresponding image
point in C lies in the same smooth neighbourhood on either side. -/
theorem marking_smoothNeighbourhood_iff_openCover {S : Scheme.{u}}
    (C F : Over S) (j : F ⟶ C) (I : Type w) (U : I → S.Opens)
    (hU : ∀ s : S, ∃ i : I, s ∈ U i) :
    (∀ f : F.left, ∃ W : C.left.Opens, j.left f ∈ W ∧ Smooth (W.ι ≫ C.hom)) ↔
      ∀ i : I, ∀ f : ((Over.pullback (U i).ι).obj F).left,
        ∃ W : ((Over.pullback (U i).ι).obj C).left.Opens,
          ((Over.pullback (U i).ι).map j).left f ∈ W ∧
            Smooth (W.ι ≫ ((Over.pullback (U i).ι).obj C).hom) := by
  sorry

/-- Any isomorphism-invariant predicate of geometric fibre diagrams is local on the base.
The local side uses the SAME chosen closure of `S.residueField s`: `g` is its unique
factorization through the base open. Quantifying over these factorizations excludes none
of the local points and makes no field-extension invariance assumption on P.
Source: geometric-fibre definition and the open-restriction fibre-product comparison
(blueprint: lem-trf-structural-fibrewise-open-locality).

Proof (DAG Steps 1 and 7): residue fields are unchanged on opens. At s in U i, the chosen
geometric point factors uniquely through U i by
lem-weil-pbc-morphism-factors-through-open-subscheme. For each of F,C,X the iterated
pullback over this factorization is isomorphic over the fixed closure to the original
geometric fibre. Construct the inverse using the original projection and the unique
factorization through the open. Both composites are identities by the pullback universal
property. The three isomorphisms intertwine j and r, since the two composites have equal
projections. Apply hP to this diagram isomorphism. The cover contains every base point,
which proves both implications. No change of algebraically closed field occurs. -/
theorem geometricDiagramPredicate_iff_openCover {S : Scheme.{u}}
    (F C X : Over S) (j : F ⟶ C) (r : C ⟶ X) (I : Type w) (U : I → S.Opens)
    (hU : ∀ s : S, ∃ i : I, s ∈ U i)
    (P : (Ω : Type u) → [Field Ω] → [IsAlgClosed Ω] →
      ComposableArrows (Over (Spec (CommRingCat.of Ω))) 2 → Prop)
    (hP : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (D E : ComposableArrows (Over (Spec (CommRingCat.of Ω))) 2),
      (D ≅ E) → (P Ω D ↔ P Ω E)) :
    (∀ s : S, P (AlgebraicClosure (S.residueField s))
      (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
          (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s)
        ).mapComposableArrows 2).obj (ComposableArrows.mk₂ j r))) ↔
      ∀ (i : I) (s : S)
        (g : Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))) ⟶ (U i).toScheme),
        g ≫ (U i).ι =
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
            (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s →
        P (AlgebraicClosure (S.residueField s))
          (((Over.pullback g).mapComposableArrows 2).obj
            (((Over.pullback (U i).ι).mapComposableArrows 2).obj
              (ComposableArrows.mk₂ j r))) := by
  sorry

end AlgebraicGeometry
