/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.FiniteClosedAugmentedRows
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

import Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRefinements
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Unit-normalized closed comparisons and finite total pullback

Source: Stacks Project, proetale.tex, Tag 09AH, lemma-ses-associated-to-open;
homology.tex, Tag 0133; the six-step agent comparison deduction in the DAG.
(blueprint: lem-sfb-closed-restriction-total-pullback).

The graded terms, signs, intersections, units, and ordinary totalization reuse the
existing finite-closed construction. The row interface below deliberately imposes no
covering or exactness condition. Its restriction maps are fixed by the actual units,
which are epimorphic under the geometric hypotheses of the statements.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- Signed augmented rows exist without a covering hypothesis.
Source: Stacks, Tag 09AH; comparison deduction, steps 1 and 3
(blueprint: lem-sfb-closed-restriction-total-pullback).
Proof: finite fibre products of closed immersions are closed. Their complementary opens
are finite unions of the given quasi-compact complements. Tag 09AH makes each actual unit
epimorphic. For inclusions of intersections push forward the actual inner unit, using
inverse-image composition. The composite-unit identity gives the restriction-unit equation.
Cancelling the epimorphic unit proves composition. Form the finite products of restrictions;
the two orders of deleting a pair of positions have opposite signs and identical composite
restrictions, proving d squared is zero. Naturality and additivity give the row functor.
Its singleton unit maps give the augmentation. Applying it termwise and using the canonical
(0,n) inclusion gives the total augmentation; its chain equation is the row augmentation
equation. Nothing in this construction uses a covering or row exactness. -/
theorem finiteClosedAugmentedRows_exists {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (m : ℕ) (hm : 0 < m) (W : Fin m → Over X)
    (hclosed : ∀ a, IsClosedImmersion (W a).hom)
    (hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i))
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (hqcW : ∀ a, ∃ U : X.Opens,
      Set.range U.ι = (Set.range (W a).hom)ᶜ ∧ QuasiCompact U.ι)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Nonempty (FiniteClosedAugmentedRows i W A) := by
  classical
  let F : SignedClosedFamily i := ⟨m, hm, W, hclosed, hfactor, hqcW⟩
  obtain ⟨S⟩ := closedRestriction_signed_refinements i hqc A
  let R := S.row F
  let r := fun s t : Finset (Fin m) ↦ if s ⊆ t then R.restriction s t else 0
  have hd (p : ℕ) : finiteClosedDifferential W A r p =
      finiteClosedDifferential W A R.restriction p := by
    unfold finiteClosedDifferential
    congr 1
    funext t
    apply Finset.sum_congr rfl
    intro j _
    have hst : Finset.univ.image ((Fin.succAboveOrderEmb j).trans t) ⊆
        Finset.univ.image t := by
      intro a ha
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨Fin.succAboveOrderEmb j b, Finset.mem_univ _, rfl⟩
    rw [show r (Finset.univ.image ((Fin.succAboveOrderEmb j).trans t))
        (Finset.univ.image t) = R.restriction
          (Finset.univ.image ((Fin.succAboveOrderEmb j).trans t)) (Finset.univ.image t)
      from if_pos hst]
  refine ⟨{
    restriction := r
    restriction_unit := ?_
    restriction_zero := ?_
    ambientRestriction := R.fromSupport
    ambient_unit := R.fromSupport_unit
    rows := R.rows
    additive := R.additive
    terms := R.terms
    differential := ?_
    support := R.support
    augment := R.augment
    augment_unit := ?_
    totalAugment := R.totalAugment
    totalAugment_f := R.totalAugment_f }⟩
  · intro s t hst
    dsimp [r]
    rw [if_pos hst]
    exact R.restriction_unit s t hst
  · intro s t hst
    exact if_neg hst
  · intro M p
    rw [hd]
    exact R.differential M p
  · intro M t
    rw [R.augment_components]
    exact congrArg (fun f ↦ f.app M) (R.fromSupport_unit _ _)

/-- Unit equations force all face squares, and hence unique natural row and total
isomorphisms, including the actual augmentation and its ordinary-derived normalization.
The total comparison is natural on bounded-below complexes; the localization clause needs
only the stated quasi-isomorphism conditions.

Source: Stacks, Tag 09AH, and homology.tex, Tag 0133; six-step comparison deduction
(blueprint: lem-sfb-closed-restriction-total-pullback).

Proof: (1) Every intersection is closed; its complement is a finite union of the given
quasi-compact opens. The ringed open-closed sequence makes each actual unit epimorphic.
Exact inverse image preserves these epimorphisms, also after base change.
(2) Precompose the two candidate face composites with g* eta_J. The restriction-unit
identities and the supplied equations for c_J and c_L give the same eta'_L. Cancel the
epimorphism. Do the same for the ambient Z and each singleton for the augmentation.
(3) Take the direct sum of the supplied comparisons. The face squares give its chain
equation, and the direct sums of their inverses give the inverse row map. The finite
product projections jointly detect maps, so the projection formula alone determines it.
(4) Apply HomologicalComplex₂.mapTotalIso, then totalize this bicomplex isomorphism.
On each diagonal summand its chain equation is the horizontal equation plus (-1)^p times
the vertical equation. The canonical total-comparison injection equation gives TotalFormula.
The diagonal inclusions jointly detect maps, giving uniqueness and naturality.
(5) The augmentation lands in (0,n), so its square is the singleton square in step 3.
Exact inverse image preserves quasi-isomorphisms. Localize the chain equality and multiply
by the inverse of Q(g* alpha), obtaining the displayed ordinary-derived equation.
(6) Every compatible morphism of the data is tested on the same diagonal inclusions.
Composite pullback comparisons satisfy the unit equations; epi cancellation identifies
any separately supplied normalized comparison with that composite. Uniqueness of the total
map gives identity, composition and associativity. Apply this to automorphisms or objectwise
to each arrow of any small parameter category; functoriality and inversion preserve all
the displayed equations. -/
theorem closed_restriction_total_pullback {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (m : ℕ) (hm : 0 < m) (W : Fin m → Over X)
    (hclosed : ∀ a, IsClosedImmersion (W a).hom)
    (hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i))
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (hqcW : ∀ a, ∃ U : X.Opens,
      Set.range U.ι = (Set.range (W a).hom)ᶜ ∧ QuasiCompact U.ι)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (D : FiniteClosedAugmentedRows i W A) {Y : Scheme.{u}} (g : Y ⟶ X)
    (D' : FiniteClosedAugmentedRows (pullback.fst g i) (finiteClosedPullbackFamily W g)
      (ProEtaleTensorComparison.inverseRing g A))
    (c : finiteClosedRestriction i A ⋙ proEtaleModuleInverseImage g A ≅
      proEtaleModuleInverseImage g A ⋙ finiteClosedRestriction (pullback.fst g i)
        (ProEtaleTensorComparison.inverseRing g A))
    (hc : ∀ M : ProEtaleTensorComparison.Modules A,
      (proEtaleModuleInverseImage g A).map ((finiteClosedUnit i A).app M) ≫ c.hom.app M =
        (finiteClosedUnit (pullback.fst g i) (ProEtaleTensorComparison.inverseRing g A)).app
          ((proEtaleModuleInverseImage g A).obj M))
    (cs : ∀ s : Finset (Fin m), s.Nonempty →
      (finiteClosedRestriction (finiteClosedIntersection W s).hom A ⋙
          proEtaleModuleInverseImage g A ≅
        proEtaleModuleInverseImage g A ⋙
          finiteClosedRestriction (finiteClosedIntersection (finiteClosedPullbackFamily W g) s).hom
            (ProEtaleTensorComparison.inverseRing g A)))
    (hcs : ∀ (s : Finset (Fin m)) (hs : s.Nonempty) (M : ProEtaleTensorComparison.Modules A),
      (proEtaleModuleInverseImage g A).map
          ((finiteClosedUnit (finiteClosedIntersection W s).hom A).app M) ≫
        (cs s hs).hom.app M =
          (finiteClosedUnit (finiteClosedIntersection (finiteClosedPullbackFamily W g) s).hom
            (ProEtaleTensorComparison.inverseRing g A)).app
              ((proEtaleModuleInverseImage g A).obj M)) :
    (∀ (s t : Finset (Fin m)) (hs : s.Nonempty) (ht : t.Nonempty), s ⊆ t →
      Functor.whiskerRight (D.restriction s t) (proEtaleModuleInverseImage g A) ≫
          (cs t ht).hom =
        (cs s hs).hom ≫ Functor.whiskerLeft (proEtaleModuleInverseImage g A)
          (D'.restriction s t)) ∧
    (∀ (s : Finset (Fin m)) (hs : s.Nonempty),
      Functor.whiskerRight (D.ambientRestriction s hs) (proEtaleModuleInverseImage g A) ≫
          (cs s hs).hom =
        c.hom ≫ Functor.whiskerLeft (proEtaleModuleInverseImage g A)
          (D'.ambientRestriction s hs)) ∧
    ∃ σ : D.rows ⋙ finiteClosedPullbackComplex g A ≅ proEtaleModuleInverseImage g A ⋙ D'.rows,
      (∀ σ' : D.rows ⋙ finiteClosedPullbackComplex g A ≅
          proEtaleModuleInverseImage g A ⋙ D'.rows,
        D.RowFormula g D' cs σ'.hom ↔ σ' = σ) ∧
      (∀ M : ProEtaleTensorComparison.Modules A,
        (proEtaleModuleInverseImage g A).map (D.augment.app M) ≫ (σ.hom.app M).f 0 =
          c.hom.app M ≫ D'.augment.app ((proEtaleModuleInverseImage g A).obj M)) ∧
      ∃ τ : CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A) ⋙
            @finiteClosedTotal X A D.rows D.additive ⋙ finiteClosedPullbackComplex g A ≅
          CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A) ⋙
            finiteClosedPullbackComplex g A ⋙ @finiteClosedTotal Y _ D'.rows D'.additive,
        (∀ τ' : CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A) ⋙
              @finiteClosedTotal X A D.rows D.additive ⋙ finiteClosedPullbackComplex g A ≅
            CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A) ⋙
              finiteClosedPullbackComplex g A ⋙ @finiteClosedTotal Y _ D'.rows D'.additive,
          D.TotalFormula g D' σ.hom τ'.hom ↔ τ' = τ) ∧
        (Functor.whiskerLeft (CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A))
            (Functor.whiskerRight D.totalAugment (finiteClosedPullbackComplex g A)) ≫ τ.hom =
          Functor.whiskerLeft (CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A))
            (NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ) ≫
              Functor.whiskerLeft (finiteClosedPullbackComplex g A) D'.totalAugment)) ∧
        ∀ (K : CochainComplex.Plus (ProEtaleTensorComparison.Modules A)),
          QuasiIso (D.totalAugment.app K.obj) →
          QuasiIso (D'.totalAugment.app ((finiteClosedPullbackComplex g A).obj K.obj)) →
          ∃ e : DerivedCategory.Q.obj
              ((finiteClosedPullbackComplex g A).obj
                (((finiteClosedRestriction i A).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K.obj)) ≅
              DerivedCategory.Q.obj ((finiteClosedPullbackComplex g A).obj
                ((@finiteClosedTotal X A D.rows D.additive).obj K.obj)),
            e.hom = DerivedCategory.Q.map
              ((finiteClosedPullbackComplex g A).map (D.totalAugment.app K.obj)) ∧
            DerivedCategory.Q.map (τ.hom.app K) = e.inv ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom
              (ComplexShape.up ℤ)).app K.obj) ≫
            DerivedCategory.Q.map
              (D'.totalAugment.app ((finiteClosedPullbackComplex g A).obj K.obj)) := by
  sorry

/-- Unit-normalized comparisons are unique. Applied after canonical coefficient
composition identifications, this identifies iterated pullback comparisons with every
separately supplied comparison, including identities and automorphisms.
Source: Stacks, Tag 09AH; comparison deduction, steps 2 and 6
(blueprint: lem-sfb-closed-restriction-total-pullback).
Proof: the complementary-open localization sequence makes the actual unit epimorphic;
exact inverse image preserves that epimorphism. Precompose the two hom components with
its image. Both composites equal the target unit by the hypotheses. Cancel, then use
extensionality of natural transformations and isomorphisms. -/
theorem closedRestrictionComparison_unique {X Z Y T : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : T ⟶ Y) (g : Y ⟶ X)
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c d : finiteClosedRestriction i A ⋙ proEtaleModuleInverseImage g A ≅
      proEtaleModuleInverseImage g A ⋙
        finiteClosedRestriction j (ProEtaleTensorComparison.inverseRing g A))
    (hc : Functor.whiskerRight (finiteClosedUnit i A) (proEtaleModuleInverseImage g A) ≫
        c.hom = Functor.whiskerLeft (proEtaleModuleInverseImage g A)
          (finiteClosedUnit j (ProEtaleTensorComparison.inverseRing g A)))
    (hd : Functor.whiskerRight (finiteClosedUnit i A) (proEtaleModuleInverseImage g A) ≫
        d.hom = Functor.whiskerLeft (proEtaleModuleInverseImage g A)
          (finiteClosedUnit j (ProEtaleTensorComparison.inverseRing g A))) : c = d := by
  obtain ⟨U, hU, hqcU⟩ := hqc
  let V := ProEt.mk U.ι
  have : IsOpenImmersion V.hom := inferInstanceAs (IsOpenImmersion U.ι)
  have : QuasiCompact V.hom := hqcU
  obtain ⟨q, hq, ai, aj, hi, hj, hzi, hzj, hl, hcj, hli, hci, hseq, hfil⟩ :=
    proEtale_ringed_open_closed i V hU A
  let a := ProEtaleClosedProjection.adjunction i A
  have hepi (M : ProEtaleTensorComparison.Modules A) : Epi (a.unit.app M) := by
    have : Epi (ai.unit.app M) := (hseq M).2.1
    have he := Adjunction.unit_rightAdjointUniq_hom_app a ai M
    rw [← he] at this
    exact (epi_comp_iff_of_isIso (a.unit.app M)
      ((Adjunction.rightAdjointUniq a ai).hom.app
        ((proEtaleModuleInverseImage i A).obj M))).mp this
  let := (ProEtaleClosedProjection.adjunction g A).isLeftAdjoint
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have : Epi ((finiteClosedUnit i A).app M) := hepi M
  apply (cancel_epi ((proEtaleModuleInverseImage g A).map
    ((finiteClosedUnit i A).app M))).1
  exact congrArg (fun f ↦ f.app M) (hc.trans hd.symm)

end AlgebraicGeometry

universe vC uC vD uD
open HomologicalComplex₂
namespace AlgebraicGeometry

/-- Total comparisons respect every compatible morphism of the displayed bicomplex data.
A total comparison is any chain map given on every diagonal inclusion by the componentwise
comparison, as in the diagonal characterization of the main statement. Together with that
characterization this gives the comparison squares for parameter arrows and automorphisms.
Composed pullback comparisons use the same formula and the unit uniqueness statement; total
functoriality then gives identity, composition and associativity. Thus a small category of
displayed data gives a natural comparison, not merely unrelated comparisons at its objects.
Source: homology.tex, Tag 0133; comparison deduction, steps 4 and 6
(blueprint: lem-sfb-closed-restriction-total-pullback).
Proof: F preserves the diagonal coproducts of B, so the maps F(iota_{p,q}) jointly detect
maps out of F(Tot B)^n. Precomposed with F(iota_{p,q}), the left side is F(mu_{p,q}) followed
by the E-formula, that is F(mu_{p,q}) e_{p,q} iota'_{p,q}; the right side is
b_{p,q} nu_{p,q} iota'_{p,q} by the B-formula and the definition of Tot(nu). The stipulated
compatibility square equates them. Whiskering this equality by a diagram, inverting the
comparison isomorphisms, or applying the localization functor preserves the equality. -/
theorem closedTotalComparison_naturality
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (B E : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (B' E' : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [B.HasTotal (ComplexShape.up ℤ)] [E.HasTotal (ComplexShape.up ℤ)]
    [B'.HasTotal (ComplexShape.up ℤ)] [E'.HasTotal (ComplexShape.up ℤ)]
    [∀ n : ℤ, PreservesColimit (Discrete.functor (B.toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)) F]
    (b : (F.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj B ≅ B')
    (e : (F.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj E ≅ E')
    (μ : B ⟶ E) (ν : B' ⟶ E')
    (h : (F.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map μ ≫
      e.hom = b.hom ≫ ν)
    (τB : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (B.total (ComplexShape.up ℤ)) ⟶
      B'.total (ComplexShape.up ℤ))
    (τE : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (E.total (ComplexShape.up ℤ)) ⟶
      E'.total (ComplexShape.up ℤ))
    (hB : ∀ (p q n : ℤ) (hpq : p + q = n),
      F.map (B.ιTotal (ComplexShape.up ℤ) p q n hpq) ≫ τB.f n =
        (b.hom.f p).f q ≫ B'.ιTotal (ComplexShape.up ℤ) p q n hpq)
    (hE : ∀ (p q n : ℤ) (hpq : p + q = n),
      F.map (E.ιTotal (ComplexShape.up ℤ) p q n hpq) ≫ τE.f n =
        (e.hom.f p).f q ≫ E'.ιTotal (ComplexShape.up ℤ) p q n hpq) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (total.map μ (ComplexShape.up ℤ)) ≫ τE =
      τB ≫ total.map ν (ComplexShape.up ℤ) := by
  ext n
  apply (cancel_epi (mapTotalXIso F B (ComplexShape.up ℤ) n).hom).1
  apply total.hom_ext
  intro p q hpq
  simp only [ι_mapTotalXIso_hom_assoc]
  change F.map (B.ιTotal (ComplexShape.up ℤ) p q n hpq) ≫
      (F.map ((total.map μ (ComplexShape.up ℤ)).f n) ≫ τE.f n) =
    F.map (B.ιTotal (ComplexShape.up ℤ) p q n hpq) ≫
      (τB.f n ≫ (total.map ν (ComplexShape.up ℤ)).f n)
  rw [← Category.assoc, ← F.map_comp, ιTotal_map, F.map_comp, Category.assoc,
    hE p q n hpq, ← Category.assoc, ← Category.assoc, hB p q n hpq,
    Category.assoc, Category.assoc, ιTotal_map]
  have hpq' := congrArg (fun f ↦ (f.f p).f q) h
  change F.map ((μ.f p).f q) ≫ (e.hom.f p).f q =
    (b.hom.f p).f q ≫ (ν.f p).f q at hpq'
  rw [← Category.assoc, ← Category.assoc, hpq']

end AlgebraicGeometry
