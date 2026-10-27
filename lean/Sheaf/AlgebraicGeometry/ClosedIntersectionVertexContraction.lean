/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.ClosedIntersectionAugmentedRow
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Sheaf.AlgebraicGeometry.ClosedIntersectionGeometry
import Sheaf.AlgebraicGeometry.ClosedIntersectionRowFromSigned
import Sheaf.AlgebraicGeometry.ClosedIntersectionOpenComparison
import Sheaf.AlgebraicGeometry.ClosedIntersectionAffineVertex
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.AlgebraicGeometry.ZariskiCoverSliceModuleDetection
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Affine closed-intersection comparisons and vertex contraction

Source: Stacks Project, proetale.tex, Tags 09AA (lemma-closed-immersion),
09BM (lemma-closed-immersion-complement-retrocompact-exact), and
09AH (lemma-ses-associated-to-open); the affine base-change and signed-insertion deduction
in the DAG proof (blueprint: lem-sfb-closed-intersection-vertex-contraction).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ClosedIntersection

private theorem disjoint_open_direct_image_zero {X T : Scheme.{u}} (f : T ⟶ X)
    (U : X.ProEt) [IsOpenImmersion U.hom]
    (hU : Disjoint (Set.range U.hom) (Set.range f)) (A : Rings X)
    (H : Modules (inverseRing f A)) :
    IsZero ((inverse U.hom A).obj ((proEtaleRingedDirectImage f A).obj H)) := by
  classical
  obtain ⟨q, ⟨e⟩⟩ := proEtale_ringed_open_comparison U A
  have hz : IsZero ((SheafOfModules.overFunctor (proEtaleModuleCoefficients A) U).obj
      ((proEtaleRingedDirectImage f A).obj H)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let W := (proEtaleBaseChange f).obj V.unop.left
    have hsubset : Set.range V.unop.left.hom ⊆ Set.range U.hom := by
      rintro _ ⟨v, rfl⟩
      exact ⟨V.unop.hom.left v, congrArg (fun k : V.unop.left.left ⟶ X ↦ k v)
        V.unop.hom.w⟩
    have hdisj : Disjoint (Set.range V.unop.left.hom) (Set.range f) :=
      hU.mono_left hsubset
    let : IsEmpty W.left := Scheme.isEmpty_pullback V.unop.left.hom f hdisj
    let HH := (SheafOfModules.toSheaf _).obj H
    have hz := (HH.isTerminalOfBotCover W (ProEt.bot_mem_topology W)).isZero
    let : Subsingleton (HH.obj.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero hz
    change (x : HH.obj.obj (op W)) = 0
    exact @Subsingleton.elim (HH.obj.obj (op W)) inferInstance _ _
  have hzq : IsZero (q.functor.obj
      ((inverse U.hom A).obj ((proEtaleRingedDirectImage f A).obj H))) :=
    hz.of_iso (e.app _)
  apply (IsZero.iff_id_eq_zero _).2
  apply q.functor.map_injective
  rw [q.functor.map_id, q.functor.map_zero]
  exact hzq.eq_of_src _ _

private theorem row_zero_of_terms {X Z : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Rings X} (D : Row i W A)
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    (F : Modules A ⥤ C)
    [PreservesFiniteLimits F] (M : Modules A) (p : ℤ)
    (hz : ∀ s, IsZero (F.obj ((term i W A s).obj M))) :
    IsZero (F.obj ((D.rows.obj M).X p)) := by
  classical
  let T := fun s : Degree m p ↦ term i W A s.1
  have he := isLimitOfPreserves ((evaluation (Modules A) (Modules A)).obj M)
    (limit.isLimit (Discrete.functor T))
  have hf := isLimitOfPreserves F he
  have hz' : IsZero (F.obj ((graded i W A p).obj M)) := by
    apply hf.isZero_pt
    apply (Functor.isZero_iff _).2
    intro s
    exact hz s.as.val
  exact hz'.of_iso (F.mapIso ((D.terms p).app M))

private theorem row_support {X Z : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Rings X} (D : Row i W A) (M : Modules A) (p : ℤ)
    (hp : p < -1 ∨ (m : ℤ) ≤ p) : IsZero ((D.rows.obj M).X p) := by
  classical
  let : IsEmpty (Degree m p) := ⟨fun s ↦ by
    have hs := s.property
    have hc : s.val.card ≤ m := (Finset.card_le_univ s.val).trans_eq (Fintype.card_fin m)
    rcases hp with hp | hp <;> omega⟩
  have hz : IsZero (graded i W A p) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply Pi.hom_ext
    intro s
    exact isEmptyElim s
  exact (((evaluation (Modules A) (Modules A)).obj M).map_isZero hz).of_iso
    ((D.terms p).app M)

private theorem closed_restriction_exact {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (A : Rings X) : PreservesFiniteLimits (finiteClosedRestriction i A) ∧
      PreservesFiniteColimits (finiteClosedRestriction i A) := by
  obtain ⟨U, hU, hqcU⟩ := hqc
  let := hqcU
  let : IsOpenImmersion (ProEt.mk U.ι).hom := by
    change IsOpenImmersion U.ι
    infer_instance
  let : QuasiCompact (ProEt.mk U.ι).hom := hqcU
  obtain ⟨q, hq, ai, aj, hc, hu, hz, hz', hjl, hjc, hil, hic, hs, hf⟩ :=
    proEtale_ringed_open_closed i (ProEt.mk U.ι) hU A
  let := hil
  let := hic
  obtain ⟨ha, hl, hc, hr⟩ := (proEtale_immersion_inverseImage_preservesLimits i).2.2 A
  let := hl
  let := hc
  change PreservesFiniteLimits (_ ⋙ _) ∧ PreservesFiniteColimits (_ ⋙ _)
  exact ⟨inferInstance, inferInstance⟩

private theorem affine_acyclic_detection {X : Scheme.{u}} (A : Rings X)
    (I : Type v) (V : I → X.Opens) (hcover : (⋃ b, (V b : Set X)) = Set.univ)
    (K : CochainComplex (Modules A) ℤ) :
    K.Acyclic ↔ ∀ b, ((finiteClosedPullbackComplex (V b).ι A).obj K).Acyclic := by
  classical
  have exactness (b : I) :=
    (proEtale_immersion_inverseImage_preservesLimits (V b).ι).2.2 A
  constructor
  · intro h b
    obtain ⟨ha, hl, hc, hr⟩ := exactness b
    let := ha
    let := hl
    let := hc
    exact h.map (inverse (V b).ι A)
  · intro h p
    apply (K.exactAt_iff_isZero_homology p).2
    have hcover' : ∀ x : X, ∃ b, x ∈ V b := by
      intro x
      have hx : x ∈ ⋃ b, (V b : Set X) := by rw [hcover]; trivial
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
      exact ⟨b, hb⟩
    apply ((zariskiCoverProetaleModuleDetection X V hcover').2.2.1 A (K.homology p)).2.2.1.mpr
    intro b
    let U := ProEt.mk (V b).ι
    let : IsOpenImmersion U.hom := by
      change IsOpenImmersion (V b).ι
      infer_instance
    obtain ⟨q, ⟨e⟩⟩ := proEtale_ringed_open_comparison U A
    obtain ⟨ha, hl, hc, hr⟩ := exactness b
    let := ha
    let := hl
    let := hc
    have hz : IsZero ((inverse (V b).ι A).obj (K.homology p)) :=
      (((h b p).isZero_homology).of_iso
        ((K.sc p).mapHomologyIso (inverse (V b).ι A)).symm)
    exact (q.functor.map_isZero hz).of_iso (e.app (K.homology p)).symm

private theorem row_vanish_off_support {X Z : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Rings X} (D : Row i W A)
    (hfactor : ∀ s, Nonempty (intersection i W s ⟶ Over.mk i))
    (U : X.Opens) (hU : Set.range U.ι = (Set.range i)ᶜ) (M : Modules A) (p : ℤ) :
    IsZero ((inverse U.ι A).obj ((D.rows.obj M).X p)) := by
  obtain ⟨ha, hl, hc, hr⟩ := (proEtale_immersion_inverseImage_preservesLimits U.ι).2.2 A
  let := hl
  apply row_zero_of_terms D (inverse U.ι A) M p
  intro s
  obtain ⟨e⟩ := hfactor s
  have hsub : Set.range (intersection i W s).hom ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    exact ⟨e.left z, congrArg (fun k : (intersection i W s).left ⟶ X ↦ k z) e.w⟩
  have hdisj : Disjoint (Set.range U.ι) (Set.range (intersection i W s).hom) := by
    rw [Set.disjoint_left]
    intro x hx hz
    exact (hU ▸ hx) (hsub hz)
  let : IsOpenImmersion (ProEt.mk U.ι).hom := by
    change IsOpenImmersion U.ι
    infer_instance
  exact disjoint_open_direct_image_zero (intersection i W s).hom (ProEt.mk U.ι) hdisj A
    ((inverse (intersection i W s).hom A).obj M)

/-- Closed intersections are exact, commute with open restriction through their actual
unit-normalized comparisons, and have the stated vertex insertion contraction on affine
opens. The nonempty finite family need not cover Z. The empty summand is E_Z, and no
finiteness or flatness condition is imposed on either coefficients or modules.

Source: Stacks Project, proetale.tex, Tags 09AA, 09BM and 09AH; affine base-change and
signed-insertion consequence (blueprint: lem-sfb-closed-intersection-vertex-contraction).

Proof:
1. Complements of finite intersections are finite unions of the quasi-compact open
complements. Base change preserves quasi-compactness and closed immersions; composites
of the affine quotient maps are surjective. The ringed open-closed theorem gives exact
closed direct image, and geometric inverse image is exact. Their composites E_J and E_Z
are exact (lem-weil-pbc-proetale-ringed-open-closed,
lem-trf-geometric-inverse-image-exact, lem-weil-pbc-closed-immersion-base-change,
lem-pc-quasi-compact-base-change).
2. The signed-restriction construction gives the row and its actual units. Composite
adjunctions and the unit-preserving ordinary inverse-image comparison identify successive
restrictions; paired deletions cancel, including the augmentation square
(lem-sfb-closed-restriction-signed-refinements, def-weil-pbc-composite-adjunction,
def-sfb-proetale-ordinary-pullback-comparison, lem-weil-pbc-conjugate-iso-unit-equation).
3. On a test object T over an open V, both open restriction of i_* and direct image of
the restricted sheaf evaluate on T times_X Z. This sectionwise comparison and the
unit-normalized inverse-image comparison preserve units, hence all the restrictions.
Finite products give the displayed row comparison including its empty summand
(lem-weil-proetale-weakly-etale-localization).
4. Open restriction preserves kernels, images and cokernels. Its homology is therefore
the restricted homology. If homology vanishes on an affine open cover, separatedness
on the induced cover of each test object makes every homology section zero. This detects
acyclicity without any hypothesis on pairwise intersections of the cover
(lem-weil-pbc-module-sheaves-colimits-forgetful,
lem-weil-pbc-finite-type-restriction-exact, lem-sp-exact-functor-preserves-homology).
5. Over an affine V, its closed members are affine and qcqs. Apply the arbitrary-ring
closed base-change mate to each intersection, including Z at the empty index. Its mate
is the normalized inverse-image square comparison followed by the closed counit. The
pullback is the intersection with the chosen vertex; at the empty index it is that
vertex since it factors through the monomorphism Z into V. Naturality of the counit
and the composite-unit formula identify every face with the actual restriction unit.
Adjoining the vertex becomes restriction along an identity closed subscheme, and is
invertible, including the empty-to-singleton augmentation
(lem-sf-ring-sheaf-base-change-mates, lem-weil-pbc-proetale-ringed-open-closed).
6. Define h by the inverse of this restriction, with sign (-1) to the number of smaller
vertices in the output index, and zero if the output already contains the vertex. For
the empty output use the singleton projection and this inverse; after the augmentation
identification it is precisely the closed counit by the adjunction triangle identity.
All components are module maps.
7. If the vertex belongs to J, the sole surviving term of dh deletes that vertex and
has sign squared, hence is the identity. Otherwise the term of hd deleting the inserted
vertex is the identity. For every other deleted b, the commuting restriction square
gives the same composite map in dh and hd. Their exponents differ by one: if k is the
position of b in J, they are s_a(J)+k+[a<b] and k+s_a(J)-[b<a]. They cancel. This includes
singletons and the empty index. At degree -1 the identity is inverse-augmentation times
augmentation; at the top degree every index contains the vertex and hd is zero. Outside
the finite range both sides are maps of zero objects.
8. Off Z every closed direct image vanishes by open-closed localization, so every term
of the restricted row is zero. The units, counits, square mates, inverse isomorphisms
and finite signed matrices are all natural module maps. Thus every comparison and the
contraction are linear over the inverse-image rings and natural in M. -/
theorem closed_intersection_vertex_contraction {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (m : ℕ) (hm : 0 < m) (W : Fin m → Over X)
    (hclosed : ∀ a, IsClosedImmersion (W a).hom)
    (hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i))
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (hqcW : ∀ a, ∃ U : X.Opens,
      Set.range U.ι = (Set.range (W a).hom)ᶜ ∧ QuasiCompact U.ι)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ D : Row i W A,
      (∀ s, PreservesFiniteLimits (term i W A s) ∧
        PreservesFiniteColimits (term i W A s)) ∧
      (∀ (M : Modules A) (p : ℤ), p < -1 ∨ (m : ℤ) ≤ p →
        IsZero ((D.rows.obj M).X p)) ∧
      (∀ (I : Type v) (V : I → X.Opens), (∀ b, IsAffineOpen (V b)) →
        (⋃ b, (V b : Set X)) = Set.univ →
        ∀ K : CochainComplex (Modules A) ℤ,
          K.Acyclic ↔ ∀ b, ((finiteClosedPullbackComplex (V b).ι A).obj K).Acyclic) ∧
      ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g],
        ∃ D' : Row (pullback.fst g i) (finiteClosedPullbackFamily W g) (inverseRing g A),
          Nonempty (OpenCompatibility D g D') ∧
          (IsAffine Y →
            (∀ a, Nonempty (VertexContraction D' a)) ∧
            ∀ (U : Y.Opens),
              Set.range U.ι = (Set.range (pullback.fst g i))ᶜ →
              ∀ (M : Modules (inverseRing g A)) (p : ℤ),
                IsZero ((inverse U.ι (inverseRing g A)).obj ((D'.rows.obj M).X p))) := by
  classical
  have hgeometry := closed_intersection_geometry i W hclosed hfactor hqc hqcW
  let F : SignedClosedFamily i := ⟨m, hm, W, hclosed, hfactor, hqcW⟩
  obtain ⟨S⟩ := closedRestriction_signed_refinements i hqc A
  obtain ⟨D⟩ := row_from_signed F A (S.row F)
  refine ⟨D, ?_, row_support D, ?_, ?_⟩
  · intro s
    let := (hgeometry.1 s).1
    exact closed_restriction_exact (intersection i W s).hom (hgeometry.1 s).2.2 A
  · intro I V hV hcover K
    exact affine_acyclic_detection A I V hcover K
  · intro Y g hg
    obtain ⟨D', hcompat⟩ :=
      closed_intersection_open_comparison i W hclosed hfactor hqc hqcW A D g
    refine ⟨D', hcompat, ?_⟩
    intro hAffine
    let := hAffine
    obtain ⟨hclosed', hfactor', hqc', hqcW'⟩ := hgeometry.2 g
    refine ⟨?_, ?_⟩
    · intro a
      exact closed_intersection_affine_vertex (pullback.fst g i)
        (finiteClosedPullbackFamily W g) hclosed' hfactor' hqc' hqcW' (inverseRing g A) D' a
    · intro U hU M p
      have hgeometry' := closed_intersection_geometry (pullback.fst g i)
        (finiteClosedPullbackFamily W g) hclosed' hfactor' hqc' hqcW'
      exact row_vanish_off_support D' (fun s ↦ (hgeometry'.1 s).2.1) U hU M p

end AlgebraicGeometry.ClosedIntersection
