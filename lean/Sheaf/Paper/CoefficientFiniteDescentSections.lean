/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Finite coefficient descent on quasi-compact pro-étale objects

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-sections;
Stacks Project, Sites, Tag 0738 (blueprint: det-lem-coefficient-finite-descent-sections).

The three statements give clause (1) for sets and abelian groups and clause (2)
for the existing finite-subextension coefficient sheaves. No quasi-separatedness
is imposed in the injective-transition case or in coefficient descent.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The section-colimit comparison for sets is injective on a quasi-compact object,
and bijective if the object is quasi-separated or all transitions are sectionwise injective.
The sheaf colimit is supplied as an arbitrary cocone `c` with universal property `hc`.
Source: Stacks Project, Sites, Tag 0738(2)--(4), and the corrected blueprint node
(blueprint: det-lem-coefficient-finite-descent-sections), clause (1).

Proof: (1) Form the sectionwise presheaf colimit; sheafification is the sheaf colimit
by its adjunction (lem-weil-pbc-presheaf-colimits-sectionwise,
def-weil-pbc-sheafification). Filteredness gives representatives and eventual equality,
including equalization of parallel arrows (def-weil-pbc-category-colimit).
(2) An fpqc covering of a quasi-compact pro-etale object has a finite affine refinement
(sk-def-pe-site, def-weil-pbc-quasi-compact-scheme, def-weil-pbc-sites-and-cohomology).
(3) Equal images are equal locally by lem-weil-pbc-site-sheafification-sections-local.
On the finite refinement, move the equality witnesses to a common stage and use the
stage sheaf's separatedness. This proves injectivity.
(4) For a quasi-separated object, pairwise overlaps of affine covering objects are
quasi-compact: base change its quasi-compact diagonal to their affine product over Z
(def-weil-quasi-separated-morphism, lem-pc-quasi-compact-base-change,
lem-weil-pbc-fibre-product-affine-spectra). Lift a section locally, refine finitely,
move to a common stage, and use (3) on the finitely many overlaps. A further common
stage makes the representatives compatible, and the sheaf condition glues them.
(5) Alternatively, injective transitions make every stage inject into its presheaf
colimit, using filteredness to equalize parallel arrows. Local equality and the stage
sheaf condition then make every stage inject into the sheaf colimit on every object.
Move local representatives on a finite cover to one stage; they agree on all overlaps
by this injectivity and glue, without assuming quasi-compact overlaps. -/
theorem set_sections_filtered_colimit (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    (c : Cocone F) (hc : IsColimit c) :
    Function.Injective
        (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
          (Type (max (u + 1) v))).obj (op V)).mapCocone c)) ∧
      ((QuasiSeparated (toSpecZ V.left) ∨
          ∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
            Function.Injective ((F.map f).hom.app (op U))) →
        Function.Bijective
          (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
            (Type (max (u + 1) v))).obj (op V)).mapCocone c))) := by
  sorry

/-- The same section-colimit comparison for abelian sheaves, with the same two
sufficient conditions for bijectivity. In both comparisons, `c` with `hc` is an
arbitrary chosen sheaf-colimit cocone; the source is the chosen section-group colimit.
Source: Stacks Project, Sites, Tags 0738 and 03CO(4), and blueprint clause (1)
(blueprint: det-lem-coefficient-finite-descent-sections).

Proof: Use the set comparison just stated (steps (1)--(5) of this node).
The presheaf colimit is sectionwise (lem-weil-pbc-presheaf-colimits-sectionwise),
and forgetting abelian groups preserves filtered colimits
(lem-weil-pbc-abelian-groups-forget-filtered-colimits).
Abelian sheafification has the underlying set sheafification
(lem-pc-sites-sheafification-underlying-sets), so the underlying comparison is
precisely the set comparison, with unchanged compactness and transition hypotheses.
This also agrees with the abelian sheaf colimit of
lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact. -/
theorem abelian_sections_filtered_colimit (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (c : Cocone F) (hc : IsColimit c) :
    Function.Injective
        (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
          AddCommGrpCat.{max (u + 1) v}).obj (op V)).mapCocone c)) ∧
      ((QuasiSeparated (toSpecZ V.left) ∨
          ∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
            Function.Injective ((F.map f).hom.app (op U))) →
        Function.Bijective
          (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
            AddCommGrpCat.{max (u + 1) v}).obj (op V)).mapCocone c))) := by
  let J := Scheme.ProEt.topology X
  let A := AddCommGrpCat.{max (u + 1) v}
  let U := forget A
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} U :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, max (u + 1) v,
      u + 1, max (u + 1) v} U
  have : PreservesFilteredColimitsOfSize.{v, v} U :=
    preservesFilteredColimitsOfSize_shrink.{v, max (u + 1) v,
      v, max (u + 1) v} U
  have : J.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification J U
  have : PreservesColimitsOfShape I (sheafCompose J U) := by
    rw [(sheafificationAdjunction J A).preservesColimitsOfShape_iff]
    exact preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J U (sheafificationAdjunction J A)
        (sheafificationAdjunction J (Type (max (u + 1) v))))
  let D := F ⋙ (sheafSections J A).obj (op V)
  let d := ((sheafSections J A).obj (op V)).mapCocone c
  let d' := ((sheafSections J (Type (max (u + 1) v))).obj (op V)).mapCocone
    ((sheafCompose J U).mapCocone c)
  have hs := set_sections_filtered_colimit X V I (F ⋙ sheafCompose J U)
    ((sheafCompose J U).mapCocone c) (isColimitOfPreserves (sheafCompose J U) hc)
  have he : colimit.post D U ≫ U.map (colimit.desc D d) =
      colimit.desc _ d' := colimit.post_desc D U d
  have hi : Function.Bijective (colimit.post D U) :=
    (isIso_iff_bijective _).mp inferInstance
  have he' : (fun x ↦ colimit.desc _ d' x) =
      (fun x ↦ colimit.desc D d x) ∘ (colimit.post D U) := by
    funext x
    exact (ConcreteCategory.congr_hom he x).symm
  change Function.Injective (fun x ↦ colimit.desc _ d' x) ∧ _ at hs
  rw [he'] at hs
  refine ⟨?_, ?_⟩
  · exact hs.1.of_comp_right hi.2
  · intro h
    have hb := hs.2 h
    have hb' : Function.Bijective
        ((fun x ↦ colimit.desc D d x) ∘ (colimit.post D U)) := by
      rw [← he']
      exact hb
    exact ⟨hb'.1.of_comp_right hi.2, hb'.2.of_comp⟩


private theorem coefficient_section_injective (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (V : X.ProEt) :
    Function.Injective ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V)) := by
  have : Mono (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E) := by
    apply Sheaf.mono_of_injective
    intro S a b h
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    apply Subtype.val_injective
    exact congrArg (fun z ↦ (z.down : C(S.unop, PadicAlgCl l)) s) h
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  have : Mono (padicSubfieldRingObjToPadicAlgCl X l E) :=
    (upperStarFromPoint X).map_mono _
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- Coefficient inclusions are injective on sections, their ranges cover the algebraic
closure coefficient sections, and every finite set or finite family of finite matrices
has entries in one finite subextension. No quasi-separatedness is required.
Source: blueprint main-20261015, coefficient finite descent, clause (2)
(blueprint: det-lem-coefficient-finite-descent-sections).

Proof: (7) On profinite test objects, the condensed coefficient inclusion is injective
because postcomposition with a subfield inclusion is injective. The resulting sheaf
morphism is a monomorphism. Mathlib's finite-limit preservation for the constructed
point inverse image and scheme inverse image shows that their composite preserves
this monomorphism. Evaluation preserves monomorphisms, giving sectionwise injectivity.
(8) Use the already proved abelian coefficient colimit
`isColimitPadicAlgClRingObjCocone`. Its transition maps are injective since their
composites with the coefficient inclusions are injective. Apply the abelian comparison
above in its injective-transition case. Surjectivity of that comparison and stage
representatives for the section-group colimit give the union assertion.
(9) Induct on a finite set. The empty set uses the base field, and an insertion uses
a common upper bound of the field for the new element and the previous field.
Naturality of the coefficient inclusions transports both ranges into the common
field. For a finite family of finite matrices, apply this result to the range of
the function on the finite dependent sum of all entry positions. -/
theorem coefficient_finite_descent_sections (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (V : X.ProEt) [CompactSpace V.left] :
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Function.Injective ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (Set.univ = ⋃ E : PadicAlgCl.FiniteIntermediateField l,
      Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (∀ S : Set ((padicAlgClRingObj X l).obj.obj (op V)), S.Finite →
      ∃ E : PadicAlgCl.FiniteIntermediateField l,
        S ⊆ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (∀ (K : Type v) [Finite K] (rows : K → Type w) (cols : K → Type z)
      [∀ k : K, Finite (rows k)] [∀ k : K, Finite (cols k)]
      (M : ∀ k : K, Matrix (rows k) (cols k)
        ((padicAlgClRingObj X l).obj.obj (op V))),
      ∃ E : PadicAlgCl.FiniteIntermediateField l,
        ∀ (k : K) (i : rows k) (j : cols k),
          M k i j ∈ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) := by
  classical
  let D := Profinite.padicSubfieldRingObjFunctor.{u} l ⋙ upperStarFromPoint X
  let c := padicAlgClRingObjCocone X l
  let ev := (sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V)
  have htrans : ∀ (i j : PadicAlgCl.FiniteIntermediateField l) (f : i ⟶ j)
      (U : X.ProEt), Function.Injective ((D.map f).hom.app (op U)) := by
    intro i j f U a b hab
    apply coefficient_section_injective X l i U
    have he := congrArg (fun g ↦ g.hom.app (op U))
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X l (leOfHom f))
    exact (ConcreteCategory.congr_hom he a).symm.trans
      ((congrArg ((padicSubfieldRingObjToPadicAlgCl X l j).hom.app (op U)) hab).trans
        (ConcreteCategory.congr_hom he b))
  have hbij := (abelian_sections_filtered_colimit X V
    (PadicAlgCl.FiniteIntermediateField l) D c (isColimitPadicAlgClRingObjCocone X l)).2
      (Or.inr htrans)
  have hrep (s : (padicAlgClRingObj X l).obj.obj (op V)) :
      ∃ E, s ∈ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V)) := by
    obtain ⟨t, ht⟩ := hbij.2 s
    have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    obtain ⟨E, a, ha⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget AddCommGrpCat.{u + 1})
        (colimit.isColimit (D ⋙ ev))) t
    refine ⟨E, a, ?_⟩
    have he := ConcreteCategory.congr_hom (colimit.ι_desc (ev.mapCocone c) E) a
    exact he.symm.trans ((congrArg (colimit.desc (D ⋙ ev) (ev.mapCocone c)) ha).trans ht)
  have hmono {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
      Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V)) ⊆
      Set.range ((padicSubfieldRingObjToPadicAlgCl X l F).hom.app (op V)) := by
    rintro s ⟨a, rfl⟩
    refine ⟨(padicSubfieldRingObjMap X l h).hom.app (op V) a, ?_⟩
    exact ConcreteCategory.congr_hom
      (congrArg (fun g ↦ g.hom.app (op V))
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X l h)) a
  have hfinite : ∀ S : Set ((padicAlgClRingObj X l).obj.obj (op V)), S.Finite →
      ∃ E, S ⊆ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V)) := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact ⟨Classical.arbitrary _, Set.empty_subset _⟩
    | @insert s S hs hS ih =>
      obtain ⟨E, hE⟩ := hrep s
      obtain ⟨F, hF⟩ := ih
      obtain ⟨G, hEG, hFG⟩ := exists_ge_ge E F
      exact ⟨G, Set.insert_subset ((hmono hEG) hE) (fun a ha ↦ hmono hFG (hF ha))⟩
  refine ⟨fun E ↦ coefficient_section_injective X l E V, ?_, hfinite, ?_⟩
  · symm
    apply Set.eq_univ_iff_forall.mpr
    intro s
    obtain ⟨E, hE⟩ := hrep s
    exact Set.mem_iUnion.mpr ⟨E, hE⟩
  · intro K _ rows cols _ _ M
    let entries : (Σ k : K, rows k × cols k) →
        (padicAlgClRingObj X l).obj.obj (op V) := fun p ↦ M p.1 p.2.1 p.2.2
    obtain ⟨E, hE⟩ := hfinite (Set.range entries) (Set.finite_range entries)
    exact ⟨E, fun k i j ↦ hE ⟨⟨k, i, j⟩, rfl⟩⟩


end AlgebraicGeometry.ProEtale
