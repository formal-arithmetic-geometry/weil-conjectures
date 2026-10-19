module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver

import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Pretopology
import Sheaf.CategoryTheory.PeSiteSheafGluing

/-!
# Effective descent for sheaves of sets on a covering

Source: Stacks Project, `sites.tex`, Tags 04TR and 04TQ
(blueprint: lem-pe-set-sheaf-cover-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- The Hom equivalence induced by the inverse iterated-slice equivalence. -/
private noncomputable def setSheafHomEquiv {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C}
    (M N : Sheaf (J.over U) (Type (max u v))) (T : Over U) :
    (sheafHom' M N).obj (Opposite.op T) ≃
      ((J.pseudofunctorOver (Type (max u v))).presheafHom M N).obj (Opposite.op T) := by
  letI : T.iteratedSliceBackward.IsEquivalence := T.iteratedSliceEquiv.isEquivalence_inverse
  let W := (Functor.whiskeringLeft (Over T.left)ᵒᵖ (Over T)ᵒᵖ
    (Type (max u v))).obj T.iteratedSliceBackward.op
  exact (Sheaf.homEquiv
    (X := ((J.over U).overPullback (Type (max u v)) T).obj M)
    (Y := ((J.over U).overPullback (Type (max u v)) T).obj N)).trans
    ((Functor.FullyFaithful.ofFullyFaithful W).homEquiv
      (X := (((J.over U).overPullback (Type (max u v)) T).obj M).obj)
      (Y := (((J.over U).overPullback (Type (max u v)) T).obj N).obj) |>.trans
        (Sheaf.homEquiv
          (X := (J.overMapPullback (Type (max u v)) T.hom).obj M)
          (Y := (J.overMapPullback (Type (max u v)) T.hom).obj N)).symm)


set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the canonical slice-sheaf Hom equivalence.

Source: Stacks Project, sites.tex, Tag 04TQ, restriction of sheaf morphisms

Proof: the component at T precomposes a natural transformation on (C/U)/T
with the inverse slice equivalence C/T -> (C/U)/T. For a morphism S -> T,
the two composites evaluate a local transformation on the same object,
up to the canonical isomorphism with identity underlying arrow. The
pseudofunctor composition constraints are exactly the restriction maps
along this isomorphism and its inverse. Naturality of the transformation
along that isomorphism gives equality of the component maps. Extensionality
first for sheaf morphisms, then for natural transformations, then for
functions proves the displayed equality. The inverse slice equivalence
is valid for every object, including empty section sets; no cover or
nonempty index set is used. -/
private theorem setSheafHomEquiv_naturality
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U : C}
    (M N : Sheaf (J.over U) (Type (max u v)))
    {T S : (Over U)ᵒᵖ} (f : T ⟶ S) :
    (sheafHom' M N).map f ≫ (setSheafHomEquiv J M N S.unop).toIso.hom =
      (setSheafHomEquiv J M N T.unop).toIso.hom ≫
        ((J.pseudofunctorOver (Type (max u v))).presheafHom M N).map f := by
  rcases T with ⟨⟨T, rT, t⟩⟩
  rcases S with ⟨⟨S, rS, s⟩⟩
  rcases f with ⟨⟨h, r, w⟩⟩
  change S ⟶ T at h
  change rS ⟶ rT at r
  change S ⟶ U at s
  change T ⟶ U at t
  change h ≫ t = s ≫ 𝟙 U at w
  have hw : h ≫ t = s := by simpa using w
  subst s
  apply ConcreteCategory.hom_ext
  intro α
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  simp only [Pseudofunctor.presheafHom_obj, comp_apply, Equiv.toIso_hom_hom_apply,
    Pseudofunctor.presheafHom_map, Quiver.Hom.unop_op', TypeCat.hom_ofHom,
    TypeCat.Fun.coe_mk]
  dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Pseudofunctor.mapComp']
  simp only [Functor.map_id]
  change α.hom.app (Opposite.op ((Over.map
    ({ left := h, right := r, w := w } :
      ({ left := S, right := rS, hom := h ≫ t } : Over U) ⟶
        ({ left := T, right := rT, hom := t } : Over U))).obj
      ((Over.iteratedSliceBackward
        ({ left := S, right := rS, hom := h ≫ t } : Over U)).obj V.unop))) =
    M.obj.map ((Over.mapComp h t).inv.app V.unop).op ≫
      α.hom.app (Opposite.op ((Over.iteratedSliceBackward
        ({ left := T, right := rT, hom := t } : Over U)).obj
          ((Over.map h).obj V.unop))) ≫ N.obj.map ((Over.mapComp h t).hom.app V.unop).op
  let A : Over ({ left := T, right := rT, hom := t } : Over U) :=
    (Over.map
      ({ left := h, right := r, w := w } :
        ({ left := S, right := rS, hom := h ≫ t } : Over U) ⟶
          ({ left := T, right := rT, hom := t } : Over U))).obj
      ((Over.iteratedSliceBackward
        ({ left := S, right := rS, hom := h ≫ t } : Over U)).obj V.unop)
  let B := (Over.iteratedSliceBackward
    ({ left := T, right := rT, hom := t } : Over U)).obj ((Over.map h).obj V.unop)
  let e : A ≅ B := Over.isoMk ((Over.mapComp h t).app V.unop) (by
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ (V.unop.hom ≫ h) = V.unop.hom ≫ h
    exact Category.id_comp _)
  have hn : M.obj.map ((Over.mapComp h t).inv.app V.unop).op ≫ α.hom.app (Opposite.op B) =
      α.hom.app (Opposite.op A) ≫ N.obj.map ((Over.mapComp h t).inv.app V.unop).op := by
    exact α.hom.naturality e.inv.op
  rw [← Category.assoc, hn, Category.assoc, ← N.obj.map_comp, ← op_comp]
  simp only [Iso.hom_inv_id_app, op_id]
  exact ((congrArg (fun g ↦ α.hom.app (Opposite.op A) ≫ g)
    (N.obj.map_id (Opposite.op ((Over.map (h ≫ t)).obj V.unop)))).trans
      (Category.comp_id _)).symm


private theorem precoverageSite {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) : J.toPrecoverage.IsSiteForCoverings := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro X R T hR hT
    exact J.toPretopology.transitive R (fun _ f hf ↦ T f hf) hR
      (fun _ f hf ↦ hT _ f hf)
  · intro I X U a ha Y b
    refine ⟨fun i ↦ pullback b (a i), fun i ↦ pullback.fst _ _,
      fun i ↦ pullback.snd _ _, fun i ↦ IsPullback.of_hasPullback _ _, ?_⟩
    change Sieve.ofArrows _ _ ∈ J Y
    rw [Sieve.ofArrows_eq_pullback_of_isPullback _
      (fun i ↦ IsPullback.of_hasPullback b (a i))]
    exact J.pullback_stable b ha

private theorem precoverageTopology {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : J.toPrecoverage.toGrothendieck = J := by
  apply le_antisymm J.toGrothendieck_toPrecoverage_le
  intro U S hS
  simpa only [Sieve.generate_sieve] using
    J.toPrecoverage.generate_mem_toGrothendieck
      ((J.arrows_mem_toPrecoverage_iff S).2 hS)

private noncomputable def homIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C}
    (M N : Sheaf (J.over U) (Type (max u v))) :
    sheafHom' M N ≅ (J.pseudofunctorOver (Type (max u v))).presheafHom M N :=
  NatIso.ofComponents (fun T ↦ (setSheafHomEquiv J M N T.unop).toIso)
    (setSheafHomEquiv_naturality J M N)

/-- Effective descent and unique gluing for sheaves of sets along a covering.

Source: Stacks Project, `sites.tex`, Tags 04TR and 04TQ
(blueprint: lem-pe-set-sheaf-cover-descent).

The sheaves on the slice sites form the pseudofunctor
`GrothendieckTopology.pseudofunctorOver`.  Its descent-data category for the
covering family consists of sheaves `F_a` on the slices, overlap isomorphisms
`φ_ab`, and the triple-overlap cocycle.  The asserted equivalence says exactly
that such data is induced by a sheaf `F` on `C/U`, with isomorphisms
`e_a : F|_{U_a} ≅ F_a` satisfying `e_b = φ_ab ≫ e_a` on overlaps.  Full
faithfulness of the same equivalence is the final assertion: compatible local
maps between two sheaves glue to one and only one global map.

Proof: construct the compatible-tuples sheaf by the sectionwise equalizer of
products, verify the local graph maps are inverse isomorphisms using the
cocycle, and glue compatible morphisms by the sheaf equalizer axiom, as in
Tags 04TR and 04TQ. More precisely: (1) base-change the local sheaves to
the slices over `U` and verify that the resulting component presheaves are
sheaves; (2) take the sectionwise limit of their products and equalize the
two overlap maps, obtaining the compatible-tuples sheaf; (3) restrict the
cocycle to the triple diagonal and cancel the resulting automorphism to get
the diagonal normalization; (4) define the local comparison maps by pulling
back along graph sections, and define their inverses from the cocycle; (5)
check both inverse identities and naturality, hence obtain the local
isomorphisms; (6) pull the tuple equations back along the double-overlap
graph to obtain `e_b = φ_ab ≫ e_a`; (7) for compatible local morphisms,
amalgamate their values using the sheaf equalizer axiom and prove
naturality by separatedness; (8) prove restriction and uniqueness by the
same equalizer axiom. The component-sheaf and equalizer steps use
`def-weil-pbc-sites-and-cohomology`, `def-pur-localized-ringed-site`,
`def-weil-size-convention`, and
`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`. -/
theorem setSheafCoverDescent
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C)
    {I : Type (max u v)} (U : C) (X : I → C)
    (f : ∀ i, X i ⟶ U)
    (hcov : Sieve.ofArrows X f ∈ J U) :
    (∀ D : (J.pseudofunctorOver (Type (max u v))).DescentData f,
      ∃ F : Sheaf (J.over U) (Type (max u v)),
        Nonempty (D ≅
          ((J.pseudofunctorOver (Type (max u v))).toDescentData f).obj F)) ∧
      Nonempty (((J.pseudofunctorOver (Type (max u v))).toDescentData f).FullyFaithful) := by
  constructor
  · have h := peSiteSheafGluing J.toPrecoverage (precoverageSite J) U X f hcov
    rw [precoverageTopology J] at h
    exact h
  · let : (J.pseudofunctorOver (Type (max u v))).IsPrestack J :=
      { isSheaf := fun M N ↦
          (Presheaf.isSheaf_of_iso_iff (homIso J M N)).1 (sheafHom M N).property }
    exact ⟨(J.pseudofunctorOver (Type (max u v))).fullyFaithfulToDescentData f hcov⟩

end CategoryTheory
