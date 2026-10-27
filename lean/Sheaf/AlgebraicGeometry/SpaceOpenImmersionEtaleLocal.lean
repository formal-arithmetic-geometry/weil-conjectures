module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceFpqcOpenImmersionDescent
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.MorphismProperty.Representable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Open immersions of algebraic spaces are etale-local on the target

Source: Stacks Project, Spaces and Morphisms, Tag 03M4, and Spaces Descent,
Tag 041X (blueprint: lem-trf-space-open-immersion-etale-local).
This stage-2 delivery records the statement with its proof intentionally postponed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

-- A representable fppf sheaf has its scheme diagonal and the identity atlas.
private theorem scheme_isAlgebraicSpace {S : Scheme.{u}} (T : Over S) :
    IsAlgebraicSpace ((Scheme.fppfTopology.over S).yoneda.obj T) := by
  constructor
  · have hd : yoneda.relativelyRepresentable (Limits.diag (yoneda.obj T)) := by
      apply Functor.relativelyRepresentable.diag_of_map_from_obj
      intro U g
      obtain ⟨g, rfl⟩ := yoneda.map_surjective g
      exact Functor.relativelyRepresentable.map yoneda g
    intro U a
    obtain ⟨V, p, q, h⟩ := hd a
    exact ⟨V, p, q, h, trivial⟩
  · refine ⟨T, 𝟙 _, ?_, ?_⟩
    · intro U a
      exact ⟨U, 𝟙 U, a, IsPullback.of_vert_isIso ⟨by simp⟩, by
        change Etale (𝟙 U.left)
        infer_instance⟩
    · intro U a
      exact ⟨U, 𝟙 U, a, IsPullback.of_vert_isIso ⟨by simp⟩, by
        change Surjective (𝟙 U.left)
        infer_instance⟩

/-- Open immersions of algebraic spaces descend along a jointly surjective etale
family of scheme maps. The proof is the compatible-open descent and fppf sheaf
argument of Tags 03M4 and 041X, using the open-subscheme fpqc descent lemma
(lem-weil-pbc-open-subscheme-fpqc-descent), the etale-to-fpqc comparison
(lem-weil-pbc-fpqc-finer-than-etale), and base change of open immersions
(lem-weil-pbc-open-immersion-base-change).
(blueprint: lem-trf-space-open-immersion-etale-local) -/
theorem isOpenImmersion_of_etale_cover
    {S : Scheme.{u}} {X P : AlgebraicSpace S} (a : X ⟶ P)
    (I : Type u) (P_i : I → Over S)
    (p_i : ∀ i, yoneda.obj (P_i i) ⟶ P.obj.obj)
    (h_etale : ∀ i, IsEtale (p_i i))
    (h_joint : ∀ (T : Over S) (x : P.obj.obj.obj (Opposite.op T)),
      ∃ (R : Sieve T.left), R ∈ Scheme.fppfTopology T.left ∧
        ∀ (U : Over S) (f : U ⟶ T), R f.left →
          ∃ (i : I) (y : (yoneda.obj (P_i i)).obj (Opposite.op U)),
            (p_i i).app (Opposite.op U) y = P.obj.obj.map f.op x)
    (h_open : ∀ i,
      AlgebraicSpace.IsRepresentableWith
        (fun _ _ q => IsOpenImmersion q.left)
        (pullback.snd a.hom.hom (p_i i))) :
    AlgebraicSpace.IsRepresentableWith
      (fun _ _ q => IsOpenImmersion q.left) a.hom.hom := by
  classical
  intro T t
  choose Tᵢ q c hc hq using fun i ↦ h_etale i T t
  have hsurj : ∀ z : T.left, ∃ i, ∃ w : (Tᵢ i).left, (q i).left w = z := by
    intro z
    obtain ⟨R, hR, hlocal⟩ := h_joint T (t.app (op T) (𝟙 T))
    obtain ⟨V, f, hf, _, _, v, hv⟩ :=
      Scheme.exists_flat_mem_of_mem_fppfTopology hR z
    let E : Over S := Over.mk (f ≫ T.hom)
    let f' : E ⟶ T := Over.homMk f
    obtain ⟨i, y, hy⟩ := hlocal E f' hf
    have he : (p_i i).app (op E) y = t.app (op E) f' := by
      rw [hy]
      simpa using (t.naturality_apply f'.op (𝟙 T)).symm
    obtain ⟨w, _, hw⟩ := Types.exists_of_isPullback ((hc i).app (op E)) y f' he
    refine ⟨i, w.left v, ?_⟩
    have hw' : w ≫ q i = f' := hw
    have hw'' := congrArg (fun k : E ⟶ T ↦ k.left v) hw'
    exact hw''.trans hv
  have hcover : Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (q i).left) ∈
      Scheme.fpqcPrecoverage T.left := by
    apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
    change Presieve.ofArrows _ _ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) _
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hsurj, fun i ↦ by
      have := hq i
      exact ⟨inferInstance, inferInstance⟩⟩
  let Y : AlgebraicSpace S :=
    ⟨(Scheme.fppfTopology.over S).yoneda.obj T, scheme_isAlgebraicSpace T⟩
  let b : Y ⟶ P := ObjectProperty.homMk ⟨t⟩
  let Z : AlgebraicSpace S :=
    ⟨Limits.pullback a.hom b.hom, (fibreProduct_isAlgebraicSpace X Y P a b).1⟩
  let r : Z.obj.obj ⟶ yoneda.obj T := (pullback.snd a.hom b.hom).hom
  have hZ : IsPullback (pullback.fst a.hom b.hom).hom r a.hom.hom t :=
    (IsPullback.of_hasPullback a.hom b.hom).map
      (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u))
  have hlocal : ∀ i, ∃ (U : Over S) (j : U ⟶ Tᵢ i)
      (e : Limits.pullback r (yoneda.map (q i)) ≅ yoneda.obj U),
      IsOpenImmersion j.left ∧
        pullback.snd r (yoneda.map (q i)) = e.hom ≫ yoneda.map j := by
    intro i
    obtain ⟨U, j, s, hs, hj⟩ := h_open i (Tᵢ i) (c i)
    have hs' : IsPullback (s ≫ pullback.fst a.hom.hom (p_i i)) (yoneda.map j)
        a.hom.hom (yoneda.map (q i) ≫ t) := by
      have hh := hs.paste_horiz (IsPullback.of_hasPullback a.hom.hom (p_i i))
      rw [(hc i).w] at hh
      exact hh
    have hfinal := hs'.of_right' hZ
    exact ⟨U, j, hfinal.isoPullback.symm, hj, by simp⟩
  obtain ⟨U, j, hj, e, he⟩ :=
    exists_scheme_openImmersion_of_fpqc_cover T Z r Tᵢ q hcover hlocal
  refine ⟨U, j, e.inv ≫ (pullback.fst a.hom b.hom).hom, ?_, hj⟩
  have he' : e.inv ≫ r = yoneda.map j := by
    rw [he]
    simp
  exact hZ.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using he') (by simp) (by simp)

end AlgebraicGeometry.AlgebraicSpace
