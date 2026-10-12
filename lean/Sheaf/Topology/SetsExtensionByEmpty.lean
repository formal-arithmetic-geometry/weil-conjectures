module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Extension by the empty set

Source: `literature/stacks-project/sheaves.tex`, Definition 00A2 (blueprint:
`def-weil-pbc-sets-extension-by-empty`); the sheaf of locally constant maps as in
Definition 006W and Modules, Section 0CAG.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace TopologicalSpace.Opens Opposite

namespace TopCat

noncomputable section

/-- Transporting a morphism in both objects is conjugation by equality morphisms. -/
private theorem cast_hom {A B A' B' : Type u} (hA : A = A') (hB : B = B')
    (h : (A' ⟶ B') = (A ⟶ B)) (f : A ⟶ B) :
    h.mpr f = eqToHom hA.symm ≫ f ≫ eqToHom hB := by
  subst A'
  subst B'
  simp

variable {X : TopCat.{u}} (U : Opens X)

/-- The restriction maps of the presheaf `j_{U,p!} G`: the restriction of `G` when the source
open lies in `U`, the empty map otherwise.
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
def extensionByEmptyMap (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    (@ite _ (unop V ≤ U) (Classical.propDecidable _)
      (G.presheaf.obj (op ((Opens.map U.inclusion').obj (unop V)))) PEmpty) ⟶
      (@ite _ (unop W ≤ U) (Classical.propDecidable _)
        (G.presheaf.obj (op ((Opens.map U.inclusion').obj (unop W)))) PEmpty) := by
  classical
  by_cases hV : unop V ≤ U
  · have hW : unop W ≤ U := le_trans i.unop.le hV
    simp only [if_pos hV, if_pos hW]
    exact G.presheaf.map ((Opens.map U.inclusion').map i.unop).op
  · rw [if_neg hV]
    by_cases hW : unop W ≤ U
    · rw [if_pos hW]
      exact TypeCat.ofHom (fun x : PEmpty => PEmpty.elim x)
    · rw [if_neg hW]
      exact TypeCat.ofHom (fun x : PEmpty => PEmpty.elim x)

/-- The restriction along the identity is the identity: that of `G`, or of the empty set.
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
theorem extensionByEmptyMap_id (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    (V : (Opens X)ᵒᵖ) :
    extensionByEmptyMap U G (𝟙 V) = 𝟙 _ := by
  classical
  by_cases hV : unop V ≤ U
  · simp only [extensionByEmptyMap, dif_pos hV]
    rw [cast_hom (if_pos hV).symm (if_pos hV).symm]
    simp
  · have h : IsEmpty (if unop V ≤ U then
        G.presheaf.obj (op ((Opens.map U.inclusion').obj (unop V))) else PEmpty) := by
      rw [if_neg hV]
      infer_instance
    ext x
    exact isEmptyElim x

/-- Restrictions compose: if the largest open lies in `U` all three are restrictions of `G`,
otherwise both sides are maps out of the empty set.
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
theorem extensionByEmptyMap_comp (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U))
    {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) :
    extensionByEmptyMap U G (f ≫ g) =
      extensionByEmptyMap U G f ≫ extensionByEmptyMap U G g := by
  classical
  by_cases hV : unop V ≤ U
  · have hW : unop W ≤ U := le_trans f.unop.le hV
    have hZ : unop Z ≤ U := le_trans g.unop.le hW
    simp only [extensionByEmptyMap, dif_pos hV, dif_pos hW]
    rw [cast_hom (if_pos hV).symm (if_pos hZ).symm,
      cast_hom (if_pos hV).symm (if_pos hW).symm,
      cast_hom (if_pos hW).symm (if_pos hZ).symm]
    simp
  · have h : IsEmpty (if unop V ≤ U then
        G.presheaf.obj (op ((Opens.map U.inclusion').obj (unop V))) else PEmpty) := by
      rw [if_neg hV]
      infer_instance
    ext x
    exact isEmptyElim x

/-- The presheaf `j_{U,p!} G`: `G(V)` on opens `V ⊆ U` and empty elsewhere.
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
def extensionByEmptyPresheafObj (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) :
    Presheaf (Type u) X where
  obj V := @ite _ (unop V ≤ U) (Classical.propDecidable _)
    (G.presheaf.obj (op ((Opens.map U.inclusion').obj (unop V)))) PEmpty
  map i := extensionByEmptyMap U G i
  map_id := extensionByEmptyMap_id U G
  map_comp := extensionByEmptyMap_comp U G

/-- The component of `j_{U,p!} α` at `V`: `α_V` when `V ⊆ U`, the identity of the empty set
otherwise. Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
def extensionByEmptyPresheafApp {G G' : TopCat.Sheaf (Type u) ((toTopCat X).obj U)}
    (α : G ⟶ G') (V : (Opens X)ᵒᵖ) :
    (extensionByEmptyPresheafObj U G).obj V ⟶ (extensionByEmptyPresheafObj U G').obj V := by
  classical
  by_cases hV : unop V ≤ U
  · simp only [extensionByEmptyPresheafObj, if_pos hV]
    exact α.hom.app (op ((Opens.map U.inclusion').obj (unop V)))
  · simp only [extensionByEmptyPresheafObj, if_neg hV]
    exact 𝟙 PEmpty

/-- Naturality of `j_{U,p!} α`: on opens inside `U` it is the naturality of `α`, otherwise both
composites are maps out of the empty set.
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
theorem extensionByEmptyPresheafApp_naturality
    {G G' : TopCat.Sheaf (Type u) ((toTopCat X).obj U)} (α : G ⟶ G')
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    (extensionByEmptyPresheafObj U G).map i ≫ extensionByEmptyPresheafApp U α W =
      extensionByEmptyPresheafApp U α V ≫ (extensionByEmptyPresheafObj U G').map i := by
  classical
  by_cases hV : unop V ≤ U
  · have hW : unop W ≤ U := le_trans i.unop.le hV
    simp only [extensionByEmptyPresheafObj, extensionByEmptyMap,
      extensionByEmptyPresheafApp, dif_pos hV, dif_pos hW]
    rw [cast_hom (if_pos hV).symm (if_pos hW).symm,
      cast_hom (if_pos hW).symm (if_pos hW).symm,
      cast_hom (if_pos hV).symm (if_pos hV).symm,
      cast_hom (if_pos hV).symm (if_pos hW).symm]
    simp [Category.assoc]
  · have h : IsEmpty ((extensionByEmptyPresheafObj U G).obj V) := by
      simp only [extensionByEmptyPresheafObj, if_neg hV]
      infer_instance
    ext x
    exact isEmptyElim x

/-- The morphism of presheaves `j_{U,p!} α`.
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
def extensionByEmptyPresheafHom {G G' : TopCat.Sheaf (Type u) ((toTopCat X).obj U)}
    (α : G ⟶ G') : extensionByEmptyPresheafObj U G ⟶ extensionByEmptyPresheafObj U G' where
  app := extensionByEmptyPresheafApp U α
  naturality _ _ i := extensionByEmptyPresheafApp_naturality U α i

/-- `j_{U,p!}` preserves identities (componentwise `id_V` or `id_∅`).
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
theorem extensionByEmptyPresheafHom_id (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) :
    extensionByEmptyPresheafHom U (𝟙 G) = 𝟙 _ := by
  classical
  apply NatTrans.ext
  funext V
  change extensionByEmptyPresheafApp U (𝟙 G) V = 𝟙 _
  by_cases hV : unop V ≤ U
  · simp only [extensionByEmptyPresheafApp, dif_pos hV]
    rw [cast_hom (if_pos hV).symm (if_pos hV).symm]
    simp [TopCat.Sheaf, extensionByEmptyPresheafObj]
  · have h : IsEmpty ((extensionByEmptyPresheafObj U G).obj V) := by
      simp only [extensionByEmptyPresheafObj, if_neg hV]
      infer_instance
    ext x
    exact isEmptyElim x

/-- `j_{U,p!}` preserves composition (componentwise).
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
theorem extensionByEmptyPresheafHom_comp
    {G G' G'' : TopCat.Sheaf (Type u) ((toTopCat X).obj U)} (α : G ⟶ G') (β : G' ⟶ G'') :
    extensionByEmptyPresheafHom U (α ≫ β) =
      extensionByEmptyPresheafHom U α ≫ extensionByEmptyPresheafHom U β := by
  classical
  apply NatTrans.ext
  funext V
  change extensionByEmptyPresheafApp U (α ≫ β) V =
    extensionByEmptyPresheafApp U α V ≫ extensionByEmptyPresheafApp U β V
  by_cases hV : unop V ≤ U
  · simp only [extensionByEmptyPresheafApp, dif_pos hV]
    rw [cast_hom (if_pos hV).symm (if_pos hV).symm,
      cast_hom (if_pos hV).symm (if_pos hV).symm,
      cast_hom (if_pos hV).symm (if_pos hV).symm]
    simp [TopCat.Sheaf, Category.assoc]
  · have h : IsEmpty ((extensionByEmptyPresheafObj U G).obj V) := by
      simp only [extensionByEmptyPresheafObj, if_neg hV]
      infer_instance
    ext x
    exact isEmptyElim x

/-- The functor `j_{U,p!}` from sheaves of sets on `U` to presheaves of sets on `X`.
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
def extensionByEmptyPresheaf :
    TopCat.Sheaf (Type u) ((toTopCat X).obj U) ⥤ Presheaf (Type u) X where
  obj G := extensionByEmptyPresheafObj U G
  map α := extensionByEmptyPresheafHom U α
  map_id G := extensionByEmptyPresheafHom_id U G
  map_comp α β := extensionByEmptyPresheafHom_comp U α β

/-- Extension by the empty set `j_{U!}`: the sheafification of `j_{U,p!}`, on objects and on
morphisms; the map `θ_G : j_{U,p!} G → j_{U!} G` is
`toSheafify (Opens.grothendieckTopology X) ((extensionByEmptyPresheaf U).obj G)`.
Source: Stacks, Definition 00A2 (blueprint: def-weil-pbc-sets-extension-by-empty). -/
def extensionByEmpty : TopCat.Sheaf (Type u) ((toTopCat X).obj U) ⥤ X.Sheaf (Type u) :=
  extensionByEmptyPresheaf U ⋙ presheafToSheaf (Opens.grothendieckTopology X) (Type u)

/-- `j_{U!} S = j_{U!}(S_U)`, where `S_U` is the sheaf of locally constant maps to `S` on `U`,
i.e. the continuous maps to `S` with the discrete topology (`TopCat.sheafToTop`).
Source: Stacks, Definitions 00A2 and 006W, Modules 0CAG
(blueprint: def-weil-pbc-sets-extension-by-empty). -/
def extensionByEmptyConstant (S : Type u) : X.Sheaf (Type u) :=
  (extensionByEmpty U).obj (sheafToTop (X := (toTopCat X).obj U) (TopCat.discrete.obj S))

end

end TopCat
