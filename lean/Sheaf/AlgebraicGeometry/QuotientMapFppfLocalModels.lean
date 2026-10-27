module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.EtaleRelationKernelPair
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-! # Fppf local models of a quotient map

Source: Stacks Project, Spaces, Tag 0265, first representability step, with the
relation projections interchanged (blueprint: lem-trf-quotient-map-fppf-local-models).

The quotient is specified by its sheafification universal property, as in
`etale_relation_kernel_pair`. The coequalizer is the pointwise quotient presheaf.
The helper constructs the actual presheaf of lifts, without choosing any lifts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- On the big site over `T`, the presheaf of maps into `U` whose quotient image
is the prescribed section. Restriction is precomposition, and its equality proof
is transported by naturality. Source: Stacks Project, Spaces, Tag 0265, first
representability step (blueprint: lem-trf-quotient-map-fppf-local-models). -/
def quotientMapFibre {S : Scheme.{u}} {U : Over S} (T : Over S)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (q : yoneda.obj U ⟶ F.obj) (a : yoneda.obj T ⟶ F.obj) :
    (Over T.left)ᵒᵖ ⥤ Type u where
  obj W := { b : (Over.map T.hom).obj W.unop ⟶ U //
    q.app (op ((Over.map T.hom).obj W.unop)) b =
      a.app (op ((Over.map T.hom).obj W.unop)) (Over.homMk W.unop.hom) }
  map {W V} f := ↾fun b ↦ ⟨(Over.map T.hom).map f.unop ≫ b.val, by
    have hq := q.naturality_apply ((Over.map T.hom).map f.unop).op b.val
    have ha := a.naturality_apply ((Over.map T.hom).map f.unop).op
      (Over.homMk W.unop.hom)
    have hw : (Over.map T.hom).map f.unop ≫ Over.homMk W.unop.hom =
        (Over.homMk V.unop.hom : (Over.map T.hom).obj V.unop ⟶ T) := by
      ext
      exact Over.w f.unop
    change q.app _ ((Over.map T.hom).map f.unop ≫ b.val) =
      F.obj.map ((Over.map T.hom).map f.unop).op (q.app _ b.val) at hq
    change a.app _ ((Over.map T.hom).map f.unop ≫ Over.homMk W.unop.hom) =
      F.obj.map ((Over.map T.hom).map f.unop).op
        (a.app _ (Over.homMk W.unop.hom)) at ha
    rw [hq, b.property, ← ha, hw]⟩
  map_id W := by
    apply ConcreteCategory.hom_ext
    intro b
    apply Subtype.ext
    change (Over.map T.hom).map (𝟙 W).unop ≫ b.val = b.val
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro b
    apply Subtype.ext
    change (Over.map T.hom).map (f ≫ g).unop ≫ b.val =
      (Over.map T.hom).map g.unop ≫ ((Over.map T.hom).map f.unop ≫ b.val)
    simp

/-- The fibre of the fppf quotient map is a sheaf and has the specified local
scheme models. The universal property `hη` expresses precisely sheafification
of the quotient presheaf; it does not assume sheafification of all small-valued
presheaves on the big site. Source: Stacks Project, Spaces, Tag 0265, first
representability step, with `s,t` interchanged
(blueprint: lem-trf-quotient-map-fppf-local-models).

Proof:
1. An fppf covering is fpqc (lem-trf-fppf-covering-is-fpqc). The representable
   descent theorem lem-weil-pbc-fpqc-representable-descent glues the underlying
   maps to `U` uniquely. They remain over `S` by uniqueness of descent for maps
   to `S`. Naturality and separation of `F` give the defining equality of the
   fibre. This also handles the empty covering.
2. Yoneda identifies `a` with its section at the identity of `T`. Apply
   lem-weil-pbc-site-sheafification-sections-local to that section and choose
   representatives in `U` of the resulting local quotient classes. This gives
   an fppf covering and the local lifts `aᵢ` with the displayed equalities.
3. Lem-trf-etale-relation-kernel-pair identifies pairs of maps with equal
   quotient images with unique relation witnesses. Over a local lift `aᵢ`,
   substitute the pair `(aᵢ g,b)`. The pullback universal property
   def-pc-fibre-product identifies these witnesses with maps into
   `Tᵢ ×[U] R`, using `s` for the pullback and `t` for the map to `U`.
   The inverse maps commute with restrictions by uniqueness, yielding the
   natural isomorphism and its sectionwise projection formula.
4. Each first projection is a base change of `s`. The two conclusions of
   lem-weil-pbc-separated-lqf-base-change give separatedness and local
   quasi-finiteness. -/
theorem quotient_map_fppf_local_models {S : Scheme.{u}} {R U : Over S}
    (s t : R ⟶ U) [Mono (prod.lift s t)]
    (hrel : ∀ W : Over S, Equivalence (fun b c : W ⟶ U ↦
      ∃ r : W ⟶ R, r ≫ s = b ∧ r ≫ t = c))
    [Etale s.left] [Etale t.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ H : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F.obj ⟶ H.obj ↦ η ≫ k))
    [IsSeparated s.left] (hs : Scheme.Hom.IsLocallyQuasiFinite s.left)
    (T : Over S) (a : yoneda.obj T ⟶ F.obj) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over T.left)
      (quotientMapFibre T F (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) a) ∧
    ∃ (I : Type (u + 1)) (Tᵢ : I → Over S) (f : ∀ i, Tᵢ i ⟶ T)
      (aᵢ : ∀ i, Tᵢ i ⟶ U),
      Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (f i).left) ∈
        Scheme.fppfPrecoverage T.left ∧
      (∀ i, yoneda.map (aᵢ i) ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) =
        yoneda.map (f i) ≫ a) ∧
      (∀ i, ∃ e : yoneda.obj (Over.mk (pullback.fst (aᵢ i).left s.left)) ≅
          (Over.map (f i).left).op ⋙
            quotientMapFibre T F (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) a,
        ∀ (W : Over (Tᵢ i).left)
          (x : W ⟶ Over.mk (pullback.fst (aᵢ i).left s.left)),
          (Subtype.val ((e.hom.app (op W)) x)).left =
            x.left ≫ pullback.snd (aᵢ i).left s.left ≫ t.left) ∧
      (∀ i, IsSeparated (pullback.fst (aᵢ i).left s.left) ∧
        Scheme.Hom.IsLocallyQuasiFinite (pullback.fst (aᵢ i).left s.left)) := by
  sorry

end AlgebraicGeometry.Scheme
