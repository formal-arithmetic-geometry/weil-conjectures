/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Final

/-! # Constructible derived mapping continuity on affine ind-etale limits

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14 and
proof of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

The comparison is the localization of the map out of the termwise filtered
colimit of compatible complex representatives. It is not a categorical colimit
assertion in the triangulated category. The representatives retain both the
transition maps and the legs of the evaluation-defined pullback comparison.
All constructions use the ordinary constant-coefficient small etale category.

## Main statements

* `constructible_mapping_continuity`: the canonical comparison is invertible.
* `comparison_cofinal`: the canonical cofinal comparison triangle.
* `comparison_naturality`: system maps, coefficient maps and base restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

/-- Global RHom of the two exact inverse images along a scheme over X.
This is the existing RΓ of the existing derived internal Hom.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def value (T : Over X) : DerivedCategory (ModuleCat.{u + 1} A) :=
  ((ExternalRHom.globalHom A T.left).obj
    (op ((ExternalRHom.pull A T.hom).obj K))).obj
      ((ExternalRHom.pull A T.hom).obj M)

/-- Pullback of derived morphisms, transported along the canonical composition
isomorphisms for inverse image. Its source is the evaluation transpose already
provided by ExternalRHom.restriction; no map or isomorphism is chosen.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def pullback {T S : Over X} (f : T ⟶ S) : value A K M S ⟶ value A K M T :=
  ExternalRHom.restriction A f.left
      ((ExternalRHom.pull A S.hom).obj K) ((ExternalRHom.pull A S.hom).obj M) ≫
    ((ExternalRHom.globalHom A T.left).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).hom.app K).op).app
          ((ExternalRHom.pull A f.left).obj ((ExternalRHom.pull A S.hom).obj M)) ≫
    ((ExternalRHom.globalHom A T.left).obj
      (op ((ExternalRHom.pull A T.hom).obj K))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
          f.w.symm).inv.app M)

/-- The two coefficient variances of the existing global Hom bifunctor.
Source: Bhatt--Scholze 6.3.16, naturality of RHom
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def coefficientMap {K' M' : DerivedCategoryModule A X}
    (α : K' ⟶ K) (β : M ⟶ M') (T : Over X) :
    value A K M T ⟶ value A K' M' T :=
  ((ExternalRHom.globalHom A T.left).map
      ((ExternalRHom.pull A T.hom).map α).op).app
        ((ExternalRHom.pull A T.hom).obj M) ≫
    ((ExternalRHom.globalHom A T.left).obj
      (op ((ExternalRHom.pull A T.hom).obj K'))).map
        ((ExternalRHom.pull A T.hom).map β)

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

/-- Compatible strict representatives for the global RHom diagram and its
pullback cocone. The two equations normalize every transition and every leg
against the canonical pullback of morphisms. This is computational input for an
exact filtered colimit, not an assumed continuity isomorphism.
Source: Bhatt--Scholze 6.3.16, p. 48; the node's proof, Steps 2--6
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
structure Model where
  diagram : Iᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} A) ℤ
  cocone : Cocone diagram
  stage : ∀ i : I, (DerivedCategory.Q.obj (diagram.obj (op i))) ≅ value A K M (D.obj i)
  apex : DerivedCategory.Q.obj cocone.pt ≅ value A K M c.pt
  transition : ∀ {i j : I} (f : i ⟶ j),
    DerivedCategory.Q.map (diagram.map f.op) ≫ (stage i).hom =
      (stage j).hom ≫ pullback A K M (D.map f)
  leg : ∀ i : I,
    DerivedCategory.Q.map (cocone.ι.app (op i)) ≫ apex.hom =
      (stage i).hom ≫ pullback A K M (c.π.app i)

/-- The canonical comparison, computed by the exact colimit of complexes and
then localized. The normalization in Model fixes its pullback legs.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def comparison (P : Model A K M D c) :
    DerivedCategory.Q.obj (colimit P.diagram) ⟶ value A K M c.pt :=
  DerivedCategory.Q.map (colimit.desc P.diagram P.cocone) ≫ P.apex.hom

/-- Auxiliary comparison-isomorphism statement for a fixed compatible model.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-model-comparison).

Proof:
1. Filtered colimits of A-module complexes are exact, so the cohomology of the
   colimit of `P.diagram` is the colimit of the cohomologies. By the `transition`
   and `leg` equations, the stage isomorphisms identify `H^q` of the comparison
   with the canonical map `colim_i H^q value(U_i) → H^q value(U)` induced by
   `pullback`, which does not depend on `P`. A map in `D(A)` is invertible iff
   it is so on every `H^q`, so it suffices to treat one model.
2. For the injective model built from `N_i = j_{i,*} j_i^* I`, with `I` a
   bounded-below injective representative of `M` (node proof, Step 2),
   relative direct-image continuity (Stacks 0GIU) makes `colim N_i → N_U` a
   derived isomorphism; fixed-site constructible bounded-below Hom continuity
   (6.3.14) then gives `colim RHom_X(K, N_i) ≅ RHom_X(K, N_U)`, and
   derived adjunction identifies these with the global RHom on `U_i` and `U` and
   the maps with `pullback`. -/
theorem constructible_mapping_model_comparison_isIso [Finite A] [IsAffine X]
    [IsNoetherian X] [IsCofiltered I]
    (hc : IsLimit ((Over.forget X).mapCone c))
    (haffine : ∀ i : I, IsAffine (D.obj i).left)
    (hetale : ∀ i : I, Etale (D.obj i).hom)
    (hfp : ∀ i : I, LocallyOfFinitePresentation (D.obj i).hom)
    (htransition : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hM : ∃ a : ℤ, M.IsGE a) (P : Model A K M D c) :
    IsIso (comparison A K M D c P) := by
  sorry

variable {J : Type (u + 1)} [SmallCategory J]
variable (E : J ⥤ Over X) (d : Cone E) (r : J ⥤ I)

/-- Restrict the actual strict diagram and its actual cocone. This makes the
cofinal-refinement comparison independent of any new representatives.
Source: Bhatt--Scholze 6.3.16 and Stacks 0032
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def Model.reindex (P : Model A K M D c) : Model A K M (r ⋙ D) (c.whisker r) where
  diagram := r.op ⋙ P.diagram
  cocone := P.cocone.whisker r.op
  stage j := P.stage (r.obj j)
  apex := P.apex
  transition f := P.transition (r.map f)
  leg j := P.leg (r.obj j)

/-- Cofinal refinement preserves the exact colimit and its specified comparison.
Source: Bhatt--Scholze 6.3.16 and Stacks 0032
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

Proof: finality makes colimit.pre an isomorphism by the universal property of
colimits of complexes. Localization preserves it. The identity of comparisons
is colimit.pre_desc followed by functoriality of Q and the unchanged apex map.
This is the cofinal case of Step 1 of the node's proof, with its actual legs. -/
theorem comparison_cofinal [r.op.Final] (P : Model A K M D c) :
    IsIso (DerivedCategory.Q.map (colimit.pre P.diagram r.op)) ∧
      DerivedCategory.Q.map (colimit.pre P.diagram r.op) ≫ comparison A K M D c P =
        comparison A K M (r ⋙ D) (c.whisker r) (Model.reindex A K M D c r P) := by
  constructor
  · infer_instance
  · dsimp [comparison, Model.reindex]
    rw [← Category.assoc, ← Functor.map_comp, colimit.pre_desc]

variable (K' M' : DerivedCategoryModule A X) (α : K' ⟶ K) (β : M ⟶ M')

/-- A compatible map of strict representatives, including reindexing. The
scheme maps form a map of inverse systems and its map on the limit cones.
The strict cocone square and both normalization equations say that the chain
maps represent those very pullbacks, including their coherence.
Taking r to be the identity covers system maps. Taking it cofinal covers
refinements. Taking E to be the base-changed system along an affine etale
X' → X covers base restriction, with the composition comparisons in pullback.
Source: Bhatt--Scholze 6.3.16 and the node's proof, Step 7
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
structure ModelMap (P : Model A K M D c) (Q : Model A K' M' E d)
    (η : E ⟶ r ⋙ D) (v : d.pt ⟶ c.pt) where
  cone_square : ∀ j : J, v ≫ c.π.app (r.obj j) = d.π.app j ≫ η.app j
  stages : r.op ⋙ P.diagram ⟶ Q.diagram
  apex : P.cocone.pt ⟶ Q.cocone.pt
  square : ∀ j : J,
    P.cocone.ι.app (op (r.obj j)) ≫ apex = stages.app (op j) ≫ Q.cocone.ι.app (op j)
  stage_normalization : ∀ j : J,
    DerivedCategory.Q.map (stages.app (op j)) ≫ (Q.stage j).hom =
      (P.stage (r.obj j)).hom ≫ pullback A K M (η.app j) ≫
        coefficientMap A K M α β (E.obj j)
  apex_normalization : DerivedCategory.Q.map apex ≫ Q.apex.hom =
    P.apex.hom ≫ pullback A K M v ≫ coefficientMap A K M α β d.pt

/-- Every geometric system-map square, with maps in both coefficient
arguments, has jointly compatible strict representatives. Thus the naturality
statement is available for every such square, not just for squares for which
a representative map has separately been assumed to exist.
Source: Bhatt--Scholze 6.3.16 and the simultaneous construction used for
strict model existence
(blueprint: lem-per-ind-etale-constructible-mapping-model-existence).

Proof: choose bounded-below injective models of M and M' and a representative
of β into the latter; choose simultaneous representatives for α as well.
Form the direct-image diagrams on X using the adjunction units and inverse
image composition identifications, as in Step 2. Include both limit apexes
and the given geometric square in this diagram. Resolve the whole diagram
simultaneously in the Grothendieck category of diagrams of module sheaves;
evaluation gives compatible injective models, retaining the strict squares.
Applying the Hom complexes and global sections gives P, Q and their chain
maps. Derived adjunction with its unit/counit normalization (Step 6) identifies
their transitions, legs and vertical arrows with the evaluation-defined
pullbacks and α, β. Composition coherence (Step 7) gives cone_square.
The tools are lem-weil-pbc-module-sheaves-enough-injectives,
prop-pur-kinjective-resolutions-exist, lem-trf-bounded-below-derived-adjunction,
lem-sfb-global-rhom-coefficient-model and lem-pe-constant-left-module-inverse-image. -/
theorem compatible_model_maps_exist [Finite A] [IsAffine X] [IsNoetherian X]
    [IsCofiltered I] [IsCofiltered J]
    (hc : IsLimit ((Over.forget X).mapCone c))
    (hd : IsLimit ((Over.forget X).mapCone d))
    (haffineD : ∀ i : I, IsAffine (D.obj i).left)
    (haffineE : ∀ j : J, IsAffine (E.obj j).left)
    (hetaleD : ∀ i : I, Etale (D.obj i).hom)
    (hetaleE : ∀ j : J, Etale (E.obj j).hom)
    (hfpD : ∀ i : I, LocallyOfFinitePresentation (D.obj i).hom)
    (hfpE : ∀ j : J, LocallyOfFinitePresentation (E.obj j).hom)
    (htransitionD : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (htransitionE : ∀ {i j : J} (f : i ⟶ j), IsAffineHom (E.map f).left)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hK' : DerivedCategory.isBoundedConstructible A X K')
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hTor' : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K')
    (hM : ∃ a : ℤ, M.IsGE a) (hM' : ∃ a : ℤ, M'.IsGE a)
    (η : E ⟶ r ⋙ D) (v : d.pt ⟶ c.pt)
    (hv : ∀ j : J, v ≫ c.π.app (r.obj j) = d.π.app j ≫ η.app j) :
    ∃ (P : Model A K M D c) (Q : Model A K' M' E d),
      Nonempty (ModelMap A K M D c E d r K' M' α β P Q η v) := by
  sorry

/-- Auxiliary existence statement for compatible strict representatives.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-model-existence).

Proof: apply `compatible_model_maps_exist` to the identity map of the inverse
system and its limit cone, with identity maps in both coefficient arguments.
The identity cone square is functoriality of the identity natural transformation.
The resulting simultaneous representatives include a model of the original system;
forget the second model and the compatible map. -/
theorem constructible_mapping_model_exists [Finite A] [IsAffine X] [IsNoetherian X]
    [IsCofiltered I]
    (hc : IsLimit ((Over.forget X).mapCone c))
    (haffine : ∀ i : I, IsAffine (D.obj i).left)
    (hetale : ∀ i : I, Etale (D.obj i).hom)
    (hfp : ∀ i : I, LocallyOfFinitePresentation (D.obj i).hom)
    (htransition : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hM : ∃ a : ℤ, M.IsGE a) :
    Nonempty (Model A K M D c) := by
  obtain ⟨P, _Q, _t⟩ := compatible_model_maps_exist A K M D c D c (𝟭 I) K M
    (𝟙 K) (𝟙 M) hc hc haffine haffine hetale hetale hfp hfp
    htransition htransition hK hK hTor hTor hM hM
    (𝟙 D) (𝟙 c.pt) (by intro i; simp)
  exact ⟨P⟩

/-- Constructible derived mapping continuity, including existence of compatible
strict representatives. All choices of such representatives give an isomorphism
for the specified pullback comparison.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

Proof: `constructible_mapping_model_exists` supplies the first conjunct and
`constructible_mapping_model_comparison_isIso` supplies the second, for each
compatible model. The existence lemma is the identity case of the simultaneous
construction `compatible_model_maps_exist`. The fixed-model comparison retains
the direct-image and bounded-below Hom continuity argument. Cofinal refinement
and naturality are the formal colimit calculations proved below. -/
theorem constructible_mapping_continuity [Finite A] [IsAffine X] [IsNoetherian X]
    [IsCofiltered I]
    (hc : IsLimit ((Over.forget X).mapCone c))
    (haffine : ∀ i : I, IsAffine (D.obj i).left)
    (hetale : ∀ i : I, Etale (D.obj i).hom)
    (hfp : ∀ i : I, LocallyOfFinitePresentation (D.obj i).hom)
    (htransition : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hM : ∃ a : ℤ, M.IsGE a) :
    Nonempty (Model A K M D c) ∧
      ∀ P : Model A K M D c, IsIso (comparison A K M D c P) := by
  refine ⟨constructible_mapping_model_exists A K M D c hc haffine hetale hfp htransition
      hK hTor hM, ?_⟩
  intro P
  exact constructible_mapping_model_comparison_isIso A K M D c hc haffine hetale hfp
    htransition hK hTor hM P

/-- The actual map from the restricted source colimit to the target colimit.
Together with colimit.pre this is the colimit-side arrow of a system map or
cofinal refinement. Its legs are the supplied normalized chain maps.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def mapColimit (P : Model A K M D c) (Q : Model A K' M' E d)
    (η : E ⟶ r ⋙ D) (v : d.pt ⟶ c.pt)
    (t : ModelMap A K M D c E d r K' M' α β P Q η v) :
    colimit (r.op ⋙ P.diagram) ⟶ colimit Q.diagram :=
  colimMap t.stages

/-- The canonical comparison square commutes for maps of systems and arbitrary
reindexings, and hence for cofinal refinements and affine etale restriction.
For a cofinal refinement, colimit.pre is the canonical cofinal isomorphism;
no choice of an abstract isomorphism replaces either comparison.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

Proof: the square of strict cocones in ModelMap implies equality after
precomposition with every coprojection from the restricted diagram. The
universal property of the colimit of complexes gives equality before
localization. Apply Q, compose with Q.apex.hom, and use apex_normalization.
The stage normalizations identify all these arrows with scheme pullback.
For base restriction use U_i ×_X X', U ×_X X', and their projections; inverse
image composition identifies their coefficients with the restrictions of K,M.
This argument applies without finiteness assumptions, so in particular to the
isomorphisms of constructible_mapping_continuity. -/
theorem comparison_naturality
    (P : Model A K M D c) (Q : Model A K' M' E d)
    (η : E ⟶ r ⋙ D) (v : d.pt ⟶ c.pt)
    (t : ModelMap A K M D c E d r K' M' α β P Q η v) :
    DerivedCategory.Q.map (colimit.pre P.diagram r.op) ≫ comparison A K M D c P ≫
        pullback A K M v ≫ coefficientMap A K M α β d.pt =
      DerivedCategory.Q.map (mapColimit A K M D c E d r K' M' α β P Q η v t) ≫
        comparison A K' M' E d Q := by
  have hpre :
      DerivedCategory.Q.map (colimit.pre P.diagram r.op) ≫
          DerivedCategory.Q.map (colimit.desc P.diagram P.cocone) =
        DerivedCategory.Q.map
          (colimit.desc (r.op ⋙ P.diagram) (P.cocone.whisker r.op)) := by
    rw [← Functor.map_comp, colimit.pre_desc]
  have hdesc :
      colimit.desc (r.op ⋙ P.diagram) (P.cocone.whisker r.op) ≫ t.apex =
        colimMap t.stages ≫ colimit.desc Q.diagram Q.cocone := by
    apply (colimit.isColimit _).hom_ext
    intro j
    change ((colimit.ι (r.op ⋙ P.diagram) j ≫
      colimit.desc (r.op ⋙ P.diagram) (P.cocone.whisker r.op)) ≫ t.apex) =
      ((colimit.ι (r.op ⋙ P.diagram) j ≫ colimMap t.stages) ≫
        colimit.desc Q.diagram Q.cocone)
    rw [colimit.ι_desc, ι_colimMap]
    simp only [Cocone.whisker_ι]
    rw [Category.assoc, colimit.ι_desc]
    exact t.square j.unop
  dsimp [comparison, mapColimit]
  calc
    DerivedCategory.Q.map (colimit.pre P.diagram r.op) ≫
        (DerivedCategory.Q.map (colimit.desc P.diagram P.cocone) ≫ P.apex.hom) ≫
          pullback A K M v ≫ coefficientMap A K M α β d.pt =
      DerivedCategory.Q.map
          (colimit.desc (r.op ⋙ P.diagram) (P.cocone.whisker r.op)) ≫
            P.apex.hom ≫ pullback A K M v ≫ coefficientMap A K M α β d.pt := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ P.apex.hom ≫ pullback A K M v ≫
          coefficientMap A K M α β d.pt) hpre
    _ = DerivedCategory.Q.map
          (colimit.desc (r.op ⋙ P.diagram) (P.cocone.whisker r.op)) ≫
            (DerivedCategory.Q.map t.apex ≫ Q.apex.hom) := by
      rw [t.apex_normalization]
    _ = DerivedCategory.Q.map
          (colimit.desc (r.op ⋙ P.diagram) (P.cocone.whisker r.op) ≫ t.apex) ≫
            Q.apex.hom := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = DerivedCategory.Q.map (colimMap t.stages ≫ colimit.desc Q.diagram Q.cocone) ≫
            Q.apex.hom := by rw [hdesc]
    _ = DerivedCategory.Q.map (colimMap t.stages) ≫
            DerivedCategory.Q.map (colimit.desc Q.diagram Q.cocone) ≫ Q.apex.hom := by
      rw [Functor.map_comp]
      simp only [Category.assoc]

end AlgebraicGeometry.Etale.IndEtaleMapping
