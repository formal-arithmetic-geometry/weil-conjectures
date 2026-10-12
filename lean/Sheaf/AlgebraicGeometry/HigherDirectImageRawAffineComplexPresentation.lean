/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Complex presentation of raw restricted cohomology

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-higher-direct-image-raw-affine-complex-presentation).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Existence of input data for complex continuity, together with identifications of its cocone with
specified groups and maps. This proposition does not assert that the cohomology cocone is a
colimit, or that its legs represent every class. The coefficient cocone `L` is a colimit
of complexes; cohomology need not preserve it without the geometric continuity theorem. -/
inductive RawCohomologyComplexPresentation
    (J : Type v) [SmallCategory J] (A : Jᵒᵖ → AddCommGrpCat.{v + 1})
    (Z : AddCommGrpCat.{v + 1}) (b : ∀ i, A i → Z) (p : ℤ) : Prop where
  | mk
    (D : J ⥤ Scheme.{v})
    (c : Cone D)
    (hc : IsLimit c)
    (compact : ∀ i : J, CompactSpace (D.obj i))
    (quasiSeparated : ∀ i : J, QuasiSeparatedSpace (D.obj i))
    (affine : ∀ (i j : J) (f : i ⟶ j), IsAffineHom (D.map f))
    (F : ∀ i : J, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}) ℤ)
    (φ : ∀ {i j : J} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : J, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : J) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (a : ℤ)
    (hbelow : ∀ (i : J) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Jᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (eG : ∀ i : J, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : J) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (P : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ),
      (cohomology AddCommGrpCat.{v + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{v + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{v + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{v + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} X).map
          ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (H : Jᵒᵖ ⥤ AddCommGrpCat.{v + 1})
    (eH : ∀ i : J, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{v + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (hH : ∀ (i j : J) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{v + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G)
    (hL : IsColimit L)
    (B : Cocone H)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{v + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (hB : ∀ i : J, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{v + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))))
    (stageIso : ∀ i : Jᵒᵖ, A i ≅ H.obj i)
    (limitIso : Z ≅ B.pt)
    (compatibility : ∀ (i : Jᵒᵖ) (t : A i),
    B.ι.app i ((stageIso i).hom t) = limitIso.hom (b i t)) :
      RawCohomologyComplexPresentation J A Z b p

/-- The raw restricted-cohomology groups admit a presentation by the canonical
cohomology cocone of uniformly bounded-below complexes on a qcqs inverse system.
Source: Stacks Project, Tag 09Z1 (base change to an affine etale object and the
restricted-cohomology system), Tag 03Q8 (derived Hom computes restricted cohomology),
and Tag 0EZM (the canonical complex cohomology maps).
(blueprint: lem-sbc-higher-direct-image-raw-affine-complex-presentation).

Proof: Base change D and c along U.hom, taking the schemes U times_S X_i and
U times_S X and their pullback projections. The pullback universal property
makes the new cone limiting. Base change preserves affine transitions and
qcqs structure maps; since U is affine the stages are compact and quasi-separated.
Restrict F_i along the second projections and restrict H to the limit. Use
inverse-image composition to transport phi and its identity and composition
laws, and eH and hH. Put these sheaves in single complexes in degree zero, with
common lower bound zero. Inverse image preserves the coefficient colimit, and
single complexes preserve colimits; hence their coefficient cocone L is colimiting.
Take the cohomology diagram of these single complexes and the cocone whose legs
are canonical derived pullback followed by the shifted coefficient map. Construct
P by taking homology of the derived adjunction unit and the global-sections
composition comparison; this is the equation hP, and functoriality gives hH and hB.
For each stage and the limit, the free abelian sheaf sections adjunction identifies
raw derived Hom with restricted cohomology: restriction to an etale scheme has
an exact left adjoint and thus preserves injectives. The fully faithful bounded-below
inclusion identifies the Hom groups with unbounded cohomology of the single
complexes. These identifications are additive, giving stageIso and limitIso.
Naturality of derived adjunction, inverse-image composition, the single-functor
comparison and the shift comparison identifies each leg with exactly the raw
pullback followed by the specified coefficient map. This proves compatibility.
No cohomology continuity or existence of representatives is used here. -/
theorem exists_raw_affine_complex_presentation {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (U : S.Etale) [IsAffine U.left] :
    RawCohomologyComplexPresentation Iᵒᵖ
      (fun i ↦ (abelianHigherDirectImageRawPresheaf
        (D.obj (op i.unop.unop)).hom p (F i.unop.unop)).obj (op U))
      ((abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)).obj (op U))
      (fun i t ↦ abelianHigherDirectImageRawPullback (c.π.app (op i.unop.unop)).left
        (D.obj (op i.unop.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop.unop))) p
        (F i.unop.unop) (colimit H) ((eH i.unop.unop).inv ≫ colimit.ι H i.unop.unop) U t)
      (p : ℤ) := by sorry

end AlgebraicGeometry.Etale
