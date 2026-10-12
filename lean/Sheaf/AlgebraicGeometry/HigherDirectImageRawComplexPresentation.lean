/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit

/-! # Presenting raw module cohomology by abelian etale complexes

Source: Stacks Project, Tags 09Z1, 0EZM and 03FD.
(blueprint: lem-sbc-higher-image-raw-complex-presentation).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- The precise hypotheses of complex continuity, as an existential proposition.
No object or map is chosen by this definition, and no continuity conclusion is a field.
Source: Stacks Project, Tag 0EZM, lemma-colimit-variant-complexes.
(blueprint: def-sbc-etale-complex-cohomology-presentation). -/
def EtaleComplexCohomologyPresentation
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H) : Prop :=
  ∃
    (D : I ⥤ Scheme.{u})
    (c : Cone D)
    (_hc : IsLimit c)
    (_compact : ∀ i : I, CompactSpace (D.obj i))
    (_quasiSeparated : ∀ i : I, QuasiSeparatedSpace (D.obj i))
    (_affine : ∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f))
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (_hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (_hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (a : ℤ)
    (_hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (_hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (p : ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (_hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (_hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G)
    (_hL : IsColimit L)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (_hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))), True

set_option backward.isDefEq.respectTransparency true in
/-- Complex continuity applied to a presentation. The witnesses are eliminated only
inside this proof; no library definition selects data from an existence statement. -/
theorem EtaleComplexCohomologyPresentation.isColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    {H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {B : Cocone H}
    (s : EtaleComplexCohomologyPresentation H B) : Nonempty (IsColimit B) := by
  rcases s with ⟨D, c, hc, compact, quasiSeparated, affine, F, φ,
    hidentity, hcomposition, a, hbelow, G,
    eG, hG, p, P, hP, eH, hH, L, hL, eB, hB, _⟩
  let := compact
  let := quasiSeparated
  let := affine
  exact nonempty_isColimit_etale_complex_cohomology D c hc
    F φ hidentity hcomposition a hbelow G eG hG
    p P hP H eH hH L hL B eB hB

/-- Raw module derived-Hom cohomology, including its fixed transition maps, has a
presentation by abelian etale complexes on the base-changed inverse system.
This theorem identifies the input to continuity; it does not assert cohomology
continuity or any eventual equality of classes.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit, the affine-object reduction),
Tag 0EZM (lemma-colimit-variant-complexes, the coefficient system), and Tag 03FD
(lemma-cohomology-modules-abelian, comparison after forgetting scalars).
(blueprint: lem-sbc-higher-image-raw-complex-presentation).

Proof: Use the diagram of schemes D(i) times_S U and the cone c.pt times_S U, obtained
by applying Over.map k, Over.pullback U.hom, and Over.forget U.left. Pullback preserves
this limiting cone. Its transition maps are affine by base change. Each stage is qcqs:
its map to affine U is qcqs by base change of D(i).hom followed by k, and composing with
the structure map of affine U gives compactness and quasi-separatedness of the stage.
Take F(i) to be the single complex in degree zero of the underlying abelian sheaf of
the pullback of G along D(i) times_S U -> W. Take phi from the inverse-image composition
isomorphism, so identity and composition hold by its unit and associativity coherence.
The lower bound is zero. On the limit, take the constant diagram G' with value the
single complex of the underlying abelian pullback of G. Inverse-image composition and
forgetting scalars supply eG and its map equation hG. The identity cocone of this constant
diagram is colimiting, since I opposite is nonempty and connected; this is L and hL.
Take p=q and P to be exactly the derived-adjunction map displayed in hP.
For eH and eB, free-module-sheaf adjunction identifies raw derived Hom out of the free
sheaf of U with derived sections on the corresponding fibre product. An injective
module resolution computes those sections after forgetting scalars, by the all-object
abelian acyclicity in 03FD. It gives additive isomorphisms to the abelian cohomology of
the degree-zero complexes. Derived adjunction is natural in the scheme morphism:
expanding its unit and the pullback-composition, single-complex and shift comparisons
gives the five factors of the fixed raw pullback. Hence hH and hB concern these exact
maps, not an unspecified comparison. These explicit data supply the existential presentation.
For negative q the same identification applies, with both degree-zero-complex
cohomology groups zero. No continuity theorem is used to construct the presentation. -/
theorem nonempty_higherDirectImageRaw_complex_presentation
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left] :
    EtaleComplexCohomologyPresentation
      (higherDirectImageRawDiagram Λ k G q D U)
      (higherDirectImageRawCocone Λ k G q D c U) := by
  sorry

end AlgebraicGeometry.Etale
