/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.SixFunctors.RingedDerivedCompositionComparison
import Sheaf.SixFunctors.RingedDerivedTwoIsoComparison

/-! # One flat model for the six scalar/site faces

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7E, 06YY, 0D6D and 07A4.
(blueprint: lem-sfb-etale-proetale-cube-flat-model).

All operations use the fixed-module presentation of modules over constant ring sheaves.
The six faces are the already specified canonical maps. The representative of a word
is defined by successive counits; in particular the two routes use identical endpoint maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.ScalarCubeFlatModel

/-- A word's ordinary and derived functors together with its actual representative map.
This is bookkeeping, with no existence or invertibility built into the data.
Source: Stacks 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
structure Word (C D : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] [Category.{u + 1} D] [Abelian D]
    [HasDerivedCategory.{u + 1} D] where
  ordinary : CochainComplex C ℤ ⥤ CochainComplex D ℤ
  derived : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D
  representative : ∀ P : CochainComplex C ℤ,
    derived.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj (ordinary.obj P)

/-- Append one letter: j_(hW) = Lh(j_W) followed by the representative counit of h.
Source: Stacks 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def Word.comp {C D E : Type (u + 2)}
    [Category.{u + 1} C] [Abelian C] [HasDerivedCategory.{u + 1} C]
    [Category.{u + 1} D] [Abelian D] [HasDerivedCategory.{u + 1} D]
    [Category.{u + 1} E] [Abelian E] [HasDerivedCategory.{u + 1} E]
    (F : Word C D) (G : Word D E) : Word C E where
  ordinary := F.ordinary ⋙ G.ordinary
  derived := F.derived ⋙ G.derived
  representative P := G.derived.map (F.representative P) ≫
    G.representative (F.ordinary.obj P)

/-- Flat-term K-flatness in the existing constant-coefficient monoidal presentation.
The quasi-isomorphism definition of K-flatness is equivalent to testing acyclic tensors;
flatness uses the sheafified tensor on both sides, equivalent by symmetry to either side.
Source: Stacks 06YN, 03ER (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def Good {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A]
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
    ∀ n : ℤ, ObjectProperty.flat (P.X n)

/-- The etale geometric letter uses the published geometric representative counit.
Source: Stacks 06YY (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def etale (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Word (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) where
  ordinary := (Etale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)
  derived := L(Etale.upperStar (ModuleCat.{u + 1} A) f)
  representative := Etale.scalarGeometricRepresentative A f

/-- The pro-etale geometric letter, with its left-derived counit on cochains.
Source: Stacks 06YY (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def proetale (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Word (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) where
  ordinary := (upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)
  derived := L(upperStar (ModuleCat.{u + 1} A) f)
  representative P := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Qh.map
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P)

/-- The exact comparison inverse image and its localization comparison counit.
Source: Stacks 099R, 06YY (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def comparison (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    Word (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) where
  ordinary := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapHomologicalComplex (.up ℤ)
  derived := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  representative := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryFactors.hom.app

/-- The etale scalar letter, with the published scalar representative counit.
Source: Stacks 06YY (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def etaleScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (Z : Scheme.{u}) :
    Word (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)) where
  ordinary := (etaleSheafExtendScalars a Z).mapHomologicalComplex (.up ℤ)
  derived := Etale.scalarExtension a Z
  representative := Etale.scalarExtensionRepresentative a Z

/-- The pro-etale scalar letter. Its counit is the transpose of the localized ordinary
scalar unit, under the fixed derived extension/restriction adjunction. Thus it also
covers nonflat coefficient maps and is the identity-geometric ringed pullback counit.
Source: Stacks 06YY (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def proetaleScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (Z : Scheme.{u}) :
    Word (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} B)) :=
  letI := (sheafExtendScalarsAdjunction a Z).left_adjoint_additive
  { ordinary := (sheafExtendScalars a Z).mapHomologicalComplex (.up ℤ)
    derived := pbcFixedScalarExtension (Scheme.ProEt.topology Z) a
    representative := fun P ↦
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) a)).homEquiv _ _).symm
        (_root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
            (NatTrans.mapHomologicalComplex (sheafExtendScalarsAdjunction a Z).unit
              (.up ℤ)).app P ≫
            (Functor.mapHomologicalComplexCompIso
              (Iso.refl (sheafExtendScalars a Z ⋙
                Sheaf.restrictScalars (Scheme.ProEt.topology Z) a)) (.up ℤ)).inv.app P) ≫
          (Sheaf.restrictScalars (Scheme.ProEt.topology Z) a).mapDerivedCategoryFactors.inv.app
            (((sheafExtendScalars a Z).mapHomologicalComplex (.up ℤ)).obj P)) }

/-- The six common vertices, numbered as in the source proof.
Source: Stacks 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
inductive Vertex
  | v0 | v1 | v2 | v3 | v4 | v5

/-- The six directed faces in the order of the node's assertion.
Source: Stacks 07A4, 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
inductive Face
  | proScalar | squareA | comparisonX | comparisonY | squareB | etaleScalar

/-- Sources of the faces in the two three-face routes.
Source: Stacks 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def Face.source : Face → Vertex
  | .proScalar => .v0
  | .squareA => .v1
  | .comparisonX => .v2
  | .comparisonY => .v0
  | .squareB => .v4
  | .etaleScalar => .v5

/-- Targets of the faces in the two three-face routes.
Source: Stacks 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def Face.target : Face → Vertex
  | .proScalar => .v1
  | .squareA => .v2
  | .comparisonX => .v3
  | .comparisonY => .v4
  | .squareB => .v5
  | .etaleScalar => .v3

/-- The six words, with recursively defined representative counits.
Source: Stacks 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def vertex {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Vertex → Word (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
  | .v0 => ((comparison A Y).comp (proetaleScalar a Y)).comp (proetale B f)
  | .v1 => ((comparison A Y).comp (proetale A f)).comp (proetaleScalar a X)
  | .v2 => ((etale A f).comp (comparison A X)).comp (proetaleScalar a X)
  | .v3 => ((etale A f).comp (etaleScalar a X)).comp (comparison B X)
  | .v4 => ((etaleScalar a Y).comp (comparison B Y)).comp (proetale B f)
  | .v5 => ((etaleScalar a Y).comp (etale B f)).comp (comparison B X)

/-- Apply an ordinary two-letter comparison termwise, with the canonical composition
identifications. This helper only transports an existing natural isomorphism.
Source: Stacks 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def twoComplexIso {C D E F : Type (u + 2)}
    [Category.{u + 1} C] [Preadditive C] [Category.{u + 1} D] [Preadditive D]
    [Category.{u + 1} E] [Preadditive E] [Category.{u + 1} F] [Preadditive F]
    {G : C ⥤ D} {H : D ⥤ E} {I : C ⥤ F} {J : F ⥤ E}
    [G.Additive] [H.Additive] [I.Additive] [J.Additive] (e : G ⋙ H ≅ I ⋙ J) :
    G.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) ≅
      I.mapHomologicalComplex (.up ℤ) ⋙ J.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (I ⋙ J)) (.up ℤ)).symm

/-- The six ordinary faces. Scalar faces are the adjunction conjugates of the
sectionwise restriction/direct-image identities, normalized on generalized pure tensors.
Source: Stacks 03EL, 07A4 (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def ordinaryFace {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) (e : Face)
    (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (vertex a f e.source).ordinary.obj P ⟶ (vertex a f e.target).ordinary.obj P :=
  letI := (sheafExtendScalarsAdjunction a X).left_adjoint_additive
  letI := (sheafExtendScalarsAdjunction a Y).left_adjoint_additive
  match e with
  | .proScalar => (twoComplexIso (sheafExtendScalarsCompUpperStarIso a f)).hom.app
      ((comparison A Y).ordinary.obj P)
  | .squareA => (proetaleScalar a X).ordinary.map
      ((twoComplexIso (comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} A) f)).hom.app P)
  | .comparisonX =>
      (twoComplexIso (etaleSheafExtendScalarsCompComparisonUpperStarIso a X)).inv.app
        ((etale A f).ordinary.obj P)
  | .comparisonY => (proetale B f).ordinary.map
      ((twoComplexIso (etaleSheafExtendScalarsCompComparisonUpperStarIso a Y)).inv.app P)
  | .squareB => (twoComplexIso (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} B) f)).hom.app ((etaleScalar a Y).ordinary.obj P)
  | .etaleScalar => (comparison B X).ordinary.map
      ((Etale.scalarSheafPullbackComplexIso a f).hom.app P)

/-- The six specified derived faces; no new isomorphism between the words is chosen.
Source: Stacks 07A4, 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def derivedFace {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) (e : Face)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (vertex a f e.source).derived.obj M ⟶ (vertex a f e.target).derived.obj M :=
  match e with
  | .proScalar => (scalarPullbackProEtaleIso a f).hom.app
      ((comparison A Y).derived.obj M)
  | .squareA => (proetaleScalar a X).derived.map
      ((directImageComparisonAmbientPullbackIso A f).hom.app M)
  | .comparisonX => (pbcComparisonReduction X a).hom.app ((etale A f).derived.obj M)
  | .comparisonY => (proetale B f).derived.map ((pbcComparisonReduction Y a).hom.app M)
  | .squareB => (directImageComparisonAmbientPullbackIso B f).hom.app
      ((etaleScalar a Y).derived.obj M)
  | .etaleScalar => (comparison B X).derived.map ((Etale.scalarPullbackIso a f).hom.app M)

/-- Naturality of the recursively specified representative, at a particular chain map.
Source: Stacks 06YY, 0D6D (blueprint: lem-sfb-etale-proetale-cube-flat-model). -/
def Word.NaturalAt {C D : Type (u + 2)}
    [Category.{u + 1} C] [Abelian C] [HasDerivedCategory.{u + 1} C]
    [Category.{u + 1} D] [Abelian D] [HasDerivedCategory.{u + 1} D]
    (W : Word C D) {P P' : CochainComplex C ℤ} (v : P ⟶ P') : Prop :=
  W.derived.map (_root_.DerivedCategory.Q.map v) ≫ W.representative P' =
    W.representative P ≫ _root_.DerivedCategory.Q.map (W.ordinary.map v)

/-- One flat-term K-flat representative simultaneously normalizes the six specified faces.
Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7E, 06YY, 0D6D and 07A4.
(blueprint: lem-sfb-etale-proetale-cube-flat-model).

Proof: (1) Use the site K-flat resolution theorem (lem-pc-kflat-resolution) on Y_et.
(2) Regard scalar extension as pullback along the identity geometric morphism with
structural ring map a. Ringed pullback preserves K-flat complexes with flat terms
(lem-weil-pbc-ringed-topoi-derived-tensor-pullback), so induction through every suffix
proves all the displayed Good assertions, including when a is nonflat.
(3) The representative counits of lem-weil-pbc-ringed-topoi-derived-pullback are
invertible on these suffixes. Scalar counits use lem-pur-derived-change-of-rings;
exact geometric counits use lem-weil-pbc-exact-functor-derived-functor. Word.comp is
precisely the recursion j_(hW) = Lh(j_W);epsilon_h. Hence all six j's are invertible.
(4) The ordinary site square localizes to d_R by sk-thm-pe-direct-image-comparison.
For R=B, use naturality along the scalar counit at P to obtain its actual input.
(5) Take normalized lifts from the System of lem-sfb-ringed-derived-monoidal-comparisons.
Apply lem-sfb-ringed-derived-composition-comparison to the two ringed composites,
and lem-sfb-ringed-derived-two-iso-comparison to their identity geometric path
isomorphism. Their structural maps agree on constants. Cancel the common single
pullback representative. The resulting pro-etale and comparison scalar faces are
the ordinary generalized-pure-tensor comparisons, in the stated orientations.
(6) The defining equation of def-pur-etale-scalar-pullback-iso is exactly the etale
face normalization. Its ordinary adjunction conjugate sends the pulled-back insertion
of 1 tensor m to 1 tensor the pulled-back m, by its mate-unit equation. B-linearity
and local generation by pure tensors identify it with the specified ordinary face.
(7) Applying an outer letter to a face equation and using counit naturality preserves
that equation. This supplies the three whiskered faces with the same vertex maps.
(8) Counit naturality and induction through Word.comp prove NaturalAt for every suffix
and full word. All constructions are unbounded and require no finiteness of f. -/
theorem simultaneous_flat_model
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      ∃ (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (p : P ⟶ K), Good Y.smallEtaleTopology A P ∧ QuasiIso p) ∧
    (∀ P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      Good Y.smallEtaleTopology A P →
      Good (Scheme.ProEt.topology Y) A ((comparison A Y).ordinary.obj P) ∧
      Good (X.smallEtaleTopology) A ((etale A f).ordinary.obj P) ∧
      Good (Y.smallEtaleTopology) B ((etaleScalar a Y).ordinary.obj P) ∧
      Good (Scheme.ProEt.topology Y) B
        (((comparison A Y).comp (proetaleScalar a Y)).ordinary.obj P) ∧
      Good (Scheme.ProEt.topology X) A (((comparison A Y).comp (proetale A f)).ordinary.obj P) ∧
      Good (Scheme.ProEt.topology X) A (((etale A f).comp (comparison A X)).ordinary.obj P) ∧
      Good (X.smallEtaleTopology) B (((etale A f).comp (etaleScalar a X)).ordinary.obj P) ∧
      Good (Scheme.ProEt.topology Y) B (((etaleScalar a Y).comp (comparison B Y)).ordinary.obj P) ∧
      Good (X.smallEtaleTopology) B (((etaleScalar a Y).comp (etale B f)).ordinary.obj P) ∧
      (∀ i : Vertex, Good (Scheme.ProEt.topology X) B
        ((vertex a f i).ordinary.obj P)) ∧
      IsIso ((comparison A Y).representative P) ∧
      IsIso ((etale A f).representative P) ∧
      IsIso ((etaleScalar a Y).representative P) ∧
      IsIso ((proetaleScalar a Y).representative ((comparison A Y).ordinary.obj P)) ∧
      IsIso ((proetale A f).representative ((comparison A Y).ordinary.obj P)) ∧
      IsIso ((comparison A X).representative ((etale A f).ordinary.obj P)) ∧
      IsIso ((etaleScalar a X).representative ((etale A f).ordinary.obj P)) ∧
      IsIso ((comparison B Y).representative ((etaleScalar a Y).ordinary.obj P)) ∧
      IsIso ((etale B f).representative ((etaleScalar a Y).ordinary.obj P)) ∧
      IsIso ((proetale B f).representative
        (((comparison A Y).comp (proetaleScalar a Y)).ordinary.obj P)) ∧
      IsIso ((proetaleScalar a X).representative
        (((comparison A Y).comp (proetale A f)).ordinary.obj P)) ∧
      IsIso ((proetaleScalar a X).representative
        (((etale A f).comp (comparison A X)).ordinary.obj P)) ∧
      IsIso ((comparison B X).representative
        (((etale A f).comp (etaleScalar a X)).ordinary.obj P)) ∧
      IsIso ((proetale B f).representative
        (((etaleScalar a Y).comp (comparison B Y)).ordinary.obj P)) ∧
      IsIso ((comparison B X).representative
        (((etaleScalar a Y).comp (etale B f)).ordinary.obj P)) ∧
      (∀ i : Vertex, IsIso ((vertex a f i).representative P)) ∧
      (∀ e : Face,
        derivedFace a f e (_root_.DerivedCategory.Q.obj P) ≫
            (vertex a f e.target).representative P =
          (vertex a f e.source).representative P ≫
            _root_.DerivedCategory.Q.map (ordinaryFace a f e P))) ∧
    (∀ (P P' : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (v : P ⟶ P'), Good Y.smallEtaleTopology A P → Good Y.smallEtaleTopology A P' →
      (comparison A Y).NaturalAt v ∧
      (etale A f).NaturalAt v ∧
      (etaleScalar a Y).NaturalAt v ∧
      ((comparison A Y).comp (proetaleScalar a Y)).NaturalAt v ∧
      ((comparison A Y).comp (proetale A f)).NaturalAt v ∧
      ((etale A f).comp (comparison A X)).NaturalAt v ∧
      ((etale A f).comp (etaleScalar a X)).NaturalAt v ∧
      ((etaleScalar a Y).comp (comparison B Y)).NaturalAt v ∧
      ((etaleScalar a Y).comp (etale B f)).NaturalAt v ∧
      ∀ i : Vertex, (vertex a f i).NaturalAt v) := by
  sorry

end AlgebraicGeometry.ProEtale.ScalarCubeFlatModel
