module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkMaps
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Localization.Adjunction
import Sheaf.CategoryTheory.AdditiveLocalizationDescent
public import Mathlib.Topology.Sheaves.Stalks

/-! # Open extension and restriction of left sheaf dg modules

Source: Stacks Project, sdga.tex, Tags 0FRA, 0FRV and 0FRW; modules.tex, Tag 01AK.
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false


universe u w t s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace Opposite

namespace CategoryTheory.SheafDg

variable {X : TopCat.{u}} (S : TopCat.Sheaf CommRingCat.{max u w} X)
  [EssentiallySmall.{max u w} (Opens X)]

/-- The ordinary sheafified extension presheaf, without a dg action.
Source: Stacks 0FRA and 01AK (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openModuleExtension (U : Opens X) :
    SheafOfModules.{max u w} ((rings S).over U) ⥤ SheafOfModules.{max u w} (rings S) :=
  SheafOfModules.extensionByZeroPresheaf.{max u w} (rings S) U ⋙
    PresheafOfModules.sheafification.{max u w} (𝟙 (rings S).obj)

/-- Extension is additive degreewise.
Source: Stacks 01AK (blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: the direct-sum presheaf map is additive on every summand; sheafification
is additive, so its composite is additive. -/
@[instance] theorem openModuleExtension_additive (U : Opens X) :
    (openModuleExtension.{u, w} S U).Additive := by
  sorry

/-- The ordinary extension preserves zero maps.
Source: Stacks 01AK (blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: zero maps act as zero on each summand, and sheafification preserves zero. -/
@[instance] theorem openModuleExtension_preservesZero (U : Opens X) :
    (openModuleExtension.{u, w} S U).PreservesZeroMorphisms := by
  sorry

/-- Extension of the actual underlying complex and its differentials.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openComplexExtension (U : Opens X) : Complex (S.over U) ⥤ Complex S :=
  by
    letI := openModuleExtension_preservesZero.{u, w} S U
    exact (openModuleExtension.{u, w} S U).mapHomologicalComplex (.up ℤ)

/-- A section of a slice sheaf included in its summand and then sheafified.
Source: Stacks 0FRA (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openExtensionGenerator (U : Opens X)
    (G : SheafOfModules.{max u w} ((rings S).over U))
    (V : Opens X) (φ : V ⟶ U) (m : G.val.obj (op (Over.mk φ))) :
    ((openModuleExtension.{u, w} S U).obj G).val.obj (op V) :=
  (toSheafify (Opens.grothendieckTopology X)
    ((SheafOfModules.extensionByZeroPresheaf (rings S) U).obj G).presheaf).app (op V)
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (op (Over.mk ψ))) φ m)

variable {S}

/-- The extended action is the original action on every generating section.
There is no condition on arbitrary chosen extension maps.
Source: Stacks 0FRA and 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def IsOpenExtensionAction (A : Algebra S) (U : Opens X)
    (P : LeftModule (restrictAlgebra A U))
    (a : ModObj A.X ((openComplexExtension.{u, w} S U).obj P.X)) : Prop :=
  ∀ (p q : ℤ) (V : Opens X) (φ : V ⟶ U)
      (b : (A.X.X p).val.obj (op V))
      (m : (P.X.X q).val.obj (op (Over.mk φ))),
    actionSection A (moduleOn A _ a) p q (op V) b
        (openExtensionGenerator.{u, w} S U (P.X.X q) V φ m) =
      openExtensionGenerator.{u, w} S U (P.X.X (p + q)) V φ
        (actionSection (restrictAlgebra A U) P p q (op (Over.mk φ)) b m)

/-- The section formula determines the dg action uniquely on the actual extension.
Source: Stacks 0FRA and 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: apply the old action to each direct-sum generator. It is compatible with
restrictions and therefore sheafifies. The Leibniz identity, unit and associativity
hold on generators and hence after sheafification. Generators and sheaf separation
also prove uniqueness. -/
theorem existsUnique_openExtensionAction (A : Algebra S) (U : Opens X)
    (P : LeftModule (restrictAlgebra A U)) :
    ∃! a : ModObj A.X ((openComplexExtension.{u, w} S U).obj P.X),
      IsOpenExtensionAction.{u, w} A U P a := by
  sorry

/-- Extension on objects with the uniquely specified dg action.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openExtend (A : Algebra S) (U : Opens X)
    (P : LeftModule (restrictAlgebra A U)) : LeftModule A :=
  moduleOn A _ (existsUnique_openExtensionAction.{u, w} A U P).choose

/-- The ordinary extended chain map preserves the specified action.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: evaluate the action equation on each generating section; it is the original
linearity equation for f, followed by the sheafification unit. -/
theorem openExtendMap_linear (A : Algebra S) (U : Opens X)
    {P P' : LeftModule (restrictAlgebra A U)} (f : P ⟶ P') :
    IsModHom A.X (@id ((openExtend.{u, w} A U P).X ⟶ (openExtend.{u, w} A U P').X)
      ((openComplexExtension.{u, w} S U).map f.hom)) := by
  sorry

/-- The prescribed action-preserving map of extended complexes.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openExtensionMap (A : Algebra S) (U : Opens X)
    {P P' : LeftModule (restrictAlgebra A U)} (f : P ⟶ P') :
    openExtend.{u, w} A U P ⟶ openExtend.{u, w} A U P' :=
  { hom := (openComplexExtension.{u, w} S U).map f.hom
    isModHom := openExtendMap_linear.{u, w} A U f }

/-- The degreewise object and arrow prescriptions determine a unique functor.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: the prescribed maps preserve identity and composition since the underlying
complex functor does. The forgetful functor is faithful. The same prescriptions
force equality of objects and arrows and hence uniqueness. -/
theorem existsUnique_openExtension (A : Algebra S) (U : Opens X) :
    ∃! F : LeftModule (restrictAlgebra A U) ⥤ LeftModule A,
      (∀ P : LeftModule (restrictAlgebra A U), F.obj P = openExtend.{u, w} A U P) ∧
      (∀ (P P' : LeftModule (restrictAlgebra A U)) (f : P ⟶ P'),
        HEq (F.map f) (openExtensionMap.{u, w} A U f)) := by
  sorry

/-- The degreewise extension functor, uniquely fixed on both objects and arrows.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openExtension (A : Algebra S) (U : Opens X) :
    LeftModule (restrictAlgebra A U) ⥤ LeftModule A :=
  (existsUnique_openExtension.{u, w} A U).choose

/-- The unit sends each section to its sheafified extension generator.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def IsOpenAdjunction (A : Algebra S) (U : Opens X)
    (adj : openExtension.{u, w} A U ⊣ restriction A U) : Prop :=
  ∀ (P : LeftModule (restrictAlgebra A U)) (q : ℤ) (V : Over U)
      (m : (P.X.X q).val.obj (op V)),
    HEq ((((adj.unit.app P).hom.f q).val.app (op V)) m)
      (openExtensionGenerator.{u, w} S U (P.X.X q) V.left V.hom m)

/-- The canonical ordinary dg adjunction, determined by its section formula.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: a map from an extension is uniquely determined on the displayed generators.
Its transpose restricts the map and composes with the generator inclusion. Conversely
extend a map on U on generators and sheafify. The action equations and chain-map
identities hold on generators. These inverse constructions are natural; the unit
formula determines the whole hom-equivalence and thus the adjunction. -/
theorem existsUnique_openAdjunction (A : Algebra S) (U : Opens X) :
    ∃! adj : openExtension.{u, w} A U ⊣ restriction A U, IsOpenAdjunction.{u, w} A U adj := by
  sorry

/-- The ordinary adjunction with the generator-normalized unit.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openAdjunction (A : Algebra S) (U : Opens X) :
    openExtension.{u, w} A U ⊣ restriction A U :=
  (existsUnique_openAdjunction.{u, w} A U).choose

/-- Extension descends uniquely through homotopy and word localization.
Source: Stacks 0FRV, 0FRW and Categories 04VG
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: degreewise exact extension preserves underlying cohomology isomorphisms.
An extended signed homotopy still has boundary f-g, so it descends through K.
The word-localization universal property then gives the exact factorization below
and its uniqueness, sending each formal inverse to the inverse of its image. -/
theorem existsUnique_derivedOpenExtension (A : Algebra S) (U : Opens X) :
    ∃! F : Derived (restrictAlgebra A U) ⥤ Derived A,
      moduleQ (restrictAlgebra A U) ⋙ F = openExtension.{u, w} A U ⋙ moduleQ A := by
  sorry

/-- The derived extension determined by the actual degreewise extension.
Source: Stacks 0FRV (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def derivedOpenExtension (A : Algebra S) (U : Opens X) :
    Derived (restrictAlgebra A U) ⥤ Derived A :=
  (existsUnique_derivedOpenExtension.{u, w} A U).choose

section GeneralAdditive

variable {B : Type t} [Category.{s} B] [EssentiallySmall.{w} B]
  {J : GrothendieckTopology B} {T : Sheaf J CommRingCat.{w}}

/-- The additive structure on the word localization is determined by the module maps.
Source: Stacks 0FT4, Derived Categories 05R6
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: the homotopy-system theorem supplies the additive triangulated localization.
A common roof computes sums. Every pair of roofs has a common denominator, so
additivity on module maps forces this sum and proves uniqueness. -/
theorem existsUnique_openDerivedPreadditive (A : Algebra T) :
    ∃! p : Preadditive (Derived A), @Functor.Additive _ _ _ _ _ p (moduleQ A) := by
  sorry

/-- The canonical additive structure, characterized on localized module maps.
Source: Stacks 0FT4 and 05R6 (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
instance openDerivedPreadditive (A : Algebra T) : Preadditive (Derived A) :=
  (existsUnique_openDerivedPreadditive A).choose

end GeneralAdditive

/-- The derived adjunction is the localization of the generator-normalized one.
The two HEq clauses only transport the exact functor factorizations at their endpoints.
Source: Stacks 0FRW, Categories 04VG, and localization of adjunctions
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: transpose signed homotopies using the ordinary unit and counit; this gives
an adjunction on K. Both functors preserve quasi-isomorphisms, so apply localization
of adjunctions. Its unit and counit are exactly the images of the ordinary ones.
Every object is a localized module; these components determine the adjunction uniquely. -/
theorem existsUnique_derivedOpenAdjunction (A : Algebra S) (U : Opens X) :
    ∃! adj : derivedOpenExtension.{u, w} A U ⊣ derivedRestriction A U,
      (∀ P : LeftModule (restrictAlgebra A U),
        HEq (adj.unit.app ((moduleQ (restrictAlgebra A U)).obj P))
          ((moduleQ (restrictAlgebra A U)).map ((openAdjunction.{u, w} A U).unit.app P))) ∧
      (∀ M : LeftModule A, HEq (adj.counit.app ((moduleQ A).obj M))
        ((moduleQ A).map ((openAdjunction.{u, w} A U).counit.app M))) := by
  sorry

/-- The localized adjunction, with the specified unit and counit.
Source: Stacks 0FRW and Categories 04VG
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def derivedOpenAdjunction (A : Algebra S) (U : Opens X) :
    derivedOpenExtension.{u, w} A U ⊣ derivedRestriction A U :=
  (existsUnique_derivedOpenAdjunction.{u, w} A U).choose

/-- Extension and restriction preserve signed homotopies and quasi-isomorphisms.
The stalk assertion is in every degree, including on boundary points outside U.
Source: Stacks 0FRW, Modules 01AK and Sheaves 00A7
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: (1) degreewise additivity applies to d h+h d, with the same Koszul linearity
on generators. (2) Exactness of extension and restriction identifies their cohomology
with the corresponding functor applied to cohomology, hence preserves isomorphisms.
(3) The extension presheaf has zero stalk off U, and sheafification preserves stalks.
(4) Inside U the generator inclusion is the identity after restriction; hence the unit
is an isomorphism. The triangle identity makes the restricted counit its inverse.
These are dg maps, so the same facts hold after localization. -/
theorem open_extension_calculus (A : Algebra S) (U : Opens X) :
    (openExtension.{u, w} A U).Additive ∧ (restriction A U).Additive ∧
    (∀ (P P' : LeftModule (restrictAlgebra A U)) (f g : P ⟶ P'),
      homotopyRel (restrictAlgebra A U) f g →
        homotopyRel A ((openExtension.{u, w} A U).map f) ((openExtension.{u, w} A U).map g)) ∧
    (∀ (M M' : LeftModule A) (f g : M ⟶ M'), homotopyRel A f g →
      homotopyRel (restrictAlgebra A U) ((restriction A U).map f)
        ((restriction A U).map g)) ∧
    (∀ (P P' : LeftModule (restrictAlgebra A U)) (f : P ⟶ P'),
      QuasiIso f.hom →
        QuasiIso ((openExtension.{u, w} A U).map f).hom) ∧
    (∀ (M M' : LeftModule A) (f : M ⟶ M'), QuasiIso f.hom →
      QuasiIso ((restriction A U).map f).hom) ∧
    (∀ (P : LeftModule (restrictAlgebra A U)) (n : ℤ) (x : X), x ∉ U →
      Subsingleton (↥(colimit ((OpenNhds.inclusion x).op ⋙
        ((openExtend.{u, w} A U P).X.X n).val.presheaf) : AddCommGrpCat.{max u w}))) ∧
    IsIso (openAdjunction.{u, w} A U).unit ∧
    (∀ M : LeftModule A,
      (openAdjunction.{u, w} A U).unit.app ((restriction A U).obj M) ≫
        (restriction A U).map ((openAdjunction.{u, w} A U).counit.app M) = 𝟙 _) ∧
    IsIso (derivedOpenAdjunction.{u, w} A U).unit ∧
    (∀ M : Derived A,
      (derivedOpenAdjunction.{u, w} A U).unit.app ((derivedRestriction A U).obj M) ≫
        (derivedRestriction A U).map ((derivedOpenAdjunction.{u, w} A U).counit.app M) = 𝟙 _) := by
  sorry

/-- Both localized functors are additive and preserve the specified signed shifts
and exactly the distinguished cone triangles and their isomorphic images.
Source: Stacks 0FRV, 0FRW, 0FS5 and Derived Categories 05R6
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: extension and restriction are additive on K; additive-localization descent
makes their factorizations additive. Their degreewise shift comparisons are the
identity in each reindexed degree. Thus they respect (-1)^k d and (-1)^(k p) actions.
These comparisons satisfy zero and addition coherence before and after localization.
Finite sums identify the image of a cone with the cone of the image map; inclusion
and the negative projection are unchanged. This proves preservation of the specified
cone triangles. A functor preserves isomorphisms, giving all their isomorphic images. -/
theorem openExtension_preserves_signed_triangles (A : Algebra S) (U : Opens X) :
    (derivedOpenExtension.{u, w} A U).Additive ∧ (derivedRestriction A U).Additive ∧
    ∃ cJ : (derivedOpenExtension.{u, w} A U).CommShift ℤ,
    ∃ cR : (derivedRestriction A U).CommShift ℤ,
      (∀ t : Triangle (Derived (restrictAlgebra A U)),
        IsConeTriangle (restrictAlgebra A U) t →
          IsConeTriangle A
            ((@Functor.mapTriangle _ _ _ _ _ _ (derivedOpenExtension.{u, w} A U) cJ).obj t)) ∧
      (∀ t : Triangle (Derived A), IsConeTriangle A t →
        IsConeTriangle (restrictAlgebra A U)
          ((@Functor.mapTriangle _ _ _ _ _ _ (derivedRestriction A U) cR).obj t)) := by
  sorry

/-- A relative extension between opens is computed by ambient extension then restriction.
For U contained in V it is the extension U → V; no iterated slice choices are made.
Source: Stacks 0FRW and Sheaves 00A7
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
abbrev relativeOpenExtension (A : Algebra S) (U V : Opens X) :=
  openExtension.{u, w} A U ⋙ restriction A V

/-- The corresponding relative extension on the actual word localizations.
Source: Stacks 0FRV (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
abbrev derivedRelativeOpenExtension (A : Algebra S) (U V : Opens X) :=
  derivedOpenExtension.{u, w} A U ⋙ derivedRestriction A V

/-- The inverse open-square comparison is restriction of the intersection counit.
Its source is restriction U → T, extension T → V, where T = U ∩ V.
Source: Stacks 0FRW, Sheaves 00A7
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openBaseChangeInv (A : Algebra S) (U V : Opens X) :=
  Functor.whiskerLeft (openExtension.{u, w} A U)
    (Functor.whiskerRight (openAdjunction.{u, w} A (U ⊓ V)).counit (restriction A V))

/-- The same counit mate on the localized categories.
Source: Stacks 0FRW and Categories 04VG
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def derivedOpenBaseChangeInv (A : Algebra S) (U V : Opens X) :=
  Functor.whiskerLeft (derivedOpenExtension.{u, w} A U)
    (Functor.whiskerRight (derivedOpenAdjunction.{u, w} A (U ⊓ V)).counit
      (derivedRestriction A V))

/-- The normalized square comparisons are isomorphisms, before and after localization.
Source: Stacks 0FRW, Sheaves 00A7 and 007T
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: at a point of U ∩ V the counit is the identity under the generator-unit
identifications; elsewhere in V both stalks are zero. The stalk criterion makes
this map a degreewise isomorphism. Its inverse respects action and differential.
Localize this dg natural isomorphism; the unit/counit normalization identifies its
image with the displayed derived mate. -/
@[instance] theorem openBaseChangeInv_isIso (A : Algebra S) (U V : Opens X) :
    IsIso (openBaseChangeInv.{u, w} A U V) := by
  sorry

/-- Invertibility of the localized, normalized square mate.
Source: Stacks 0FRW and Categories 04VG
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: localize the preceding degreewise natural isomorphism. The defining
factorizations and the localized counit formula identify it with this mate. -/
@[instance] theorem derivedOpenBaseChangeInv_isIso (A : Algebra S) (U V : Opens X) :
    IsIso (derivedOpenBaseChangeInv.{u, w} A U V) := by
  sorry

/-- The canonical square isomorphism k* j! ≅ j'! k'*, in the ambient-slice encoding.
Its inverse is the counit-normalized degreewise map, so it is compatible with the
adjunctions rather than being an arbitrary isomorphism of the two functors.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def derivedOpenBaseChange (A : Algebra S) (U V : Opens X) :=
  (asIso (derivedOpenBaseChangeInv.{u, w} A U V)).symm

/-- The inverse composition comparison is the middle-open counit.
Source: Stacks 0FRW and Sheaves 00A7
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def openCompositionInv (A : Algebra S) (W U : Opens X) :=
  Functor.whiskerLeft (openExtension.{u, w} A W) (openAdjunction.{u, w} A U).counit

/-- The localized composition comparison uses the same specified counit.
Source: Stacks 0FRW and Categories 04VG
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def derivedOpenCompositionInv (A : Algebra S) (W U : Opens X) :=
  Functor.whiskerLeft (derivedOpenExtension.{u, w} A W) (derivedOpenAdjunction.{u, w} A U).counit

/-- Nested-open composition is a degreewise isomorphism with its canonical normalization.
Source: Stacks 0FRW, Sheaves 00A7 and 007T
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: since W is contained in U, the counit on j_W! P is the identity at stalks in W
and the map between zero stalks elsewhere. Apply the stalk criterion in each degree.
The inverse commutes with the action and differential by the inverse-map equations. -/
theorem openCompositionInv_isIso (A : Algebra S) (W U : Opens X)
    (h : W ≤ U) : IsIso (openCompositionInv.{u, w} A W U) := by
  sorry

/-- The normalized nested-open comparison remains invertible on D.
Source: Stacks 0FRW and Categories 04VG
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: localize the actual dg natural isomorphism of the preceding theorem.
The derived counit formula identifies its components with this comparison. -/
theorem derivedOpenCompositionInv_isIso (A : Algebra S) (W U : Opens X)
    (h : W ≤ U) : IsIso (derivedOpenCompositionInv.{u, w} A W U) := by
  sorry

/-- The canonical composition isomorphism (ji)! ≅ j! i!.
Source: Stacks 0FRW (blueprint: lem-sfb-sheaf-dg-open-extension-calculus). -/
def derivedOpenComposition (A : Algebra S) (W U : Opens X) (h : W ≤ U) :
    derivedOpenExtension.{u, w} A W ≅
      derivedRelativeOpenExtension.{u, w} A W U ⋙ derivedOpenExtension.{u, w} A U :=
  by
    letI := derivedOpenCompositionInv_isIso.{u, w} A W U h
    exact (asIso (derivedOpenCompositionInv.{u, w} A W U)).symm

/-- Any iterated open identifications with the same degreewise sheaf maps agree.
This includes the unit and counit comparisons and all further restrictions and
compositions of the displayed open-square and nested-open identifications.
Source: Stacks 00A7, 0FRW and Categories 04VG
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: a dg morphism is determined by its underlying chain map, and a chain map
by its components in every integer degree. Apply these two extensionality
principles to every component of the natural transformations. -/
theorem openComparison_coherence (A : Algebra S) (U V : Opens X)
    (F G : LeftModule (restrictAlgebra A U) ⥤ LeftModule (restrictAlgebra A V))
    (α β : F ⟶ G)
    (h : ∀ (P : LeftModule (restrictAlgebra A U)) (n : ℤ),
      (α.app P).hom.f n = (β.app P).hom.f n) : α = β := by
  sorry

/-- The same degreewise coherence holds for all induced localized comparisons.
The two transport hypotheses say that the comparisons are induced by the
specified ordinary dg maps, including iterated restriction and composition maps.
Source: Stacks 0FRW and Categories 04VG
(blueprint: lem-sfb-sheaf-dg-open-extension-calculus).
Proof: the preceding degreewise extensionality makes the ordinary transformations
equal. Apply localization to that equality. Every object of the chosen word
localization is the image of an ordinary module, so equality of these components
implies equality of localized transformations. Naturality against formal inverses
follows from naturality against the arrows being inverted. -/
theorem derivedOpenComparison_coherence (A : Algebra S) (U V : Opens X)
    (F G : LeftModule (restrictAlgebra A U) ⥤ LeftModule (restrictAlgebra A V))
    (F' G' : Derived (restrictAlgebra A U) ⥤ Derived (restrictAlgebra A V))
    (α β : F ⟶ G) (α' β' : F' ⟶ G')
    (h : ∀ (P : LeftModule (restrictAlgebra A U)) (n : ℤ),
      (α.app P).hom.f n = (β.app P).hom.f n)
    (hα : ∀ P : LeftModule (restrictAlgebra A U),
      HEq (α'.app ((moduleQ (restrictAlgebra A U)).obj P))
        ((moduleQ (restrictAlgebra A V)).map (α.app P)))
    (hβ : ∀ P : LeftModule (restrictAlgebra A U),
      HEq (β'.app ((moduleQ (restrictAlgebra A U)).obj P))
        ((moduleQ (restrictAlgebra A V)).map (β.app P))) : α' = β' := by
  sorry

end CategoryTheory.SheafDg
