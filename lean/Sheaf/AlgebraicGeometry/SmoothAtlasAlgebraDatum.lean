module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Algebra descent data on every scheme test of an atlas relation

Source: Stacks Project, stacks-sheaves.tex, Tag 06WT and its explicit presheaf construction
(blueprint: def-sfb-smooth-atlas-algebra-datum).

The atlas algebra is expressed on its big fppf site, using the existing local-presentation
predicate. The scheme comparison of Tag 06WK identifies this with the ordinary algebra on U.
A relation point is an actual vertical isomorphism between the two atlas objects. Naturality
on all scheme tests expresses an isomorphism on the algebraic-space relation, including when
that space is not a scheme. The orientation is p1^* C to p2^* C.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.checkUnivs false

universe u v w m

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- A scheme test of the atlas, with its actual map to U.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
abbrev atlasAlgebraTest {S : Scheme.{u}} {U T : Over S} (f : T ⟶ U) :=
  (CostructuredArrow.mk (yoneda.map f) : (discreteModuli (yoneda.obj U)).obj)

/-- The special arrow along a scheme map in the presentation prestack.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
def atlasAlgebraTestMap {S : Scheme.{u}} {U T T' : Over S} (b : T' ⟶ T) (f : T ⟶ U) :
    atlasAlgebraTest (b ≫ f) ⟶ atlasAlgebraTest f :=
  CostructuredArrow.homMk b (by simp)

/-- The discrete fibred category attached to a presheaf is fibred in groupoids.
Source: Stacks 003T (blueprint: def-sfb-smooth-atlas-algebra-datum).
Proof: lift b:T'→T by precomposing the presheaf section with yoneda.map b.
A triangle over schemes has a unique lift because the comma arrow is determined
by its underlying scheme map. Thus every arrow is strongly cartesian. -/
theorem atlasAlgebraTest_isFibred {S : Scheme.{u}} (U : Over S) :
    IsFibredInGroupoids (discreteModuli (yoneda.obj U)) := by
  sorry

/-- The atlas structure sheaf in the same ambient universe as the stack's algebras.
Both lifts are canonical ULift transports; no equality of site universes is imposed.
Source: Stacks 06TV, 06WK (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
def atlasAlgebraStructure {S : Scheme.{u}} (U : Over S) :
    Sheaf (moduliFppfTopology (discreteModuli (yoneda.obj U)))
      CommRingCat.{max (u + 1) m} :=
  SheafOfModules.CochainUniverseTransport.ring.{u + 1, u, u + 1, max (u + 1) m, 0}
    (moduliStructureSheaf _ (atlasAlgebraTest_isFibred U))

/-- The underlying module of a lifted atlas algebra, with the structure-map scalar action.
Source: Stacks 06WG (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
def atlasAlgebraModule {S : Scheme.{u}} {U : Over S}
    (A : Under (atlasAlgebraStructure.{u, m} U)) :
    SheafOfModules.{max (u + 1) m}
      ((sheafCompose _ (forget₂ CommRingCat.{max (u + 1) m}
        RingCat.{max (u + 1) m})).obj (atlasAlgebraStructure.{u, m} U)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max (u + 1) m}
      RingCat.{max (u + 1) m})).map A.hom)).obj
    (SheafOfModules.unit ((sheafCompose _ (forget₂ CommRingCat.{max (u + 1) m}
      RingCat.{max (u + 1) m})).obj A.right))

/-- The existing slice sheafification supplies quasi-coherence in the ambient universe.
Source: Stacks 03DL (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
instance atlasAlgebraSliceSheafify {S : Scheme.{u}} (U : Over S)
    (x : (discreteModuli (yoneda.obj U)).obj) :
    HasWeakSheafify ((moduliFppfTopology (discreteModuli (yoneda.obj U))).over x)
      AddCommGrpCat.{max (u + 1) m} :=
  letI : EssentiallySmall.{max (u + 1) m} (Over x) :=
    essentiallySmallSelf.{m, u, u + 1} _
  letI : HasSheafify ((moduliFppfTopology (discreteModuli (yoneda.obj U))).over x)
      AddCommGrpCat.{max (u + 1) m} := SheafOfModules.hasSheafify_coefficientUniverse
  HasSheafify.isRightAdjoint

/-- The ambient slice sheafification has the usual local-bijection criterion.
Source: Stacks 00WK (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
instance atlasAlgebraSliceW {S : Scheme.{u}} (U : Over S)
    (x : (discreteModuli (yoneda.obj U)).obj) :
    ((moduliFppfTopology (discreteModuli (yoneda.obj U))).over x).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Atlas algebras with the general-site local-presentation predicate, and all algebra maps.
Source: Stacks 06WK, 06WG (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
abbrev AtlasQuasicoherentAlgebra {S : Scheme.{u}} (U : Over S) :=
  ObjectProperty.FullSubcategory
    (fun A : Under (atlasAlgebraStructure.{u, m} U) ↦
      SheafOfModules.IsQuasicoherent (atlasAlgebraModule.{u, m} A))

/-- A vertical relation point between two maps from the same scheme to the atlas.
This retains the actual isomorphism and its condition over the identity of T.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
abbrev AtlasAlgebraRelation {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    {T : Over S} (f g : T ⟶ U) :=
  {i : a.obj (atlasAlgebraTest f) ≅ a.obj (atlasAlgebraTest g) //
    F.p.IsHomLift (𝟙 T) i.hom}

/-- Algebra isomorphisms on relation tests, natural under base change, with identity
and triple-cocycle equations. Each isomorphism preserves multiplication, unit and scalars.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
structure SmoothAtlasAlgebraDatum {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) where
  /-- The quasi-coherent algebra on the atlas. -/
  algebra : AtlasQuasicoherentAlgebra.{u, max v w} U
  /-- Values of the algebra isomorphism p1^* C ≅ p2^* C on every scheme test. -/
  delta {T : Over S} (f g : T ⟶ U) (i : AtlasAlgebraRelation a f g) :
    algebra.obj.right.obj.obj (op (atlasAlgebraTest f)) ≅
      algebra.obj.right.obj.obj (op (atlasAlgebraTest g))
  /-- The transition is over the identity on the regular functions of T. -/
  delta_scalars {T : Over S} (f g : T ⟶ U) (i : AtlasAlgebraRelation a f g)
      (r : Scheme.Γ.obj (op T.left)) :
    (delta f g i).hom (algebra.obj.hom.hom.app (op (atlasAlgebraTest f)) (ULift.up (ULift.up r))) =
      algebra.obj.hom.hom.app (op (atlasAlgebraTest g)) (ULift.up (ULift.up r))
  /-- Naturality on all relation-test arrows is the sheaf-isomorphism condition on R. -/
  delta_naturality {T T' : Over S} (b : T' ⟶ T) (f g : T ⟶ U)
      (i : AtlasAlgebraRelation a f g) (j : AtlasAlgebraRelation a (b ≫ f) (b ≫ g))
      (h : a.map (atlasAlgebraTestMap b f) ≫ i.val.hom =
        j.val.hom ≫ a.map (atlasAlgebraTestMap b g)) :
    algebra.obj.right.obj.map (atlasAlgebraTestMap b f).op ≫
        (delta (b ≫ f) (b ≫ g) j).hom =
      (delta f g i).hom ≫ algebra.obj.right.obj.map (atlasAlgebraTestMap b g).op
  /-- Pullback along the relation diagonal is the identity. -/
  delta_id {T : Over S} (f : T ⟶ U) (h : F.p.IsHomLift (𝟙 T) (𝟙 (a.obj
      (atlasAlgebraTest f)))) :
    (delta f f ⟨Iso.refl _, h⟩).hom = 𝟙 _
  /-- Pullback to every triple relation point gives delta23 ∘ delta12 = delta13. -/
  delta_comp {T : Over S} (f g h : T ⟶ U)
      (i : AtlasAlgebraRelation a f g) (j : AtlasAlgebraRelation a g h)
      (k : AtlasAlgebraRelation a f h) (hk : k.val.hom = i.val.hom ≫ j.val.hom) :
    (delta f g i).hom ≫ (delta g h j).hom = (delta f h k).hom

namespace SmoothAtlasAlgebraDatum

/-- All algebra maps intertwining the relation transitions; no invertibility is required.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
structure Hom {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)} {U : Over S}
    {a : BasedFunctor (discreteModuli (yoneda.obj U)) F}
    (C D : SmoothAtlasAlgebraDatum a) where
  /-- The atlas algebra map. -/
  hom : C.algebra ⟶ D.algebra
  /-- Equivariance of the algebra map on every relation test. -/
  comm {T : Over S} (f g : T ⟶ U) (i : AtlasAlgebraRelation a f g) :
    hom.hom.right.hom.app (op (atlasAlgebraTest f)) ≫ (D.delta f g i).hom =
      (C.delta f g i).hom ≫ hom.hom.right.hom.app (op (atlasAlgebraTest g))

/-- Identity and composition are the underlying algebra maps.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-algebra-datum). -/
instance datumCategory {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)} {U : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) :
    Category (SmoothAtlasAlgebraDatum a) where
  Hom := Hom
  id C := ⟨𝟙 C.algebra, by intros; simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    intro T l r i
    change (_ ≫ _) ≫ _ = _ ≫ (_ ≫ _)
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc]⟩
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

end SmoothAtlasAlgebraDatum

end CategoryTheory
