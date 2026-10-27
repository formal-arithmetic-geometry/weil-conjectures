module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.DerivedColimitBar
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek

/-!
# Lower-shriek counits for polynomial-presentation sites

Source: Stacks Project, Cotangent Complex, Tags 08QR and 08QW; Cohomology on Sites,
Tags 08PF and 08PH (blueprint: lem-trf-cotangent-lower-shriek).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Algebra.CotangentSites

/-- A polynomial structural map, allowing every small set of variables, including the empty
set. Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
def IsPolynomial {A P : CommRingCat.{u}} (f : A ⟶ P) : Prop :=
  ∃ (S : Type u) (e : CommRingCat.of (MvPolynomial S A) ≅ P),
    CommRingCat.ofHom MvPolynomial.C ≫ e.hom = f

/-- Polynomial augmented algebras, before taking opposites. Its morphisms are all algebra
maps respecting the augmentation, without chosen polynomial coordinates.
Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
abbrev Presentations {A T : CommRingCat.{u}} (f : A ⟶ T) :=
  ObjectProperty.FullSubcategory
    (fun X : Over (Under.mk f) ↦ IsPolynomial X.left.hom)

/-- The fixed diagram `A → B → C`, viewed as an arrow of `A`-algebras.
Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
def triangle {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) : Arrow (Under A) :=
  Arrow.mk (Under.homMk g (by simp) : Under.mk f ⟶ Under.mk (f ≫ g))

/-- Compatible polynomial pairs, before taking opposites. The over-arrow category imposes
both augmentation squares and the square between `P → Q` and `P' → Q'`.
Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
abbrev Pairs {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :=
  ObjectProperty.FullSubcategory (fun X : Over (triangle f g) ↦
    IsPolynomial X.left.left.hom ∧ IsPolynomial X.left.hom.right)

/-- A small presentation site; its topology is bottom, the identity-cover topology.
`AsSmall` changes only universe encodings. Source: Stacks 08QR and the size convention
(blueprint: lem-trf-cotangent-lower-shriek). -/
abbrev Site {A T : CommRingCat.{u}} (f : A ⟶ T) := AsSmall.{0} (Presentations f)ᵒᵖ

/-- The small site of pairs, with the identity-cover topology.
Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
abbrev PairSite {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :=
  AsSmall.{0} (Pairs f g)ᵒᵖ

/-- Forget only the opposite and small-category encodings of a presentation.
Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
def presentationDiagram {A T : CommRingCat.{u}} (f : A ⟶ T) :
    (Site f)ᵒᵖ ⥤ Over (Under.mk f) :=
  AsSmall.down.op ⋙ (opOpEquivalence _).functor ⋙ ObjectProperty.ι _

/-- Forget only the opposite and small-category encodings of a pair.
Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
def pairDiagram {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (PairSite f g)ᵒᵖ ⥤ Over (triangle f g) :=
  AsSmall.down.op ⋙ (opOpEquivalence _).functor ⋙ ObjectProperty.ι _

/-- The structural ring presheaf `P`. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def presentationRing {A T : CommRingCat.{u}} (f : A ⟶ T) :
    (Site f)ᵒᵖ ⥤ CommRingCat.{u} :=
  presentationDiagram f ⋙ Over.forget _ ⋙ Under.forget _

/-- The structural augmentation `P → T`. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def presentationAugmentation {A T : CommRingCat.{u}} (f : A ⟶ T) :
    presentationRing f ⟶ (Functor.const _).obj T where
  app U := ((presentationDiagram f).obj U).hom.right
  naturality _ _ h := by
    exact congrArg (fun k ↦ k.right) (Over.w ((presentationDiagram f).map h))

/-- The coefficient inclusion `A → P`. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def presentationBase {A T : CommRingCat.{u}} (f : A ⟶ T) :
    (Functor.const _).obj A ⟶ presentationRing f where
  app U := ((presentationDiagram f).obj U).left.hom
  naturality _ _ h := by
    exact (Under.w ((presentationDiagram f).map h).left).symm

/-- The first polynomial ring `P` on pairs. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def pairP {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (PairSite f g)ᵒᵖ ⥤ CommRingCat.{u} :=
  pairDiagram f g ⋙ Over.forget _ ⋙ Arrow.leftFunc ⋙ Under.forget _

/-- The second polynomial ring `Q` on pairs. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def pairQ {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (PairSite f g)ᵒᵖ ⥤ CommRingCat.{u} :=
  pairDiagram f g ⋙ Over.forget _ ⋙ Arrow.rightFunc ⋙ Under.forget _

/-- The structural map `P → Q`. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def pairPQ {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    pairP f g ⟶ pairQ f g where
  app U := ((pairDiagram f g).obj U).left.hom.right
  naturality _ _ h := by
    exact congrArg (fun k ↦ k.right) (Arrow.w ((pairDiagram f g).map h).left)

/-- The augmentation `P → B`. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def pairPB {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    pairP f g ⟶ (Functor.const _).obj B where
  app U := ((pairDiagram f g).obj U).hom.left.right
  naturality _ _ h := by
    exact congrArg (fun k ↦ k.left.right) (Over.w ((pairDiagram f g).map h))

/-- The augmentation `Q → C`. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def pairQC {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    pairQ f g ⟶ (Functor.const _).obj C where
  app U := ((pairDiagram f g).obj U).hom.right.right
  naturality _ _ h := by
    exact congrArg (fun k ↦ k.right.right) (Over.w ((pairDiagram f g).map h))

/-- Ring universe transport, with the same elements and operations after `ULift.down`.
Source: Stacks size convention (blueprint: lem-trf-cotangent-lower-shriek). -/
def liftRing : CommRingCat.{u} ⥤ RingCat.{u + 1} where
  obj T := RingCat.of (ULift.{u + 1} T)
  map h := RingCat.ofHom h.hom.ulift

/-- A presheaf is a sheaf on the identity-cover topology. Source: Stacks 08QR
(blueprint: lem-trf-cotangent-lower-shriek). -/
def ringSheaf {E : Type (u + 1)} [SmallCategory E] (O : Eᵒᵖ ⥤ RingCat.{u + 1}) :
    Sheaf (⊥ : GrothendieckTopology E) RingCat.{u + 1} :=
  (sheafBotEquivalence _).inverse.obj O

/-- The geometric inverse image is precomposition on underlying presheaves of sets.
Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
def setInverse {E D : Type (u + 1)} [SmallCategory E] [SmallCategory D] (v : E ⥤ D) :
    Sheaf (⊥ : GrothendieckTopology D) (Type (u + 1)) ⥤
      Sheaf (⊥ : GrothendieckTopology E) (Type (u + 1)) :=
  (sheafBotEquivalence _).functor ⋙
    (Functor.whiskeringLeft _ _ (Type (u + 1))).obj v.op ⋙
      (sheafBotEquivalence _).inverse

/-- The ringed geometric morphism of restriction, retaining the identity structural map.
The fields specify the existing `RingedToposMorphism`, including its induced module direct
image, rather than replacing that notion. Source: Stacks 08QR and 08PH
(blueprint: lem-trf-cotangent-lower-shriek). -/
structure RingedRestriction {E D : Type (u + 1)} [SmallCategory E] [SmallCategory D]
    (v : E ⥤ D) (O : Dᵒᵖ ⥤ RingCat.{u + 1}) where
  morphism : RingedToposMorphism (ringSheaf (v.op ⋙ O)) (ringSheaf O)
  inverse : morphism.inverse ≅ setInverse v
  structural : morphism.ringMap =
    inverse.hom.app ((sheafCompose ⊥ (forget RingCat.{u + 1})).obj (ringSheaf O))

/-- Precomposition on constant-coefficient module presheaves. Source: Stacks 08PH
(blueprint: lem-trf-cotangent-lower-shriek). -/
abbrev moduleInverse {E D : Type (u + 1)} [SmallCategory E] [SmallCategory D]
    (v : E ⥤ D) (R : Type (u + 1)) [CommRing R] :=
  (Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u + 1} R)).obj v.op

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The total derived left Kan extension and its normalized derived adjunction. No data
are chosen from an existence theorem. Normalization fixes the derived adjunction from the
ordinary Kan-extension adjunction. Source: Stacks 08PH
(blueprint: lem-trf-cotangent-lower-shriek). -/
structure DerivedRestriction {E D : Type (u + 1)} [SmallCategory E] [SmallCategory D]
    (v : E ⥤ D) (R : Type (u + 1)) [CommRing R] where
  geometric : RingedRestriction v ((Functor.const Dᵒᵖ).obj (RingCat.of R))
  /-- Objectwise left exactness. -/
  [exactLimits : PreservesFiniteLimits (moduleInverse v R)]
  /-- Objectwise right exactness. -/
  [exactColimits : PreservesFiniteColimits (moduleInverse v R)]
  left : (Eᵒᵖ ⥤ ModuleCat.{u + 1} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u + 1} R)
  adjunction : left ⊣ moduleInverse v R
  /-- Additivity of the left Kan extension. -/
  [additive : left.Additive]
  derived : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u + 1} R) ⥤
    DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u + 1} R)
  comparison : DerivedCategory.Q ⋙ derived ⟶
    left.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : derived.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u + 1} R) (.up ℤ))
  derivedAdjunction : derived ⊣ (moduleInverse v R).mapDerivedCategory
  normalization : ∀ (M : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u + 1} R) ℤ)
    (N : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u + 1} R) ℤ)
    (a : (left.mapHomologicalComplex (.up ℤ)).obj M ⟶ N),
    derivedAdjunction.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N)
      (comparison.app M ≫ DerivedCategory.Q.map a) =
      DerivedCategory.Q.map ((adjunction.mapHomologicalComplex (.up ℤ)).homEquiv M N a) ≫
        (moduleInverse v R).mapDerivedCategoryFactors.inv.app N
  counit : ∀ K : Dᵒᵖ ⥤ ModuleCat.{u + 1} R,
    IsIso (derivedAdjunction.counit.app
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj K)))

/-- The three target augmentations, in order `B/A`, `C/A`, `C/B`.
Source: Stacks 08QR (blueprint: lem-trf-cotangent-lower-shriek). -/
def target {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Fin 3 → Arrow CommRingCat.{u}
  | 0 => Arrow.mk f
  | 1 => Arrow.mk (f ≫ g)
  | 2 => Arrow.mk g

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The three projection functors, their structural presheaves and the tensor-product
normalization. The tensor square is a pushout of commutative rings, which is exactly
`Q ⊗_P B`, and fixes every induced map by its two inclusions. The other projections
are fixed as augmented algebras, including their base maps.
Source: Stacks 08QR, equation-three-maps
(blueprint: lem-trf-cotangent-lower-shriek). -/
structure Projections {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) where
  projection : ∀ i : Fin 3, PairSite f g ⥤ Site (target f g i).hom
  first : (projection 0).op ⋙ presentationRing f ≅ pairP f g
  firstBase : ∀ U : (PairSite f g)ᵒᵖ,
    (presentationBase f).app ((projection 0).op.obj U) ≫ first.hom.app U =
      ((pairDiagram f g).obj U).left.left.hom
  firstAugmentation : first.hom ≫ pairPB f g =
    Functor.whiskerLeft (projection 0).op (presentationAugmentation f)
  second : (projection 1).op ⋙ presentationRing (f ≫ g) ≅ pairQ f g
  secondBase : ∀ U : (PairSite f g)ᵒᵖ,
    (presentationBase (f ≫ g)).app ((projection 1).op.obj U) ≫ second.hom.app U =
      ((pairDiagram f g).obj U).left.right.hom
  secondAugmentation : second.hom ≫ pairQC f g =
    Functor.whiskerLeft (projection 1).op (presentationAugmentation (f ≫ g))
  tensorQ : pairQ f g ⟶ (projection 2).op ⋙ presentationRing g
  tensorB : (Functor.const _).obj B ⟶ (projection 2).op ⋙ presentationRing g
  tensorBase : tensorB = Functor.whiskerLeft (projection 2).op (presentationBase g)
  tensorSquare : ∀ U : (PairSite f g)ᵒᵖ,
    IsPushout ((pairPQ f g).app U) ((pairPB f g).app U)
      (tensorQ.app U) (tensorB.app U)
  tensorAugmentation : tensorQ ≫
    Functor.whiskerLeft (projection 2).op (presentationAugmentation g) = pairQC f g
  structural : ∀ i : Fin 3,
    RingedRestriction (projection i) (presentationRing (target f g i).hom ⋙ liftRing)
  structuralLeftExact : ∀ i : Fin 3,
    PreservesFiniteLimits (PresheafOfModules.pushforward₀.{u + 1} (projection i)
      (presentationRing (target f g i).hom ⋙ liftRing))
  structuralRightExact : ∀ i : Fin 3,
    PreservesFiniteColimits (PresheafOfModules.pushforward₀.{u + 1} (projection i)
      (presentationRing (target f g i).hom ⋙ liftRing))

/-- Identity semilinearity, using the canonical restriction-of-scalars identification.
Source: Stacks 08PH (blueprint: lem-trf-cotangent-lower-shriek). -/
def identityCoefficient {E : Type (u + 1)} [SmallCategory E]
    {R : Type (u + 1)} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{u + 1} R) :
    F ⟶ F ⋙ ModuleCat.restrictScalars (RingHom.id R) :=
  (Functor.rightUnitor F).inv ≫
    Functor.whiskerLeft F (ModuleCat.restrictScalarsId R).inv

/-- The specified bar representative of reindexing. After the canonical scalar-identity
identification it sends `(Uₙ → … → U₀, x)` to `(vUₙ → … → vU₀, x)` by `bar.formula`.
Source: Stacks 08PH (blueprint: lem-trf-cotangent-lower-shriek). -/
def reindex {E D : Type (u + 1)} [SmallCategory E] [SmallCategory D]
    (bar : CategoryColimitBarSystem.{u + 1}) (v : E ⥤ D)
    {R : Type (u + 1)} [CommRing R] (K : Dᵒᵖ ⥤ ModuleCat.{u + 1} R) :
    (bar.models E R).bar.obj (v.op ⋙ K) ⟶ (bar.models D R).bar.obj K :=
  bar.map v (RingHom.id R) (identityCoefficient (v.op ⋙ K)) ≫
    (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId R) (.up ℤ)).hom.app
      ((bar.models D R).bar.obj K) ≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u + 1} R) (.up ℤ)).hom.app
      ((bar.models D R).bar.obj K)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- All claims of the lower-shriek comparison, with the canonical derived maps retained.
`bar.models` supplies the constant-coefficient point morphisms, the constant inverse images,
and the derived colimits. `represented` fixes the map itself in the derived category, not
just its source and target up to isomorphism. Naturality is the natural-transformation field
`comparison`. Coefficients include the integer ring (with universe transport when needed).
Source: Stacks 08QR, 08QW, 08PF and 08PH
(blueprint: lem-trf-cotangent-lower-shriek). -/
structure LowerShriekData {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (bar : CategoryColimitBarSystem.{u + 1}) where
  sites : Projections f g
  shriek : ∀ (R : Type (u + 1)) [CommRing R] (i : Fin 3),
    DerivedRestriction (sites.projection i) R
  comparison : ∀ (R : Type (u + 1)) [CommRing R] (i : Fin 3),
    moduleInverse (sites.projection i) R ⋙ CochainComplex.singleFunctor _ 0 ⋙
      DerivedCategory.Q ⋙ (bar.models (PairSite f g) R).derived ⟶
        CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q ⋙
          (bar.models (Site (target f g i).hom) R).derived
  represented : ∀ (R : Type (u + 1)) [CommRing R] (i : Fin 3)
    (K : (Site (target f g i).hom)ᵒᵖ ⥤ ModuleCat.{u + 1} R),
    (comparison R i).app K =
      (bar.models (PairSite f g) R).model.hom.app ((sites.projection i).op ⋙ K) ≫
        DerivedCategory.Q.map (reindex bar (sites.projection i) K) ≫
          (bar.models (Site (target f g i).hom) R).model.inv.app K
  comparisonIso : ∀ (R : Type (u + 1)) [CommRing R] (i : Fin 3)
    (K : (Site (target f g i).hom)ᵒᵖ ⥤ ModuleCat.{u + 1} R),
    IsIso ((comparison R i).app K)

/-- The three constant-coefficient derived counits and their canonical derived-colimit
comparisons are isomorphisms, naturally in every degree-zero module presheaf.
Source: Stacks Cotangent Complex, Tag 08QW, using equation-three-maps of 08QR;
Cohomology on Sites, Tags 08PF and 08PH
(blueprint: lem-trf-cotangent-lower-shriek).

Proof:
1. Polynomial coordinates `P = A[S]`, `Q = P[T]` give `Q = A[S ⊕ T]` and
   `Q ⊗_P B = B[T]`. This constructs `sites.projection` and its two ring inclusions;
   the tensor universal property fixes their action on every morphism. On the bottom
   topology every presheaf is a sheaf. Restriction is exact objectwise, both for the
   variable structural rings and for constant coefficients. Apply
   lem-trf-continuous-cocontinuous-derived-shriek for the normalized derived adjunction.
2. At a presentation `V`, lem-trf-derived-shriek-comma-homology identifies the counit
   with the augmented bar complex of `(V ↓ uᵢ)`. Its augmentation sends `((U,a),x)`
   to `K(a)x`.
3. For the first projection use the section `P ↦ (P,P)` and the natural arrow
   `U → s₁u₁U` induced, before taking opposites, by `1_P` and `P → Q`.
   It projects to the identity. The comma category retracts onto `(V ↓ C₁)`;
   lem-trf-derived-colimit-bar's prism homotopy identifies the bar maps. The initial
   object `(V,1)` contracts the latter augmented bar complex by insertion. The
   first face recovers the chain; the remaining faces cancel in pairs, including
   the augmentation term in degree zero. This proves the first counit claim.
4. For the second projection use `Q ↦ (A,Q)` and the arrow `U → s₂u₂U`
   induced by `A → P` and `1_Q`. The identical comma retraction, prism homotopy and
   insertion contraction prove the second claim. No assumption that an arbitrary
   polynomial `A`-algebra over `Q` is polynomial over `P` is used.
5. For the third projection a comma object over `V = (Qbar → C)` is precisely
   a polynomial pair augmented to `Qbar`: a map `Q ⊗_P B → Qbar` corresponds to
   a map `Q → Qbar` agreeing with `P → B → Qbar`, by the tensor universal property.
   The comma coefficients are pulled back from the presheaf
   `(T → Qbar) ↦ K(T → Qbar → C)` on polynomial `B`-algebras.
6. Since `Qbar` is polynomial over `B`, apply
   lem-trf-cotangent-lower-shriek-polynomial-top. Its explicit augmentation gives
   exactly `K(a)x`, hence the third counit isomorphism by the comma computation.
7. The composite of derived left adjoints `Lπᵢ,! Lgᵢ,!` is canonically the
   derived colimit on pairs, since their right adjoints compose to the constant
   functor. Apply `Lπᵢ,!` to the counit isomorphism. The triangle identities identify
   this map with canonical reindexing. By lem-trf-derived-colimit-bar it has precisely
   the representative `reindex`, whose generator formula is `bar.formula` after
   identity scalar restriction. The bar models give `represented`, and all maps
   are natural in `K`.
8. With integer coefficients the same constructions are the constructions for abelian
   presheaves: all faces, augmentations and contractions are additive. The variable
   structural ring maps and augmentations were fixed in step 1 and are independent
   of the constant ring used for these counit calculations. -/
theorem lowerShriekData_nonempty {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (bar : CategoryColimitBarSystem.{u + 1}) : Nonempty (LowerShriekData f g bar) := by
  sorry

end Algebra.CotangentSites
