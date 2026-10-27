module

public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # The affine reduced coproduct with arbitrary module coefficients

Source: Stacks, Cohomology on Sites, Tags 01F8 and 01FB; Modules on Sites, Tag 03EL;
Milne, Abelian Varieties, I, calculation (3) before Lemma 12.2, printed p.55
(blueprint: def-sfb-abelian-affine-reduced-coproduct).

Cohomology is literally Mathlib's Ext of the underlying additive sheaf on the existing
small affine etale model. Flat pullback is fixed by its unique morphism of delta functors,
normalized on every degree-zero section. Coefficients use the existing scalar adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.AlgebraicSpace
namespace ReducedCoproduct

variable {S : Scheme.{u}}

/-- Additive-sheaf cohomology after actual restriction to the affine etale basis.
Source: Stacks, Tags 03ED, 039Z and 01F8
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
abbrev cohomologyFunctor (X : AlgebraicSpace S) (n : ℕ) :
    X.SmallModules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf.{u} X.smallStructureRings ⋙
    Sheaf.functorH.{u, u, u, u} X.smallEtaleModelTopology n

/-- Evaluate a degree-zero class on the constant integer section 1 of a chart.
Source: Stacks, Tag 01F8 (blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def zeroValue (X : AlgebraicSpace S) (M : X.SmallModules)
    (x : (cohomologyFunctor X 0).obj M) (U : X.SmallEtaleModelᵒᵖ) : M.val.obj U :=
  (Ext.addEquiv₀ x).hom.app U
    ((toSheafify X.smallEtaleModelTopology
      ((Functor.const X.SmallEtaleModelᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)))).app U
        (ULift.up 1))

/-- A natural family on cohomology, for the already fixed tensor inverse image.
Source: Stacks, Tags 01F8 and 01FB
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
abbrev PullbackFamily {X Y : AlgebraicSpace S} (f : X ⟶ Y) :=
  ∀ n : ℕ, cohomologyFunctor Y n ⟶ smallModuleTensorPullback f ⋙ cohomologyFunctor X n

/-- Boundary compatibility and degree-zero normalization characterize canonical pullback.
The boundary condition concerns every module short complex whose two underlying additive
sequences are short exact. The zero-degree condition is on every actual global section.
Source: Stacks, Tags 01F8, 01FB and 015B
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def IsPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) (c : PullbackFamily f) : Prop :=
  (∀ (E : ShortComplex Y.SmallModules)
    (hE : (E.map (SheafOfModules.toSheaf Y.smallStructureRings)).ShortExact)
    (hF : ((E.map (smallModuleTensorPullback f)).map
      (SheafOfModules.toSheaf X.smallStructureRings)).ShortExact)
    (n : ℕ) (x : (cohomologyFunctor Y n).obj E.X₃),
    (c (n + 1)).app E.X₁ (x.comp hE.extClass rfl) =
      ((c n).app E.X₃ x).comp hF.extClass rfl) ∧
  ∀ (M : Y.SmallModules) (s : SheafOfModules.unit Y.smallStructureRings ⟶ M)
    (x : (cohomologyFunctor Y 0).obj M),
    (∀ U : Y.SmallEtaleModelᵒᵖ,
      zeroValue Y M x U = s.val.app U (1 : Y.smallStructureRings.obj.obj U)) →
    ∀ V : X.SmallEtaleModelᵒᵖ,
      zeroValue X ((smallModuleTensorPullback f).obj M) ((c 0).app M x) V =
        ((Poincare.pullbackUnit f).inv ≫ (smallModuleTensorPullback f).map s).val.app V
          (1 : X.smallStructureRings.obj.obj V)

/-- Flat pullback has a unique normalized cohomology family.
Source: Stacks, Tags 01F8, 01FB, 015B and 03EL
(blueprint: def-sfb-abelian-affine-reduced-coproduct).
Proof: flat tensor inverse image is exact on the ringed etale topos. Its composite with
additive-sheaf cohomology is therefore a delta functor on module sheaves. Degree zero is
ordinary global sections, and the unit multiplication comparison gives its natural
pullback. Additive-sheaf cohomology is effaceable on module sheaves: embed in injective
module sheaves, which are acyclic for underlying additive global sections. The universal
delta-functor theorem extends the zero-degree map uniquely. The connecting maps are Yoneda
composition with the displayed short-exact-sequence classes. Restriction to the small
model preserves these constructions. Induction using injective embeddings proves uniqueness.
-/
theorem pullbackFamily_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : MapIsFlat f) : ∃! c : PullbackFamily f, IsPullback f c := by
  sorry

/-- The unique delta-functor extension of ordinary flat section pullback.
Source: Stacks, Tags 01F8 and 01FB
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def pullbackFamily {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : MapIsFlat f) :
    PullbackFamily f :=
  (pullbackFamily_existsUnique f hf).choose

section Coefficients

variable (R : Type u) [CommRing R] (T : Over S) (e : T.left ≅ Spec (.of R))
  {X Y : AlgebraicSpace S} (p : Y ⟶ schemeSpace T) (f : X ⟶ Y)
  (q : X ⟶ schemeSpace T)

/-- The coefficient comparison is fixed on each pure global section `1 tensor n`.
Source: Stacks, Tag 03EL (blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def CoefficientNormalized
    (d : affineScalarPullback R T e Y p ⋙ smallModuleTensorPullback f ≅
      affineScalarPullback R T e X q) : Prop :=
  ∀ (N : ModuleCat.{u} R) (n : N),
    (Poincare.pullbackUnit f).inv ≫
      (smallModuleTensorPullback f).map ((affineScalarAdjunction R T e Y p).unit.app N n) ≫
        d.hom.app N = (affineScalarAdjunction R T e X q).unit.app N n

/-- Composition of scalar extension has its unique pure-section normalization.
Source: Stacks, Tags 03EL and 03D7
(blueprint: def-sfb-abelian-affine-reduced-coproduct).
Proof: on each etale chart the two sides are the sheafifications of iterated scalar
extension. Send b tensor (a tensor n) to b times f-sharp(a) tensor n; send c tensor n
back to c tensor (1 tensor n). Tensor balancing proves the two composites are identities.
The commuting triangle identifies the R-actions, so these maps glue and are natural in N.
Pure sections 1 tensor n generate these module sheaves locally as O-modules, so the
normalization determines the entire natural isomorphism uniquely. No flatness of N is used.
-/
theorem coefficientComparison_existsUnique (w : f ≫ p = q) :
    ∃! d : affineScalarPullback R T e Y p ⋙ smallModuleTensorPullback f ≅
        affineScalarPullback R T e X q,
      CoefficientNormalized R T e p f q d := by
  sorry

/-- The actual scalar-extension comparison, chosen by its complete normalization.
Source: Stacks, Tag 03EL (blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def coefficientComparison (w : f ≫ p = q) :
    affineScalarPullback R T e Y p ⋙ smallModuleTensorPullback f ≅
      affineScalarPullback R T e X q :=
  (coefficientComparison_existsUnique R T e p f q w).choose

/-- Canonical flat pullback with the common affine-base coefficient identification.
Source: Stacks, Tags 01F8, 01FB and 03EL
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def coefficientPullback (hf : MapIsFlat f) (w : f ≫ p = q)
    (N : ModuleCat.{u} R) (n : ℕ) :
    (cohomologyFunctor Y n).obj ((affineScalarPullback R T e Y p).obj N) ⟶
      (cohomologyFunctor X n).obj ((affineScalarPullback R T e X q).obj N) :=
  (pullbackFamily f hf n).app ((affineScalarPullback R T e Y p).obj N) ≫
    (cohomologyFunctor X n).map ((coefficientComparison R T e p f q w).hom.app N)

end Coefficients

section AbelianFamily

variable (A : AlgebraicSpace S) (g : CommutativeSpaceGroup A) (T : Over S)

/-- The affine base change B=A times_S T, as the existing sheaf fibre product.
Source: Milne I, calculation (3) before Lemma 12.2; Stacks, Tag 02X2
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
abbrev family := Poincare.product (groupSpaceProjection A)
  (groupSchemeMap (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 S)))

/-- Structure map B to T is the second actual fibre-product projection.
Source: Stacks, Tag 02X2 (blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def projection : family A T ⟶ schemeSpace T :=
  Poincare.snd (groupSpaceProjection A)
    (groupSchemeMap (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 S)))

/-- The product C=B times_T B.
Source: Milne I, calculation (3) before Lemma 12.2
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
abbrev square := Poincare.product (projection A T) (projection A T)

/-- The first projection C to B.
Source: Stacks, Tag 02X2 (blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def first : square A T ⟶ family A T := Poincare.fst (projection A T) (projection A T)

/-- The second projection C to B.
Source: Stacks, Tag 02X2 (blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def second : square A T ⟶ family A T := Poincare.snd (projection A T) (projection A T)

/-- The common structure map q:C to T, using the first projection.
Source: Stacks, Tag 02X2 (blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def squareProjection : square A T ⟶ schemeSpace T := first A T ≫ projection A T

/-- Base-changed addition, obtained by the universal property of both fibre products.
Source: Milne I, calculation (3) before Lemma 12.2
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def addition : square A T ⟶ family A T :=
  Poincare.pair
    (Poincare.pair
      (first A T ≫ Poincare.fst (groupSpaceProjection A)
        (groupSchemeMap (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 S))))
      (second A T ≫ Poincare.fst (groupSpaceProjection A)
        (groupSchemeMap (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 S))))
      (Poincare.baseMap_eq _ _) ≫ Poincare.addition A g)
    (squareProjection A T) (Poincare.baseMap_eq _ _)

/-- Both nondefinitional structure triangles commute by the fibre-product projections.
Source: Stacks, Tag 02X2 (blueprint: def-sfb-abelian-affine-reduced-coproduct).
Proof: the second projection of the pair defining addition is q by pullback.lift_snd.
The equation for the other projection is the symmetry of pullback.condition for B times_T B.
-/
theorem triangles :
    addition A g T ≫ projection A T = squareProjection A T ∧
      second A T ≫ projection A T = squareProjection A T := by
  sorry

/-- Addition and both projections of the base-changed abelian family are flat.
Source: Stacks, Tag 01VF and flat base change; Milne I, group-law calculation
(blueprint: def-sfb-abelian-affine-reduced-coproduct).
Proof: the two projections are base changes of the smooth structural map A to S, hence
smooth and flat after every T to S. The map (x,y) to (x+y,y) is an automorphism of B times_T B,
with inverse (z,y) to (z-y,y). Addition is its composite with the first projection,
so it too is smooth and flat. Etale chart locality gives the recorded flatness predicates.
The argument applies to every T, without a Noetherian, reducedness or characteristic condition.
-/
theorem maps_flat (hA : Poincare.IsAbelianFamily (groupSpaceProjection A)) :
    MapIsFlat (addition A g T) ∧ MapIsFlat (first A T) ∧ MapIsFlat (second A T) := by
  sorry

/-- The reduced coproduct m-star minus p1-star minus p2-star with N occurring once.
Every map uses the normalized scalar-extension identification with the same q-pullback.
Source: Milne I, calculation (3) before Lemma 12.2, printed p.55, coherent analogue;
Stacks, Tags 01F8, 01FB and 03EL
(blueprint: def-sfb-abelian-affine-reduced-coproduct). -/
def map (hA : Poincare.IsAbelianFamily (groupSpaceProjection A))
    (R : Type u) [CommRing R] (e : T.left ≅ Spec (.of R)) (N : ModuleCat.{u} R) :
    (cohomologyFunctor (family A T) 2).obj
        ((affineScalarPullback R T e (family A T) (projection A T)).obj N) ⟶
      (cohomologyFunctor (square A T) 2).obj
        ((affineScalarPullback R T e (square A T) (squareProjection A T)).obj N) :=
  coefficientPullback R T e (projection A T) (addition A g T) (squareProjection A T)
      (maps_flat A g T hA).1 (triangles A g T).1 N 2 -
    coefficientPullback R T e (projection A T) (first A T) (squareProjection A T)
      (maps_flat A g T hA).2.1 rfl N 2 -
    coefficientPullback R T e (projection A T) (second A T) (squareProjection A T)
      (maps_flat A g T hA).2.2 (triangles A g T).2 N 2

end AbelianFamily
end ReducedCoproduct
end AlgebraicGeometry.AlgebraicSpace
