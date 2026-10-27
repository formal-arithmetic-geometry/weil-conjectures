module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Mathlib.Algebra.DualNumber
public import Sheaf.AlgebraicGeometry.MarkedCurveDeformations
public import Mathlib.RingTheory.Flat.Basic

/-! # Marked modules on split square-zero base changes

Source: Stacks Project, defos.tex, Tags 08VW and 0CYE; quot.tex, Tag 08W8;
more-algebra.tex, Tag 0D2I (blueprint: def-sfb-space-marked-split-module-deformations).
The bases are the actual trivial square-zero rings. All pullbacks and their composition
comparisons are the recorded tensor-normalized functors. Flatness is geometric-stalk
flatness over the base, including for modules which are not quasi-coherent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.SplitModule

variable {k : Type u} [Field k]
variable (X : AlgebraicSpace (Spec (.of k)))
variable (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

/-- The actual affine square-zero base over the field.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def base : AlgebraicSpace (Spec (.of k)) :=
  schemeSpace (ProperCurveFamily.directionBase k (𝟙 (Spec (.of k))) V)

/-- The base scheme represents the terminal sheaf on schemes over the base.
Source: Stacks, 025Y (blueprint: def-sfb-space-marked-split-module-deformations).
Proof: every scheme over Spec k has exactly one morphism over Spec k to Spec k.
Yoneda and the sheaf embedding preserve this terminal object. Terminality determines
all its structure maps uniquely, so this is a universal-property specification. -/
theorem baseTerminal_nonempty : Nonempty (IsTerminal
    (schemeSpace (Over.mk (𝟙 (Spec (.of k))))).obj) := by
  sorry

/-- The unique structure map to the terminal representable base sheaf.
Source: Stacks, 025Y (blueprint: def-sfb-space-marked-split-module-deformations). -/
def baseMap : X.obj ⟶ (schemeSpace (Over.mk (𝟙 (Spec (.of k))))).obj :=
  (Classical.choice (baseTerminal_nonempty (k := k))).from X.obj

/-- The special point of the affine square-zero base, as a map of sheaves.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def baseZero : (schemeSpace (Over.mk (𝟙 (Spec (.of k))))).obj ⟶ (base V).obj :=
  (Scheme.fppfTopology.over (Spec (.of k))).yoneda.map
    (ProperCurveFamily.directionReduction k (𝟙 (Spec (.of k))) V)

/-- Product with the affine square-zero base is an algebraic space.
Source: Stacks, 04T9 (blueprint: def-sfb-space-marked-split-module-deformations).
Proof: this is the sheaf fibre product over the terminal base sheaf; apply
lem-trf-space-fibre-products-etale-covers, using its representable base. -/
theorem space_isAlgebraicSpace : IsAlgebraicSpace (X.obj ⨯ (base V).obj) := by
  sorry

/-- The base change X times Spec(k direct-sum V), as the actual sheaf product over k.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def space : AlgebraicSpace (Spec (.of k)) :=
  ⟨X.obj ⨯ (base V).obj, space_isAlgebraicSpace X V⟩

/-- Projection to X.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def projection : space X V ⟶ X := ObjectProperty.homMk prod.fst

/-- Projection to the square-zero base.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def toBase : space X V ⟶ base V := ObjectProperty.homMk prod.snd

/-- The special-fibre inclusion, using the actual augmentation.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def fibre : X ⟶ space X V :=
  ObjectProperty.homMk (prod.lift (𝟙 X.obj) (baseMap X ≫ baseZero V))

variable {V}
variable {W : Type u} [AddCommGroup W] [Module k W] [Module kᵐᵒᵖ W] [IsCentralScalar k W]

/-- Contravariant change of square-zero base, identity on X.
Source: Stacks, 0CYE (blueprint: def-sfb-space-marked-split-module-deformations). -/
def change (f : V →ₗ[k] W) : space X W ⟶ space X V :=
  ObjectProperty.homMk (prod.map (𝟙 X.obj)
    ((Scheme.fppfTopology.over (Spec (.of k))).yoneda.map
      (ProperCurveFamily.directionMap k (𝟙 (Spec (.of k))) f)))

/-- Base change preserves the special-fibre inclusion.
Source: Stacks, 0CYE (blueprint: def-sfb-space-marked-split-module-deformations).
Proof: both maps have first projection the identity and second projection the
augmentation point, since fst composed with TrivSqZeroExt.map is fst. -/
theorem fibre_change (f : V →ₗ[k] W) : fibre X W ≫ change X f = fibre X V := by
  sorry

/-- Base change is over X.
Source: Stacks, 0CYE (blueprint: def-sfb-space-marked-split-module-deformations).
Proof: compose the product map with its first projection; it is the first projection. -/
theorem change_projection (f : V →ₗ[k] W) :
    change X f ≫ projection X V = projection X W := by
  sorry

/-- The special-fibre inclusion is a section of projection.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations).
Proof: the first projection of the defining product lift is the identity. -/
theorem fibre_projection : fibre X V ≫ projection X V = 𝟙 X := by
  sorry

/-- Flatness over the geometric local rings of the base. Restriction of scalars is
along the germ-normalized stalk map, not along a freely supplied algebra structure.
Source: Stacks, 08VW, 00HB
(blueprint: def-sfb-space-marked-split-module-deformations). -/
def GeometricallyFlat (N : (space X V).Modules) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of k))
    (x : yoneda.obj (Over.mk s) ⟶ (space X V).obj.obj),
    Module.Flat (SingleComplex.stalkRing s (x ≫ (toBase X V).hom.hom))
      ((ModuleCat.restrictScalars (SingleComplex.stalkMap (toBase X V) s x)).obj
        ((SingleComplex.stalkModel s x).modules.obj N))

/-- A flat module on the split thickening with its specified special-fibre marking.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
structure Marked (M : X.Modules) where
  module : (space X V).Modules
  flat : GeometricallyFlat X module
  marking : (moduleTensorPullback (fibre X V)).obj module ≅ M

/-- Marked isomorphism: the two markings commute with the pulled-back isomorphism.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def Related {M : X.Modules} (N N' : Marked X (V := V) M) : Prop :=
  ∃ e : N.module ≅ N'.module,
    (moduleTensorPullback (fibre X V)).map e.hom ≫ N'.marking.hom = N.marking.hom

/-- Isomorphism classes of marked flat modules. Quot takes the equivalence closure of
marked isomorphism; that relation is already an equivalence relation.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def Classes (M : X.Modules) := Quot (Related X (V := V) (M := M))

/-- The marked isomorphism class of a lift.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def classOf {M : X.Modules} (N : Marked X (V := V) M) : Classes X (V := V) M :=
  Quot.mk _ N

/-- The marking on a tensor pullback, using the recorded normalized composition iso.
Source: Stacks, 0CYE (blueprint: def-sfb-space-marked-split-module-deformations). -/
def pullbackMarking (f : V →ₗ[k] W) {M : X.Modules} (N : Marked X (V := V) M) :
    (moduleTensorPullback (fibre X W)).obj
      ((moduleTensorPullback (change X f)).obj N.module) ≅ M :=
  (moduleTensorComposition (fibre X W) (change X f)).app N.module ≪≫
    eqToIso (congrArg (fun h ↦ (moduleTensorPullback h).obj N.module) (fibre_change X f)) ≪≫
    N.marking

/-- The target lift is the actual tensor pullback, with its induced marking.
Source: Stacks, 0CYE (blueprint: def-sfb-space-marked-split-module-deformations). -/
def PullsBack (f : V →ₗ[k] W) {M : X.Modules}
    (N : Marked X (V := V) M) (N' : Marked X (V := W) M) : Prop :=
  ∃ e : (moduleTensorPullback (change X f)).obj N.module ≅ N'.module,
    (moduleTensorPullback (fibre X W)).map e.hom ≫ N'.marking.hom =
      (pullbackMarking X f N).hom

/-- The canonical marking of the trivial lift.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def trivialMarking (M : X.Modules) :
    (moduleTensorPullback (fibre X V)).obj
      ((moduleTensorPullback (projection X V)).obj M) ≅ M :=
  (moduleTensorComposition (fibre X V) (projection X V)).app M ≪≫
    eqToIso (congrArg (fun h ↦ (moduleTensorPullback h).obj M) (fibre_projection X)) ≪≫
    (moduleTensorPullbackId X).app M

/-- A marked lift is trivial precisely when it is marked-isomorphic to p-star M.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def IsTrivial {M : X.Modules} (N : Marked X (V := V) M) : Prop :=
  ∃ e : N.module ≅ (moduleTensorPullback (projection X V)).obj M,
    (moduleTensorPullback (fibre X V)).map e.hom ≫ (trivialMarking X M).hom = N.marking.hom

/-- Infinitesimal automorphisms of the actual trivial tensor lift.
Source: Stacks, 08VW(3) (blueprint: def-sfb-space-marked-split-module-deformations). -/
def AutZero (M : X.Modules) :=
  {g : (moduleTensorPullback (projection X V)).obj M ≅
      (moduleTensorPullback (projection X V)).obj M //
    (moduleTensorPullback (fibre X V)).map g.hom = 𝟙 _}

/-- Canonical identification of the pullback of a trivial lift with the trivial lift.
Source: Stacks, 0CYE (blueprint: def-sfb-space-marked-split-module-deformations). -/
def trivialChange (f : V →ₗ[k] W) (M : X.Modules) :
    (moduleTensorPullback (change X f)).obj
      ((moduleTensorPullback (projection X V)).obj M) ≅
        (moduleTensorPullback (projection X W)).obj M :=
  (moduleTensorComposition (change X f) (projection X V)).app M ≪≫
    eqToIso (congrArg (fun h ↦ (moduleTensorPullback h).obj M) (change_projection X f))

/-- Pull back an automorphism and conjugate by the canonical trivial-lift comparison.
Source: Stacks, 0CYE (blueprint: def-sfb-space-marked-split-module-deformations). -/
def changeAut (f : V →ₗ[k] W) {M : X.Modules} (g : AutZero X (V := V) M) :
    (moduleTensorPullback (projection X W)).obj M ≅
      (moduleTensorPullback (projection X W)).obj M :=
  (trivialChange X f M).symm ≪≫
    (moduleTensorPullback (change X f)).mapIso g.val ≪≫ trivialChange X f M

/-- A gluing over k plus k-epsilon-one plus k-epsilon-two restricts to both given lifts.
This base is D times_k D; the two maps retain the first and second infinitesimal
coordinate respectively.
Source: Stacks, 0D2I (blueprint: def-sfb-space-marked-split-module-deformations). -/
def IsGluing {M : X.Modules} (L : Marked X (V := k × k) M)
    (N₁ N₂ : Marked X (V := k) M) : Prop :=
  PullsBack X (LinearMap.fst k k k) L N₁ ∧ PullsBack X (LinearMap.snd k k k) L N₂

/-- Relabelling the special-fibre marking by an isomorphism.
Source: Stacks, 08VW (blueprint: def-sfb-space-marked-split-module-deformations). -/
def relabel {M M' : X.Modules} (e : M ≅ M') (N : Marked X (V := V) M) :
    Marked X (V := V) M' := ⟨N.module, N.flat, N.marking ≪≫ e⟩

/-- Multiplication by a field element on a chart's regular functions.
Source: Stacks, 08W8 (blueprint: def-sfb-space-marked-split-module-deformations). -/
def chartScalar (U : X.EtaleSite) (a : k) : X.structureSheaf.obj.obj (op U) :=
  (Scheme.Γ.map U.obj.left.hom.op) ((Scheme.ΓSpecIso (.of k)).inv a)

/-- Scalar endomorphisms are uniquely determined by multiplication on every chart.
Source: Stacks, 08W8 (blueprint: def-sfb-space-marked-split-module-deformations).
Proof: multiply each section by the pullback of a. These maps are linear since each
chart ring is commutative. Restrictions commute with these multiplications by the
structure-map triangle over k. Hence they give a module morphism; evaluation on
all chart sections proves uniqueness. -/
theorem scalarEnd_existsUnique (M : X.Modules) (a : k) :
    ∃! h : M ⟶ M, ∀ (U : X.EtaleSite) (m : M.val.obj (op U)),
      h.val.app (op U) m = chartScalar X U a • m := by
  sorry

/-- The canonical scalar endomorphism, selected by its sectionwise formula.
Source: Stacks, 08W8 (blueprint: def-sfb-space-marked-split-module-deformations). -/
def scalarEnd (M : X.Modules) (a : k) : M ⟶ M :=
  Classical.choose (scalarEnd_existsUnique X M a)

variable [HasDerivedCategory.{w} X.SmallModules]

/-- Ext in the derived category of all modules, computed on the equivalent small
ringed site. No quasi-coherence restriction is made.
Source: Stacks, 06XV (blueprint: def-sfb-space-marked-split-module-deformations). -/
abbrev Ext (M : X.Modules) (n : ℤ) :=
  (DerivedCategory.singleFunctor X.SmallModules 0).obj (X.smallModuleRestriction.obj M) ⟶
    ((DerivedCategory.singleFunctor X.SmallModules 0).obj
      (X.smallModuleRestriction.obj M))⟦n⟧

/-- Usual scalar multiplication on Ext, by the shifted target scalar endomorphism.
Source: Stacks, 06XV, 08W8
(blueprint: def-sfb-space-marked-split-module-deformations). -/
def extScalar {M : X.Modules} (n : ℤ) (a : k) (ξ : Ext X M n) : Ext X M n :=
  ξ ≫ (shiftFunctor (DerivedCategory X.SmallModules) n).map
    ((DerivedCategory.singleFunctor X.SmallModules 0).map
      (X.smallModuleRestriction.map (scalarEnd X M a)))

/-- The usual conjugation of Ext under an isomorphism of its two coefficients.
Source: Stacks, 06XV (blueprint: def-sfb-space-marked-split-module-deformations). -/
def extRelabel {M M' : X.Modules} (e : M ≅ M') (n : ℤ) (ξ : Ext X M n) : Ext X M' n :=
  (DerivedCategory.singleFunctor X.SmallModules 0).map (X.smallModuleRestriction.map e.inv) ≫
    ξ ≫ (shiftFunctor (DerivedCategory X.SmallModules) n).map
      ((DerivedCategory.singleFunctor X.SmallModules 0).map (X.smallModuleRestriction.map e.hom))

end AlgebraicGeometry.AlgebraicSpace.SplitModule
