/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Exact inverse image for constant left-module sheaves

Source: Stacks Project, Sites, Proposition 00YV (2), (5), (6), its fixed-ring
scalar-endomorphism proof, and Section 00XZ; Derived Categories, Tag 015F
(blueprint: lem-pe-constant-left-module-inverse-image).

The lift is characterized by its underlying-set comparison, addition and scalar
endomorphisms, and the original geometric adjunction unit. Comparisons have a
normalization equation and uniqueness; arbitrary unrelated functors are never compared.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
namespace ConstantLeftModuleInverseImage

/-- Constant-coefficient module sheaves, using the recorded general-site category.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev Modules {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :=
  ringedSiteModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Forget constant scalars, retaining the abelian sheaf.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev V {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :
    Modules J Λ ⥤ Sheaf J AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Forget the abelian group structure.
Source: Stacks, 00YV (2) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev U {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J (Type u) :=
  sheafCompose J (forget AddCommGrpCat.{u})

/-- The underlying-set functor on constant-coefficient modules.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev W {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :
    Modules J Λ ⥤ Sheaf J (Type u) := V J Λ ⋙ U J

/-- Characterization of a sheaf's addition map by its values on sections.
The projections allow arbitrary choices of categorical products.
Source: Stacks, discussion preceding 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsAddition {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A) : Prop :=
  ∀ (T : Cᵒᵖ) (x : ((U J).obj A ⨯ (U J).obj A).obj.obj T),
    a.hom.app T x =
      @id (A.obj.obj T)
        ((prod.fst : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A).hom.app T x) +
      @id (A.obj.obj T)
        ((prod.snd : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A).hom.app T x)

/-- A constant scalar endomorphism of the underlying abelian sheaf. This is
not required to be a module morphism when the ring is noncommutative.
Source: Stacks, fixed-ring paragraph in the proof of 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsScalar {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J Λ) (r : Λ) (a : (V J Λ).obj M ⟶ (V J Λ).obj M) : Prop :=
  ∀ (T : Cᵒᵖ) (x : M.val.obj T),
    a.hom.app T x =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x

/-- The underlying set sheaf of the sheafified constant ring `Λ_C`.
Source: Stacks, 00YV (2) and 0H7J (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev CoeffSet {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] : Sheaf J (Type u) :=
  (sheafCompose J (forget RingCat.{u})).obj ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Characterization of the addition map of the constant ring sheaf by its values
on sections. Source: Stacks, ring paragraph of the proof of 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsRingAdd {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) +
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

/-- Characterization of the multiplication map of the constant ring sheaf by its
values on sections, in the given order (no commutativity). Source: Stacks, ring
paragraph of the proof of 00YV (blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsRingMul {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) *
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

end ConstantLeftModuleInverseImage
open ConstantLeftModuleInverseImage

/-- A normalized lift of the given geometric morphism. The set comparisons and
unit equations connect both adjunctions to `L ⊣ R`; addition and scalar equations
specify the transported operations. Zero and negation are determined by addition.
The ring comparison is normalized on every scalar summand of the constant sheaf
(these summands determine it uniquely) and carries the addition and multiplication
transported by `L` to those of the target constant ring.
Source: Stacks, 00YV (2), (5), (6), 0H7J, and the node's proof steps 1--6
(blueprint: lem-pe-constant-left-module-inverse-image). -/
structure ConstantLeftModuleInverseImageLift
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L) where
  /-- The comparison `f⁻¹|Λ_C| ≅ |Λ_D|`, written on `L` of the constant set sheaf. -/
  ringUnderlying :
    L.obj ((constantSheaf J (Type u)).obj Λ) ≅
      (sheafCompose K (forget RingCat.{u})).obj
        ((constantSheaf K RingCat.{u}).obj (RingCat.of Λ))
  /-- The comparison carries the addition `L(+) ∘ p⁻¹` transported by `L` to the
  addition of `Λ_D`. -/
  ring_add : ∀ (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ),
    IsRingAdd J Λ m → IsRingAdd K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
          L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          ringUnderlying.hom =
        prod.map
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom)
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom) ≫ m'
  /-- The comparison carries the multiplication `L(μ) ∘ p⁻¹` transported by `L`
  to the multiplication of `Λ_D`. With `ring_add`, the bijectivity of the
  comparison and `constant_scalar` at `0` and `1`, it is a ring-sheaf isomorphism
  from the transported ring structure on `f⁻¹Λ_C` to `Λ_D`. -/
  ring_mul : ∀ (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ),
    IsRingMul J Λ m → IsRingMul K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
          L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          ringUnderlying.hom =
        prod.map
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom)
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom) ≫ m'
  pointIso : L.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
    (constantSheaf K (Type u)).obj PUnit.{u+1}
  constant_scalar : ∀ r : Λ,
    L.map ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫ ringUnderlying.hom ≫
      (constantCommuteCompose K (forget RingCat.{u})).hom.app (RingCat.of Λ) =
      pointIso.hom ≫ (constantSheaf K (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))
  moduleFunctor : Modules J Λ ⥤ Modules K Λ
  moduleDirect : Modules K Λ ⥤ Modules J Λ
  moduleAdj : moduleFunctor ⊣ moduleDirect
  additive : moduleFunctor.Additive
  preservesFiniteLimits : PreservesFiniteLimits moduleFunctor
  preservesFiniteColimits : PreservesFiniteColimits moduleFunctor
  abelianInverse : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}
  abelianDirect : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}
  abelianAdj : abelianInverse ⊣ abelianDirect
  abelianSetIso : abelianInverse ⋙ U K ≅ U J ⋙ L
  abelianDirectSetIso : abelianDirect ⋙ U J ≅ U K ⋙ R
  abelian_addition : ∀ (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A)
    (b : (U K).obj (abelianInverse.obj A) ⨯ (U K).obj (abelianInverse.obj A) ⟶
      (U K).obj (abelianInverse.obj A)),
    IsAddition J A a → IsAddition K (abelianInverse.obj A) b →
      b ≫ abelianSetIso.hom.app A =
        prod.map (abelianSetIso.hom.app A) (abelianSetIso.hom.app A) ≫
          inv (prodComparison L ((U J).obj A) ((U J).obj A)) ≫ L.map a
  abelian_unit : ∀ A : Sheaf J AddCommGrpCat.{u},
    (U J).map (abelianAdj.unit.app A) ≫
      abelianDirectSetIso.hom.app (abelianInverse.obj A) ≫
      R.map (abelianSetIso.hom.app A) = adj.unit.app ((U J).obj A)
  underlyingIso : moduleFunctor ⋙ V K Λ ≅ V J Λ ⋙ abelianInverse
  directUnderlyingIso : moduleDirect ⋙ V J Λ ≅ V K Λ ⋙ abelianDirect
  moduleSetIso : moduleFunctor ⋙ W K Λ ≅ W J Λ ⋙ L
  moduleSetIso_compatibility : ∀ M : Modules J Λ,
    (U K).map (underlyingIso.hom.app M) ≫ abelianSetIso.hom.app ((V J Λ).obj M) =
      moduleSetIso.hom.app M
  scalar_compatibility : ∀ (M : Modules J Λ) (r : Λ)
    (a : (V J Λ).obj M ⟶ (V J Λ).obj M)
    (b : (V K Λ).obj (moduleFunctor.obj M) ⟶ (V K Λ).obj (moduleFunctor.obj M)),
    IsScalar J Λ M r a → IsScalar K Λ (moduleFunctor.obj M) r b →
      b ≫ underlyingIso.hom.app M = underlyingIso.hom.app M ≫ abelianInverse.map a
  unit_compatibility : ∀ M : Modules J Λ,
    (V J Λ).map (moduleAdj.unit.app M) ≫
      directUnderlyingIso.hom.app (moduleFunctor.obj M) ≫
      abelianDirect.map (underlyingIso.hom.app M) = abelianAdj.unit.app ((V J Λ).obj M)

/-- The lift with its normalized comparisons and actual termwise derived descent.
Composition compares only lifts of `L ⋙ L₂`, and change of presentation compares
only lifts joined by a specified set-level natural isomorphism. Their uniqueness
implies identity, associativity, and commuting squares, including localization
squares. Localization uses `J.over X` and Mathlib's actual sectionwise restriction,
with its coefficient isomorphism normalized on constant sections.
Source: Stacks, 00YV, 00XZ/00Y0, 04IX, 0B65, and 015F; node proof steps 7--10
(blueprint: lem-pe-constant-left-module-inverse-image). -/
structure ConstantLeftModuleInverseImageData
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    extends ConstantLeftModuleInverseImageLift J K Λ L R adj hL where
  composition_coherence :
    ∀ {E : Type u} [SmallCategory E] (H : GrothendieckTopology E)
      [HasWeakSheafify H RingCat.{u}]
      (L₂ : Sheaf K (Type u) ⥤ Sheaf H (Type u))
      (R₂ : Sheaf H (Type u) ⥤ Sheaf K (Type u))
      (adj₂ : L₂ ⊣ R₂) (hL₂ : PreservesFiniteLimits L₂)
      (d₂ : ConstantLeftModuleInverseImageLift K H Λ L₂ R₂ adj₂ hL₂)
      (d₃ : ConstantLeftModuleInverseImageLift J H Λ (L ⋙ L₂) (R₂ ⋙ R)
        (adj.comp adj₂) (@comp_preservesFiniteLimits _ _ _ _ _ _ L L₂ hL hL₂)),
      ∃! i : d₃.moduleFunctor ≅ moduleFunctor ⋙ d₂.moduleFunctor,
        ∀ M : Modules J Λ,
          (W H Λ).map (i.hom.app M) ≫ d₂.moduleSetIso.hom.app (moduleFunctor.obj M) ≫
            L₂.map (moduleSetIso.hom.app M) = d₃.moduleSetIso.hom.app M
  presentation_coherence :
    ∀ (L' : Sheaf J (Type u) ⥤ Sheaf K (Type u))
      (R' : Sheaf K (Type u) ⥤ Sheaf J (Type u))
      (adj' : L' ⊣ R') (hL' : PreservesFiniteLimits L')
      (d' : ConstantLeftModuleInverseImageLift J K Λ L' R' adj' hL') (e : L ≅ L'),
      ∃! i : moduleFunctor ≅ d'.moduleFunctor, ∀ M : Modules J Λ,
        (W K Λ).map (i.hom.app M) ≫ d'.moduleSetIso.hom.app M =
          moduleSetIso.hom.app M ≫ e.hom.app ((W J Λ).obj M)
  localization_coherence : ∀ X : C,
    ∃ (Rₓ : Sheaf (J.over X) (Type u) ⥤ Sheaf J (Type u))
      (adjₓ : J.overPullback (Type u) X ⊣ Rₓ)
      (hLₓ : PreservesFiniteLimits (J.overPullback (Type u) X))
      (dₓ : ConstantLeftModuleInverseImageLift J (J.over X) Λ
        (J.overPullback (Type u) X) Rₓ adjₓ hLₓ)
      (c : ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over X ≅
        (constantSheaf (J.over X) RingCat.{u}).obj (RingCat.of Λ)),
      (∀ (T : (Over X)ᵒᵖ) (r : Λ), c.hom.hom.app T
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app
          ((Over.forget X).op.obj T) r) =
        (toSheafify (J.over X)
          ((Functor.const (Over X)ᵒᵖ).obj (RingCat.of Λ))).app T r) ∧
      ∃ i : dₓ.moduleFunctor ≅
          SheafOfModules.overFunctor ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) X ⋙
            SheafOfModules.restrictScalars c.inv,
        ∀ (M : Modules J Λ) (T : (Over X)ᵒᵖ)
          (x : (dₓ.moduleFunctor.obj M).val.obj T),
          (i.hom.app M).val.app T x = (dₓ.moduleSetIso.hom.app M).hom.app T x
  termwise_quasiIso :
    ∀ [moduleFunctor.Additive] {X Y : CochainComplex (Modules J Λ) ℤ} (f : X ⟶ Y),
      HomologicalComplex.quasiIso (Modules J Λ) (ComplexShape.up ℤ) f →
        HomologicalComplex.quasiIso (Modules K Λ) (ComplexShape.up ℤ)
          ((moduleFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  derivedFunctor :
    ∀ [HasDerivedCategory.{w} (Modules J Λ)] [HasDerivedCategory.{w} (Modules K Λ)]
      [moduleFunctor.Additive],
      ∃ Fplus : DerivedCategory.Plus (Modules J Λ) ⥤ DerivedCategory.Plus (Modules K Λ),
        Nonempty (DerivedCategory.Plus.Q ⋙ Fplus ≅
          moduleFunctor.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q)

/-- A geometric inverse image canonically lifts to exact inverse image on left
modules over the sheafified constant ring, with normalized ring, abelian, unit,
composition, localization, and termwise bounded-below derived comparisons.

Source: Stacks Project, Sites, 00YV (2), (5), (6), fixed-ring paragraph; 0H7J;
Modules on Sites, 04JC; Derived Categories, 015F
(blueprint: lem-pe-constant-left-module-inverse-image).

Proof (the ten steps of the node, with their dependency names):

1. Write $L=f^{-1}$, $R=f_*$. By the constant-sheaf definition and sheafification universal
   property, maps from the constant set sheaf $\underline E$ to a sheaf $H$ are families,
   indexed by $e\in E$, of compatible sections of $H$, equivalently maps $*\to H$. Thus
   $\underline E$, with its scalar-section inclusions, is the coproduct of $E$ copies of the
   terminal sheaf $*$. The new ring-sheafification comparison identifies $|\Lambda_{\mathcal
   C}|$ and $|\Lambda_{\mathcal D}|$ with these constant set sheaves, including their scalar-
   section inclusions. The index set $\Lambda$ is small in the chosen coefficient universe.
   Since $L$ is a left adjoint it preserves this coproduct, and since it preserves finite limits
   it sends $*$ to $*$. The coproduct universal properties therefore give mutually inverse maps
   $c:L|\Lambda_{\mathcal C}|\to|\Lambda_{\mathcal D}|$ and $d$ carrying every scalar inclusion
   to the same scalar inclusion: each composite is the identity because it is so on every
   summand. No presheaf inverse image is used.
   Uses: def-weil-pbc-constant-sheaf, def-weil-pbc-sheafification, def-weil-size-convention,
   lem-pe-ring-sheafification-underlying-sets, lem-weil-pbc-left-adjoint-preserves-colimits,
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise.

2. Transport the ring operations by $L$ using its canonical terminal and product comparisons.
   For example the multiplication is $L(\mu)\circ p^{-1}$, where $p:L(A\times A)\cong LA\times
   LA$ and $A=|\Lambda_{\mathcal C}|$; zero and one use $L*\cong *$. Applying the functor to
   each ring-axiom diagram gives the same identities after these comparisons, so this is an
   associative unital ring sheaf, with no commutativity requirement. Check that $c$ respects
   operations. For constant scalar maps $s_a,s_b:*\to A$, functoriality and the product
   comparison give $L(\mu)p^{-1}(Ls_a,Ls_b)=L(s_{ab})$; after $c$ this is $s_{ab}$ on $\mathcal
   D$. The identical equation for addition has $a+b$ in place of $ab$, and constants and
   negation give $0,1,-a$. By the new comparison and the local-section theorem, sections of
   either constant ring are locally represented by constants. Two sections admit a common
   covering refinement; on it the preceding equations prove compatibility with each binary
   operation, and the sheaf uniqueness axiom then proves it globally. Thus $c$ is a ring-sheaf
   isomorphism carrying each scalar to itself.
   Uses: lem-pe-ring-sheafification-underlying-sets, lem-weil-pbc-site-sheafification-sections-
   local, lem-weil-pbc-site-sheaf-sets-limits-sectionwise.

3. The right adjoint $R$ preserves finite products. Apply the abelian-group-object adjunction
   lemma, and the equivalence between abelian sheaves and abelian group objects, to obtain
   $L_{\rm Ab}\dashv R_{\rm Ab}$ with the original underlying set functors, unit and counit. For
   a module sheaf $M$, its action is a sheaf map $a_M:\Lambda_{\mathcal C}\times M\to M$: this
   is sectionwise the action in the module definition, and semilinearity is precisely its
   naturality. On $LM$ define the action by $L(a_M)p^{-1}(c^{-1}\times1)$. Each module-axiom
   diagram uses only finite products, the ring operations and the action; applying $L$ and the
   comparisons proves its commutativity. Consequently this action, with the transported abelian
   operations, is a left $\Lambda_{\mathcal D}$-module sheaf. Applying $L$ to the action-
   compatibility equation for a module map proves that its image is linear, so this defines
   $f^*_{\Lambda}$. Forgetting its action leaves exactly $L_{\rm Ab}M$. Evaluating the action on
   a constant scalar $a$ shows that its unary scalar map is $L(\lambda_a)$, as in the statement.
   Uses: lem-weil-pbc-right-adjoint-preserves-limits, lem-weil-pbc-adjunction-lifts-abelian-
   group-objects, lem-weil-pbc-sheaf-algebraic-structures-objects, def-weil-sheaf-of-modules-
   category, lem-weil-pbc-site-sheaf-sets-limits-sectionwise.

4. Define the module direct image as follows. The canonical ring map $\gamma:\Lambda_{\mathcal
   C}\to R\Lambda_{\mathcal D}$ is $R(c)\circ\eta_{\Lambda_{\mathcal C}}$. Naturality of $\eta$
   with respect to each ring operation, together with its product comparison, shows it is a ring
   map; composing with $R(c)$ preserves this property. Explicitly for a binary operation $m$ the
   identity is $\eta_A m=R(L(m)p^{-1})\,\rho^{-1}(\eta_A\times\eta_A)$, where $\rho:R(LA\times
   LA)\cong RLA\times RLA$; zero and one use the terminal comparison. These identities follow by
   naturality of $\eta$ for $m$ and for the two projections. For a module $N$ on $\mathcal D$,
   give $RN$ the action $R(a_N)\rho^{-1}(\gamma\times1)$. The product-preserving functor $R$
   sends the module-axiom diagrams to commuting diagrams, and restriction along the ring map
   $\gamma$ gives the asserted module axioms. The same formula on maps defines a functor
   $f_{*,\Lambda}$ with underlying $R_{\rm Ab}$. On constant scalars its unary action is
   $R(\lambda_a)$, since $\gamma$ carries a constant scalar to its direct-image scalar section.
   Uses: lem-weil-pbc-right-adjoint-preserves-limits, lem-weil-pbc-adjunction-lifts-abelian-
   group-objects, def-weil-sheaf-of-modules-category.

5. For an abelian map $\alpha:L_{\rm Ab}M\to N$, put $\beta=R_{\rm Ab}(\alpha)\eta_M$.
   Naturality of the abelian adjunction bijection gives $\operatorname{adj}(\alpha\circ
   L\lambda_a)=\beta\circ\lambda_a$ and
   $\operatorname{adj}(\lambda_a\circ\alpha)=R\lambda_a\circ\beta$. Its injectivity therefore
   says that $\alpha$ commutes with every constant scalar if and only if $\beta$ does. A natural
   abelian map between constant-ring module sheaves commuting with the constant scalars commutes
   with every scalar section: represent that section by constants on a cover using the new
   sheafification comparison and the local-section theorem, use naturality and constant-scalar
   linearity there, and glue the equality. This applies on both sites, so the abelian hom
   bijection restricts to module maps, with the same inverse. It gives $f^*_{\Lambda}\dashv
   f_{*,\Lambda}$; its unit is the image of the identity under this restricted bijection, hence
   has underlying map $\eta_M$. Thus $Vf^*_{\Lambda}\cong L_{\rm Ab}V$ is natural and carries
   the module unit to the abelian unit.
   Uses: lem-weil-pbc-adjunction-lifts-abelian-group-objects, lem-pe-ring-sheafification-
   underlying-sets, lem-weil-pbc-site-sheafification-sections-local, def-weil-sheaf-of-modules-
   category.

6. We prove exactness for the given geometric morphism, without assuming a presenting continuous
   functor between these particular sites. Kernels of abelian-sheaf maps are sectionwise kernels
   and their underlying sets are equalizers of the given map and zero. The finite-limit-
   preserving $L$ sends this equalizer and its transported group operations to the kernel of the
   transported map. Hence $L_{\rm Ab}$ preserves kernels. It preserves cokernels because it is a
   left adjoint, by the preceding abelian adjunction and preservation of colimits. It is
   additive: addition of maps is addition on the target composed with their pair, and both
   addition and the product pairing are transported by $L$. Thus $L_{\rm Ab}$ is exact. The
   forgetful module functor is faithful and preserves kernels and cokernels, and its statement
   identifies them with those in abelian sheaves. Since $Vf^*_{\Lambda}=L_{\rm Ab}V$, a sequence
   and its module inverse image have the corresponding abelian exact sequences. Faithfulness
   detects the vanishing of the kernel/image quotient. Therefore $f^*_{\Lambda}$ is additive and
   exact.
   Uses: lem-weil-pbc-sheafification-exact, lem-weil-pbc-site-sheaf-sets-limits-sectionwise,
   lem-weil-pbc-left-adjoint-preserves-colimits, lem-weil-pbc-module-sheaves-colimits-forgetful.

7. For composable geometric morphisms, take the canonical direct-image comparison and the
   composite adjunction. The composite unit is $\eta^{gf}_M=g_*(\eta^f_{g^{-1}M})\circ\eta^g_M$,
   with the appropriate direct-image identification. The conjugate-isomorphism lemma
   characterizes the inverse-image comparison as the unique map satisfying its unit equation.
   Applying this lemma first to abelian and then to module adjunctions gives the same underlying
   comparison, since step 5 identifies their hom bijections and units. In particular it commutes
   with scalar maps and gives the natural module comparison. The coefficient-ring comparisons
   also agree: the two possible maps on the constant ring agree on every terminal-sheaf scalar
   summand of step 1, hence agree. For three morphisms both parenthesized comparisons satisfy
   the same composite-unit equation, so uniqueness identifies them; the identity comparison
   follows from the identity adjunction. This proves the claimed composition coherence,
   including that for the forgotten units.
   Uses: def-weil-pbc-composite-adjunction, lem-weil-pbc-conjugate-iso-unit-equation.

8. For an object $U$ of $\mathcal C$, let $u:\mathcal C/U\to\mathcal C$ forget the structure
   map. It is continuous: a covering over $V/U$ is exactly an underlying covering of $V$, and
   base change of that covering along $W/U\to V/U$ has underlying objects $W\times_VV_i$ and
   structure maps to $U$. It is cocontinuous: any covering $\{V_i\to V\}$ of the underlying
   object of $V/U$ lifts to the covering $\{(V_i\to V\to U)\to(V\to U)\}$ with exactly the same
   image family. These verify the two hypotheses of the continuous-cocontinuous topos-adjunction
   theorem. Applying that theorem gives an adjunction $j_U^{-1}\dashv j_{U*}$ with
   $j_U^{-1}H(V/U)=H(V)$ and $j_U^{-1}$ preserving finite limits. Thus restriction on sets is
   indeed the inverse image of a geometric morphism, so the preceding construction applies to
   it. The slice remains small because its objects and morphisms are specified by objects and
   morphisms of the small site.
   Uses: def-pur-localized-ringed-site, def-weil-pbc-sites-and-cohomology, def-weil-pbc-special-
   cocontinuous-functor, lem-weil-pbc-continuous-cocontinuous-topos-adjunction.

9. For the localization geometric morphism established in step 8, its inverse image is
   sectionwise restriction. The localized-ringed-site definition gives the corresponding
   sectionwise ring and module operations. The restriction of the constant ring presheaf is the
   constant ring presheaf on $\mathcal C/U$, and the ring-sheafification-localization comparison
   identifies its sheafification with $\Lambda_{\mathcal C}|_U$, preserving the unit and thus
   each constant scalar. Consequently applying the construction to $j_U$ gives exactly
   restriction: its transported action is $a_{M,V}$ at $V/U$, and its underlying map on a
   morphism is that morphism at $V$. Apply step 7 to composites involving these localization
   inverse images. The coefficient identifications agree on constant sections, and the module
   comparisons are the uniquely unit-compatible comparisons. Hence the construction and its
   forgotten-unit comparison commute with restriction whenever the inverse-image composite is
   restricted to localized sites. This asserts compatibility of the canonical
   localization/composition comparisons; it does not identify unrelated site objects on the two
   sites.
   Uses: def-pur-localized-ringed-site, lem-pur-ring-presheaf-sheafification-localization.

10. Apply the exact-functor-derived-factorization theorem to the exact additive functor of step
   6 between the abelian module-sheaf categories. It sends quasi-isomorphisms of complexes to
   quasi-isomorphisms, so termwise application induces the derived inverse image, with its
   canonical termwise comparison and triangulated structure. The bounded-below theorem gives
   $H^r(f^*_{\Lambda}K)\cong f^*_{\Lambda}H^r(K)$ and hence preservation of every lower
   cohomological bound. Restricting therefore gives the functor on $D^+$. All comparisons
   already constructed are natural chain maps when applied degreewise, so they survive
   localization at quasi-isomorphisms with their same equations.
   Uses: lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-exact-functor-bounded-
   below, def-weil-abstract-derived-category, def-weil-pbc-bounded-derived-subcategories. -/
theorem constant_left_module_inverse_image
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L) :
    Nonempty (ConstantLeftModuleInverseImageData.{u, w} J K Λ L R adj hL) := by
  sorry

end CategoryTheory
