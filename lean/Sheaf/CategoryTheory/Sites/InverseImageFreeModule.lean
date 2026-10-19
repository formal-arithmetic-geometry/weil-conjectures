/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits

import Sheaf.CategoryTheory.GeometricModuleTransport

/-!
# Geometric inverse image of free module sheaves

Source: Stacks Project, Modules on Sites, Tags 04BL, 03CY, 03D3 and 08TQ
(blueprint: lem-trf-geometric-inverse-image-free-module).

The free module is module sheafification of the sectionwise free module, on an arbitrary
sheaf of generators. Algebraic inverse-image presentations record precisely the transported
operations. Underlying modules use the common value universe of that recorded interface.
-/

@[expose] public section

universe w wI uC vC uD vD uH vH

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SheafFreeModule

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

/-- Forget commutativity of the coefficient sheaf, using Mathlib's sheaf composition.
Source: Stacks 04BL (blueprint: lem-trf-geometric-inverse-image-free-module). -/
abbrev ring (B : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B

/-- Underlying set sheaves of modules, with the lift used by algebraic inverse image.
Source: Stacks 03D2 (blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable abbrev moduleSets (B : Sheaf J CommRingCat.{w}) :
    ringedSiteModules.{w, w, vC, uC} (ring B) ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf (ring B) ⋙
    sheafCompose J (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})

/-- Module sheafification of `U ↦ B(U)[E(U)]`. Mathlib's presheaf free functor sends
restrictions to the semilinear extension of `[s] ↦ [s|V]`, and its map on generator
sheaves is the sectionwise linear extension. Source: Stacks 04BL and 03CY
(blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def free (B : Sheaf J CommRingCat.{w}) :
    Sheaf J (Type w) ⥤ ringedSiteModules.{w, w, vC, uC} (ring B) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  sheafToPresheaf J (Type w) ⋙ PresheafOfModules.free (ring B).obj ⋙
    PresheafOfModules.sheafification (𝟙 (ring B).obj)

/-- The presheaf generator map followed by the abelian sheafification unit, before
lifting the underlying sets. Source: Stacks 04BL
(blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def generatorRaw (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    E ⟶ (SheafOfModules.toSheaf (ring B) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})).obj ((free B).obj E) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  { hom := PresheafOfModules.freeAdjunctionUnit (ring B).obj E.obj ≫
      Functor.whiskerRight
        (toSheafify J (PresheafOfModules.freeObj (R := (ring B).obj) E.obj).presheaf)
        (forget AddCommGrpCat.{w}) }

/-- The map `s ↦ [s]` into the underlying sheaf of the free module, with the harmless
`ULift` identification required by the recorded algebraic inverse-image interface.
Source: Stacks 04BL (blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def generator (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    E ⟶ (moduleSets B).obj ((free B).obj E) where
  hom := (generatorRaw B E).hom ≫ Functor.whiskerLeft
    (((free B).obj E).val.presheaf ⋙ forget AddCommGrpCat.{w}) uliftFunctorTrivial.inv

/-- Simultaneous coefficient and generator change: the sheafified linear extension of
`[s] ↦ [e(s)]`, semilinear along `b`. It is constructed by the two recorded adjunctions,
with target scalars restricted along `b`. Source: Stacks 04BL and 03CY
(blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def change {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    (free B).obj E ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj
        ((free B').obj E') :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj)).homEquiv _ _).symm
    (PresheafOfModules.freeObjDesc (e.hom ≫ (generatorRaw B' E').hom))

/-- The simultaneous change map on underlying lifted set sheaves.
Source: Stacks 04BL (blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def changeSets {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    (moduleSets B).obj ((free B).obj E) ⟶ (moduleSets B').obj ((free B').obj E') :=
  (moduleSets B).map (change b e)

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {K : GrothendieckTopology D}

/-- The underlying comparison with the canonical inverse-image identification retained.
Source: Stacks 08TQ (blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def comparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E)) :
    f.inverse.obj ((moduleSets B).obj ((free B).obj E)) ⟶
      (moduleSets BI).obj ((free BI).obj (f.inverse.obj E)) :=
  F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets BI).map p.hom

/-- Generator normalization of the comparison, an equality of sheaf maps and hence
valid on all generalized sections. Source: Stacks 08TQ
(blueprint: lem-trf-geometric-inverse-image-free-module). -/
def IsComparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E)) : Prop :=
  f.inverse.map (generator B E) ≫ comparison f F E p = generator BI (f.inverse.obj E)

/-- Inverse image preserves the free module sheaf on any sheaf of sets, with its uniquely
normalized isomorphism. Source: Stacks 04BL, 03CY, 03D3 and 08TQ
(blueprint: lem-trf-geometric-inverse-image-free-module).

Proof: first extend a map E → |M| sectionwise by summing coefficients times the images
of generators. The free presheaf universal property and module sheafification give
Hom_B(B[E], M) ≃ Hom(E, |M|). The geometric module transport adjunction of 03D3,
with coefficient map the identity on the transported ring, then gives
Hom_BI(F(B[E]), H) ≃ Hom_B(B[E], f_* H) ≃ Hom(E, f_* |H|) ≃ Hom(f⁻¹ E, |H|).
The transport normalization identifies this bijection with restriction to f⁻¹ of the
generator map. Thus source and target are free on f⁻¹ E with those generator maps.
Extend each generator map into the other free module. Their composites fix generators,
so freeness makes them identities. This gives the isomorphism; the same uniqueness
makes it the only generator-normalized isomorphism. -/
theorem inverseFreeModule_existsUnique
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w)) :
    ∃! p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E),
      IsComparison f F E p := by
  sorry

/-- Naturality in both generator sheaves and coefficient-ring maps, expressed on
underlying sheaves to retain semilinear coefficient changes. The compatibility hypothesis
only identifies the transported coefficient map. Source: Stacks 04BL and 08TQ
(blueprint: lem-trf-geometric-inverse-image-free-module).

Proof: both composites are semilinear along the same transported ring map. On f⁻¹ E
they both equal the target generator map after f⁻¹ e, by the two normalization equations
and the sectionwise definition of change. The transported free universal property
therefore identifies the two composites. Taking b and bi to be identities gives
naturality in E; taking e to be identity gives coefficient naturality. -/
theorem inverseFreeModule_naturality
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B' BI')
    (b : B ⟶ B') (bi : BI ⟶ BI')
    (hb : f.inverse.map ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map b) ≫ F'.ringUnderlying.hom =
      F.ringUnderlying.hom ≫ (sheafCompose K
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map bi)
    {E E' : Sheaf J (Type w)} (e : E ⟶ E')
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E))
    (p' : F'.modules.obj ((free B').obj E') ≅ (free BI').obj (f.inverse.obj E'))
    (hp : IsComparison f F E p) (hp' : IsComparison f F' E' p') :
    f.inverse.map (changeSets b e) ≫ comparison f F' E' p' =
      comparison f F E p ≫ changeSets bi (f.inverse.map e) := by
  sorry

/-- Finite-product compatibility on the generator sheaves, including the empty product.
Source: Stacks 08TQ (blueprint: lem-trf-geometric-inverse-image-free-module).

Proof: normalize the comparison at the product sheaf. The free functor applied to the
finite-product comparison carries [s] to [lambda(s)], by its sectionwise construction
and sheafification. Composing the normalization equation gives the asserted equality.
Left exactness makes lambda invertible; no product decomposition of free modules is used. -/
theorem inverseFreeModule_products
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    {I : Type wI} [Finite I] (E : I → Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj (∏ᶜ E)) ≅ (free BI).obj (f.inverse.obj (∏ᶜ E)))
    (hp : IsComparison f F (∏ᶜ E) p) :
    f.inverse.map (generator B (∏ᶜ E)) ≫ comparison f F (∏ᶜ E) p ≫
        (moduleSets BI).map ((free BI).map (piComparison f.inverse E)) =
      piComparison f.inverse E ≫ generator BI (∏ᶜ fun i ↦ f.inverse.obj (E i)) := by
  sorry

/-- The identity comparison is identity after its underlying-module identification.
The ring presentation is normalized to the identity, rather than requiring equality of
chosen module structures. Source: Stacks 08TQ
(blueprint: lem-trf-geometric-inverse-image-free-module).

Proof: both the normalized comparison and the identity fix the generator map. The free
universal property identifies them on the entire free sheaf. -/
theorem inverseFreeModule_identity
    (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w))
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uC, vC, w, w}
      (𝟭 (Sheaf J (Type w))) B B)
    (hB : F.ringUnderlying = Iso.refl ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B))
    (p : F.modules.obj ((free B).obj E) ≅ (free B).obj E)
    (hp : generator B E ≫ F.moduleUnderlying.inv.app ((free B).obj E) ≫
      (moduleSets B).map p.hom = generator B E) :
    F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets B).map p.hom =
      𝟙 ((moduleSets B).obj ((free B).obj E)) := by
  sorry

variable {H : Type uH} [Category.{vH} H] [EssentiallySmall.{w} H]
  {T : GrothendieckTopology H}

/-- Composition coherence with the actual composite inverse image and ring comparison.
Source: Stacks 08TQ (blueprint: lem-trf-geometric-inverse-image-free-module).

Proof: the comparison for the composite sends the twice transported generator to the
target generator. Applying g⁻¹ to the first normalization equation and then using the
second proves that the successive comparisons have the same effect. The compatibility
of the ring presentations makes both maps linear over the same target ring. The free
universal property for the composite identifies them, with the underlying-module
comparisons retained explicitly as in the equation. -/
theorem inverseFreeModule_composition
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (g : GeometricMorphism (Sheaf T (Type w)) (Sheaf K (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    {BII : Sheaf T CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (G : SheafOfModules.AlgebraicInverseImageOfUniverses.{uD, vD, uH, vH, w, w}
      g.inverse BI BII)
    (FG : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uH, vH, w, w}
      (g.comp f).inverse B BII)
    (hB : FG.ringUnderlying.hom =
      g.inverse.map F.ringUnderlying.hom ≫ G.ringUnderlying.hom)
    (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E))
    (q : G.modules.obj ((free BI).obj (f.inverse.obj E)) ≅
      (free BII).obj (g.inverse.obj (f.inverse.obj E)))
    (r : FG.modules.obj ((free B).obj E) ≅
      (free BII).obj ((g.comp f).inverse.obj E))
    (hp : IsComparison f F E p) (hq : IsComparison g G (f.inverse.obj E) q)
    (hr : IsComparison (g.comp f) FG E r) :
    comparison (g.comp f) FG E r =
      g.inverse.map (comparison f F E p) ≫ comparison g G (f.inverse.obj E) q := by
  sorry

end CategoryTheory.SheafFreeModule
