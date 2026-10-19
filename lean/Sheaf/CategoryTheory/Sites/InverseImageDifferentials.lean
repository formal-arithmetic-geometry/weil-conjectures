/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.CategoryTheory.Sites.InverseImageFreeModule
import Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel

/-!
# Inverse image of sheaf differentials

Source: Stacks Project, Modules on Sites, Tags 08TP and 08TQ
(blueprint: lem-trf-topos-inverse-image-differentials).

The differential module is the actual sheafification of sectionwise differentials.
Algebraic inverse images use the recorded finite-product transport interface. Underlying
sets are lifted to the common value universe, exactly as in that interface.
-/

@[expose] public section

universe w uC vC uD vD uE vE

open CategoryTheory CategoryTheory.Limits PresheafOfModules
open PresheafOfModules.DifferentialsConstruction

namespace CategoryTheory.SheafDifferentials

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

/-- The ring sheaf viewed as a sheaf of rings without commutativity data.
Source: Stacks 08TP (blueprint: lem-trf-topos-inverse-image-differentials). -/
abbrev ring (B : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B

/-- Underlying sets in the value universe used by algebraic inverse image.
Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable abbrev sets (B : Sheaf J CommRingCat.{w}) : Sheaf J (Type w) :=
  (sheafCompose J (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B

/-- Forget a module sheaf to its lifted underlying set sheaf.
Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable abbrev moduleSets (B : Sheaf J CommRingCat.{w}) :
    ringedSiteModules.{w, w, vC, uC} (ring B) ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf (ring B) ⋙
    sheafCompose J (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})

/-- Sheafification of `U ↦ Ω[B(U)/A(U)]`, with its actual module action.
Source: Stacks 08TP (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable def omega {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B) :
    ringedSiteModules.{w, w, vC, uC} (ring B) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  (PresheafOfModules.sheafification (𝟙 (ring B).obj)).obj
    (relativeDifferentials' φ.hom)

/-- The sectionwise universal derivation followed by the sheafification unit.
Source: Stacks 08TP (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable def derivation {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B) :
    (omega φ).val.Derivation' φ.hom :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  (derivation' φ.hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj)).unit.app _)

/-- The universal derivation as a map of underlying set sheaves.
Source: Stacks 08TP (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable def d {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B) :
    sets B ⟶ (moduleSets B).obj (omega φ) where
  hom :=
    { app := fun U ↦ TypeCat.ofHom
        (fun (x : ULift.{w} (B.obj.obj U)) ↦ ULift.up ((derivation φ).d x.down))
      naturality := by
        intro U V r
        ext x
        exact congrArg ULift.up ((derivation φ).d_map r x.down) }

/-- The map on underlying ring sheaves induced by a ring map.
Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable abbrev setsMap {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B) :
    sets A ⟶ sets B :=
  (sheafCompose J (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map φ

/-- The derivation into the target differential module restricted along a ring square.
Source: Stacks 08TP, functoriality (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable def squareDerivation {A B A' B' : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (φ' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ φ' = φ ≫ b) :
    ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj
        (omega φ')).val.Derivation' φ.hom where
  d := fun {U} ↦ (derivation φ').d.comp (b.hom.app U).hom.toAddMonoidHom
  d_mul := by
    intro U x y
    change (derivation φ').d (b.hom.app U (x * y)) =
      (b.hom.app U x) • (derivation φ').d (b.hom.app U y) +
        (b.hom.app U y) • (derivation φ').d (b.hom.app U x)
    rw [map_mul]
    exact (derivation φ').d_mul _ _
  d_map := by
    intro U V r x
    have hb := ConcreteCategory.congr_hom (b.hom.naturality r) x
    change b.hom.app V (B.obj.map r x) = B'.obj.map r (b.hom.app U x) at hb
    change (derivation φ').d (b.hom.app V (B.obj.map r x)) =
      (omega φ').val.map r ((derivation φ').d (b.hom.app U x))
    rw [hb]
    exact (derivation φ').d_map r _
  d_app := by
    intro U x
    have hs := ConcreteCategory.congr_hom (congrArg (fun t ↦ t.hom.app U) h) x
    change φ'.hom.app U (a.hom.app U x) = b.hom.app U (φ.hom.app U x) at hs
    change (derivation φ').d (b.hom.app U (φ.hom.app U x)) = 0
    rw [← hs]
    exact PresheafOfModules.Derivation'.d_app (derivation φ') _

/-- Canonical map on differentials for a commutative ring square, obtained by the
sectionwise universal property and the module sheafification adjunction.
Source: Stacks 08TP (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable def squareMap {A B A' B' : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (φ' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ φ' = φ ≫ b) :
    omega φ ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj (omega φ') :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj)).homEquiv _ _).symm
    ((isUniversal' φ.hom).desc (squareDerivation φ φ' a b h))

/-- The canonical square map on underlying set sheaves.
Source: Stacks 08TP (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable def squareSetsMap {A B A' B' : Sheaf J CommRingCat.{w}}
    (φ : A ⟶ B) (φ' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ φ' = φ ≫ b) :
    (moduleSets B).obj (omega φ) ⟶ (moduleSets B').obj (omega φ') :=
  (moduleSets B).map (squareMap φ φ' a b h)

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {K : GrothendieckTopology D}

/-- Compatibility of the transported ring map with the inverse image of the original map.
Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials). -/
def RingMapCompatibility
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {A B : Sheaf J CommRingCat.{w}} {AI BI : Sheaf K CommRingCat.{w}}
    (φ : A ⟶ B) (ψ : AI ⟶ BI)
    (FA : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse A AI)
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) : Prop :=
  f.inverse.map (setsMap φ) ≫ F.ringUnderlying.hom = FA.ringUnderlying.hom ≫ setsMap ψ

/-- Underlying comparison after the canonical module inverse-image identification.
Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials). -/
noncomputable def comparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {A B : Sheaf J CommRingCat.{w}} {AI BI : Sheaf K CommRingCat.{w}}
    (φ : A ⟶ B) (ψ : AI ⟶ BI)
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (e : F.modules.obj (omega φ) ≅ omega ψ) :
    f.inverse.obj ((moduleSets B).obj (omega φ)) ⟶
      (moduleSets BI).obj (omega ψ) :=
  F.moduleUnderlying.inv.app (omega φ) ≫ (moduleSets BI).map e.hom

/-- Universal-derivation normalization of the differential comparison.
Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials). -/
def IsComparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {A B : Sheaf J CommRingCat.{w}} {AI BI : Sheaf K CommRingCat.{w}}
    (φ : A ⟶ B) (ψ : AI ⟶ BI)
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (e : F.modules.obj (omega φ) ≅ omega ψ) : Prop :=
  f.inverse.map (d φ) ≫ comparison f φ ψ F e = F.ringUnderlying.hom ≫ d ψ

/-- Inverse image preserves sheaf differentials, with its unique canonical normalization.
The inverse-image operations are the supplied finite-product transports, not extra
linearity or exactness assumptions. Source: Stacks 08TP and 08TQ
(blueprint: lem-trf-topos-inverse-image-differentials).

Proof: (1) 08TP presents omega as the cokernel of free-module additivity, Leibniz,
and base-ring relations (lem-trf-sheafified-module-differentials-cokernel).
(2) Geometric inverse image is exact and preserves the free modules and their generators
(lem-trf-geometric-inverse-image-exact, lem-trf-geometric-inverse-image-free-module).
(3) The transported relation map is therefore the target relation map. Its cokernel
isomorphism sends the inverse image of db to db. The same presentation says that this
normalization determines the map, and hence the isomorphism, uniquely.
(4) Functoriality on these generators gives the naturality and coherence statements below. -/
theorem inverseDifferentials_existsUnique
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {A B : Sheaf J CommRingCat.{w}} {AI BI : Sheaf K CommRingCat.{w}}
    (φ : A ⟶ B) (ψ : AI ⟶ BI)
    (FA : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse A AI)
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (h : RingMapCompatibility f φ ψ FA F) :
    ∃! e : F.modules.obj (omega φ) ≅ omega ψ, IsComparison f φ ψ F e := by
  sorry

/-- Naturality in a commutative square of sheaves of commutative rings.
Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials).
Proof: use the canonical square maps constructed from the sectionwise universal
properties and sheafification. Both composites send the inverse image of db to
d of the image of b. The relation-map cokernel uniqueness in 08TP makes them equal. -/
theorem inverseDifferentials_naturality
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {A B A' B' : Sheaf J CommRingCat.{w}}
    {AI BI AI' BI' : Sheaf K CommRingCat.{w}}
    (φ : A ⟶ B) (φ' : A' ⟶ B') (ψ : AI ⟶ BI) (ψ' : AI' ⟶ BI')
    (a : A ⟶ A') (b : B ⟶ B') (h : a ≫ φ' = φ ≫ b)
    (ai : AI ⟶ AI') (bi : BI ⟶ BI') (hi : ai ≫ ψ' = ψ ≫ bi)
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B' BI')
    (hb : f.inverse.map (setsMap b) ≫ F'.ringUnderlying.hom =
      F.ringUnderlying.hom ≫ setsMap bi)
    (e : F.modules.obj (omega φ) ≅ omega ψ)
    (e' : F'.modules.obj (omega φ') ≅ omega ψ')
    (he : IsComparison f φ ψ F e) (he' : IsComparison f φ' ψ' F' e') :
    f.inverse.map (squareSetsMap φ φ' a b h) ≫ comparison f φ' ψ' F' e' =
      comparison f φ ψ F e ≫ squareSetsMap ψ ψ' ai bi hi := by
  sorry

/-- The differential comparison for the identity inverse image is the identity after
its canonical underlying-module comparison. No equality of chosen module structures is
assumed. Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials).
Proof: the identity comparison fixes every universal differential. The 08TP relation
presentation shows that any normalized comparison fixes all sections, hence is identity. -/
theorem inverseDifferentials_identity
    {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B)
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uC, vC, w, w}
      (𝟭 (Sheaf J (Type w))) B B)
    (hB : F.ringUnderlying = Iso.refl (sets B))
    (e : F.modules.obj (omega φ) ≅ omega φ)
    (he : d φ ≫ F.moduleUnderlying.inv.app (omega φ) ≫ (moduleSets B).map e.hom = d φ) :
    F.moduleUnderlying.inv.app (omega φ) ≫ (moduleSets B).map e.hom =
      𝟙 ((moduleSets B).obj (omega φ)) := by
  sorry

variable {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {L : GrothendieckTopology E}

/-- Coherence for composite geometric morphisms, with the canonical inverse-image
comparisons on rings and modules explicitly retained.
Source: Stacks 08TQ (blueprint: lem-trf-topos-inverse-image-differentials).
Proof: exactness and the free-module comparison transport the same relation map under
successive inverse images and their composite. With the stated ring comparison both
arrows send the twice transported db to db. Cokernel uniqueness from 08TP identifies
them; this is precisely the composite inverse-image comparison on underlying modules. -/
theorem inverseDifferentials_composition
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (g : GeometricMorphism (Sheaf L (Type w)) (Sheaf K (Type w)))
    {A B : Sheaf J CommRingCat.{w}} {AI BI : Sheaf K CommRingCat.{w}}
    {AII BII : Sheaf L CommRingCat.{w}}
    (φ : A ⟶ B) (ψ : AI ⟶ BI) (χ : AII ⟶ BII)
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (G : SheafOfModules.AlgebraicInverseImageOfUniverses.{uD, vD, uE, vE, w, w}
      g.inverse BI BII)
    (H : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uE, vE, w, w}
      (g.comp f).inverse B BII)
    (hB : H.ringUnderlying.hom =
      g.inverse.map F.ringUnderlying.hom ≫ G.ringUnderlying.hom)
    (eF : F.modules.obj (omega φ) ≅ omega ψ)
    (eG : G.modules.obj (omega ψ) ≅ omega χ)
    (eH : H.modules.obj (omega φ) ≅ omega χ)
    (hF : IsComparison f φ ψ F eF) (hG : IsComparison g ψ χ G eG)
    (hH : IsComparison (g.comp f) φ χ H eH) :
    comparison (g.comp f) φ χ H eH =
      g.inverse.map (comparison f φ ψ F eF) ≫ comparison g ψ χ G eG := by
  sorry

end CategoryTheory.SheafDifferentials
