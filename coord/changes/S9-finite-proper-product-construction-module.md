# WeilConjectures.FiniteProperProduct construction module

## Reason

Repair of returned head `1cd1c0d5045` (reviewer C-1cd1c): this record is
delivered at `coord/changes/S9-finite-proper-product-construction-module.md`.
The stage-3 landing override name for it is
`S9-finite-proper-product-construction-module.change.md`, as required by
`tools/batch_land.py:fixes`. The basename ending only in `.md` is not an
accepted `--apply-fixes` entry; using it caused the previous landing refusal.
The record is included directly in this repaired packet. Any further reviewer
correction must use the `.change.md` override name rather than the repository
basename. This changes delivery metadata only.

The assigned theorem must use ordinaryDerivedProductLegTransposes, but that module
publicly imports the assigned theorem's module for its construction definitions.
Adding the required reverse import produces an import cycle. Extract all existing
construction declarations into FiniteProperProductMaps and publicly reexport them
from the original module. The leg module imports the construction module instead.
Its declarations, attributes, signatures and visibility remain identical.

The tensor, pull and push aliases become semireducible definitions with exactly
their existing bodies. This permits local irreducibility in the proof so Lean does
not repeatedly expand the concrete derived tensor and functors. No mathematical
object or equation changes. Explicit return types are supplied for tensor, pull,
push, external, v, w and omega, with their same intended functor or morphism types;
their bodies are unchanged. pairEvaluation also has its explicit morphism type.
These annotations keep proof specializations from comparing inferred model details.
All other existing construction bodies are unchanged.
The added pairEvaluation and swapStructure name displayed maps. swapPull uses
objectwiseComparison, the objectwise presentation of equality transport followed
by the same compositor; objectwiseComparison_naturality is proved by equality
elimination and naturality. This exposes the existing canonical component without
forcing the kernel to expand the concrete derived functors while comparing casts.
Targets retain the same objects and statements; semantic review should verify the
identical moved construction bodies and the three alias bodies.

## Old

```lean
variable (P : PurityFiniteSetting.{u})

/-- The existing positive-level coefficient ring, with index level-1.
Source: purity conventions (blueprint: lem-pur-finite-proper-product-transpose). -/
abbrev A := finiteCoefficientRing P.coefficients.l P.extension (P.level - 1 + 1)

/-- The recorded ordinary unbounded category, at the positive coefficient level.
Source: purity conventions (blueprint: lem-pur-finite-proper-product-transpose). -/
abbrev D (X : Scheme.{u}) := proEtaleDerivedCategory X (A P)

/-- The recorded intrinsic tensor bifunctor, with its K-flat normalization.
Source: Stacks 07A4 (blueprint: lem-pur-finite-proper-product-transpose). -/
abbrev tensor (X : Scheme.{u}) :=
  finiteIntrinsicDerivedTensor P.coefficients.l P.extension X (P.level - 1)

/-- The recorded exact inverse image on the whole unbounded category.
Source: Stacks 0735 (blueprint: lem-pur-finite-proper-product-transpose). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  finiteDerivedPullback P.coefficients.l P.extension (P.level - 1) f

/-- Ordinary K-injective direct image on the intrinsic coefficient category.
Source: Stacks 07A5 (blueprint: lem-pur-finite-proper-product-transpose). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleConstantDerivedDirectImage f (A P)

/-- The normalized ordinary inverse-image/direct-image derived adjunction.
Source: Stacks 07A6 (blueprint: lem-pur-finite-proper-product-transpose). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : pull P f ⊣ push P f :=
  letI := pullbackTensorCoefficientFinite P.coefficients.l P.extension (P.level - 1)
  (sfIntrinsicConstantModuleAdjunction f (A P)).mapDerivedCategoryRightDerivedAdjunction

/-- The existing normalized composition of intrinsic inverse images.
Source: Stacks 0D6D (blueprint: lem-pur-finite-proper-product-transpose). -/
def comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull P (f ≫ g) ≅ pull P g ⋙ pull P f :=
  letI := pullbackTensorCoefficientFinite P.coefficients.l P.extension (P.level - 1)
  sfIntrinsicDerivedPullbackComp (A P) f g

/-- The signed symmetry fixed on K-flat homogeneous tensors by the Koszul rule.
Source: Stacks 06YS (blueprint: lem-pur-finite-proper-product-transpose). -/
def sigma (X : Scheme.{u}) (M N : D P X) :
    (tensor P X).obj (M,N) ≅ (tensor P X).obj (N,M) :=
  (pullbackTensorBraiding (ProEt.topology X)
    (integralCoefficientCommRingSheaf P.coefficients.l P.extension X (P.level - 1))
    (finiteIntrinsicClosed P.coefficients.l P.extension X (P.level - 1))
    (finiteIntrinsicTensorModels P.coefficients.l P.extension X (P.level - 1))).app (M,N)

/-- The source-implied inverse of ell in a residue field; no new assumption is made.
Source: purity conventions, ell distinct from p
(blueprint: lem-pur-finite-proper-product-transpose). -/
@[instance_reducible]
def residueInverse (X : Scheme.{u}) (s : X ⟶ Spec (.of P.field.k)) (x : X) :
    Invertible (P.coefficients.l : X.residueField x) :=
  (show IsUnit (P.coefficients.l : X.residueField x) by
    simpa only [map_natCast] using
      (P.coefficientPrime_isUnit_stalk X s x).map
        (IsLocalRing.residue (X.presheaf.stalk x))).invertible

/-- The canonical tensor comparison of the recorded pullback, with inherited units.
Source: Stacks 07A4 (blueprint: lem-pur-finite-proper-product-transpose). -/
def mu {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : X ⟶ Spec (.of P.field.k)) (sY : Y ⟶ Spec (.of P.field.k))
    (M N : D P Y) :
    (pull P f).obj ((tensor P Y).obj (M,N)) ≅
      (tensor P X).obj ((pull P f).obj M, (pull P f).obj N) :=
  @canonicalFinitePullbackTensor P.coefficients.l _ P.extension _ _ _ X Y f
    (P.level - 1) (residueInverse P X sX) (residueInverse P Y sY) M N

/-- The specified canonical equivalence with fixed-scalar sheaves.
Source: Stacks 00YV (blueprint: lem-pur-finite-proper-product-transpose). -/
def realization (X : Scheme.{u}) :=
  letI := pullbackTensorCoefficientFinite P.coefficients.l P.extension (P.level - 1)
  sfIntrinsicDerivedEquivalence X (A P)

/-- The normalized change to fixed-scalar direct image, on K-injective representatives.
Source: Stacks 07A5 (blueprint: lem-pur-finite-proper-product-transpose). -/
def pushModel {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push P f ≅ (realization P X).inverse ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (A P))) f).rightDerivedFunctor ⋙
        (realization P Y).functor :=
  letI := pullbackTensorCoefficientFinite P.coefficients.l P.extension (P.level - 1)
  ((realization P X).invFunIdAssoc (push P f)).symm ≪≫
    isoWhiskerLeft (realization P X).inverse (sfIntrinsicDerivedDirectImageComparison f (A P))

/-- Iterated direct image in fixed-scalar coordinates, inserting only realization units.
Source: Stacks 00YV, 0D6E (blueprint: lem-pur-finite-proper-product-transpose). -/
def iteratedPushModel {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push P f ⋙ push P g ≅ (realization P X).inverse ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (A P))) f).rightDerivedFunctor ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (A P))) g).rightDerivedFunctor ⋙
        (realization P Z).functor :=
  isoWhiskerRight (pushModel P f) (push P g) ≪≫
    (associator _ _ _ ) ≪≫
    isoWhiskerLeft (realization P X).inverse
      (associator _ _ _ ≪≫
        isoWhiskerLeft _ (isoWhiskerLeft (realization P Y).functor (pushModel P g)) ≪≫
        isoWhiskerLeft _ ((realization P Y).funInvIdAssoc _))

/-- Exactly the recorded finite direct-image compositor in intrinsic coordinates.
It is transported through the existing section/K-injective-normalized equivalences.
Source: Stacks 0D6E (blueprint: lem-pur-finite-proper-product-transpose). -/
def kappa {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push P (f ≫ g) ≅ push P f ⋙ push P g :=
  pushModel P (f ≫ g) ≪≫
    isoWhiskerLeft (realization P X).inverse
      (isoWhiskerRight (ProEtale.finiteDirectImageComposition
        (ULift.{u + 1} (A P)) f g) (realization P Z).functor ≪≫ associator _ _ _) ≪≫
    (iteratedPushModel P f g).symm

/-- The specified square pullback comparison, in the direction used by exchange.
Source: Stacks 0E48 (blueprint: lem-pur-finite-proper-product-transpose). -/
def theta {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B) :
    pull P b ⋙ pull P (pullback.snd a b) ≅ pull P a ⋙ pull P (pullback.fst a b) :=
  (comp P (pullback.snd a b) b).symm ≪≫
    eqToIso (congrArg (pull P) (pullback.condition (f := a) (g := b)).symm) ≪≫
    comp P (pullback.fst a b) a

/-- The ordinary counit-defined exchange, specialized to this fibre-product square.
Source: def-exchange-projection and Stacks 0E48
(blueprint: lem-pur-finite-proper-product-transpose). -/
def exchange {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B) (H : D P Y) :
    (pull P b).obj ((push P a).obj H) ⟶
      (push P (pullback.snd a b)).obj ((pull P (pullback.fst a b)).obj H) :=
  (mateEquiv (adj P a) (adj P (pullback.snd a b))
    (TwoSquare.mk _ _ _ _ (theta P a b).hom)).natTrans.app H

/-- The component of the counit-defined ordinary projection map, without invertibility.
This is precisely the inverse Hom bijection on mu followed by epsilon tensor identity.
Source: def-exchange-projection; Stacks projection-formula-map preceding 0E48
(blueprint: lem-pur-finite-proper-product-transpose). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : X ⟶ Spec (.of P.field.k)) (sY : Y ⟶ Spec (.of P.field.k))
    (M : D P X) (N : D P Y) :
    (tensor P Y).obj ((push P f).obj M,N) ⟶
      (push P f).obj ((tensor P X).obj (M,(pull P f).obj N)) :=
  (adj P f).homEquiv _ _
    ((mu P f sX sY _ N).hom ≫
      (tensor P X).map (Prod.mkHom ((adj P f).counit.app M) (𝟙 _)))

/-- The external tensor object E on the actual fibre product.
Source: node's first display (blueprint: lem-pur-finite-proper-product-transpose). -/
abbrev external {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (H : D P Y) (J : D P Z) :=
  (tensor P (pullback a b)).obj
    ((pull P (pullback.fst a b)).obj H, (pull P (pullback.snd a b)).obj J)

/-- The displayed map v: exchange tensor identity followed by projection along t.
Source: Stacks 0E48, node display (blueprint: lem-pur-finite-proper-product-transpose). -/
def v {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sZ : Z ⟶ Spec (.of P.field.k)) (H : D P Y) (J : D P Z) :=
  (tensor P Z).map (Prod.mkHom (exchange P a b H) (𝟙 J)) ≫
    projection P (pullback.snd a b) (pullback.snd a b ≫ sZ) sZ
      ((pull P (pullback.fst a b)).obj H) J

/-- The displayed map w, retaining both signed symmetries.
Source: Stacks 0E48, node display (blueprint: lem-pur-finite-proper-product-transpose). -/
def w {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sB : B ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) :=
  (sigma P B ((push P a).obj H) ((push P b).obj J)).hom ≫
    projection P b sZ sB J ((push P a).obj H) ≫
    (push P b).map ((sigma P Z J ((pull P b).obj ((push P a).obj H))).hom)

/-- The specified forward product, using the recorded direct-image compositor.
Source: Stacks 0E48, node display (blueprint: lem-pur-finite-proper-product-transpose). -/
def omega {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sB : B ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) :=
  w P a b sB sZ H J ≫ (push P b).map (v P a b sZ H J) ≫
    (kappa P (pullback.snd a b) b).inv.app (external P a b H J)


/-- Pull back the swapped external tensor and apply the signed interchange.
The two component identifications are the canonical pullback compositors and the
projection equations for the actual fibre-product swap.
Source: Stacks 0E48, node swap paragraph
(blueprint: lem-pur-finite-proper-product-transpose). -/
def swapTensor {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sY : Y ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) :
    (pull P (pullbackSymmetry a b).hom).obj (external P b a J H) ⟶ external P a b H J :=
  (mu P (pullbackSymmetry a b).hom (pullback.snd a b ≫ sZ)
    (pullback.snd b a ≫ sY) _ _).hom ≫
  (tensor P (pullback a b)).map
    (Prod.mkHom
      ((comp P (pullbackSymmetry a b).hom (pullback.fst b a)).inv.app J ≫
        (eqToIso (congrArg (fun f ↦ (pull P f).obj J)
          (pullbackSymmetry_hom_comp_fst a b))).hom)
      ((comp P (pullbackSymmetry a b).hom (pullback.snd b a)).inv.app H ≫
        (eqToIso (congrArg (fun f ↦ (pull P f).obj H)
          (pullbackSymmetry_hom_comp_snd a b))).hom)) ≫
  (sigma P (pullback a b) ((pull P (pullback.snd a b)).obj J)
    ((pull P (pullback.fst a b)).obj H)).hom

/-- Transport along the actual swap, using its unit and the same direct-image compositor,
then the signed tensor interchange. This is the specified S_{a,b}, with no arbitrary map.
Source: Stacks 0E48, node proof Step 6
(blueprint: lem-pur-finite-proper-product-transpose). -/
def swapPush {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sY : Y ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) :
    (push P (pullback.snd b a ≫ a)).obj (external P b a J H) ⟶
      (push P (pullback.snd a b ≫ b)).obj (external P a b H J) :=
  (push P (pullback.snd b a ≫ a)).map
    ((adj P (pullbackSymmetry a b).hom).unit.app (external P b a J H)) ≫
  (kappa P (pullbackSymmetry a b).hom (pullback.snd b a ≫ a)).inv.app
    ((pull P (pullbackSymmetry a b).hom).obj (external P b a J H)) ≫
  (eqToIso (congrArg
    (fun f ↦ (push P f).obj
      ((pull P (pullbackSymmetry a b).hom).obj (external P b a J H)))
    ((Category.assoc (pullbackSymmetry a b).hom (pullback.snd b a) a).symm.trans
      ((congrArg (fun f ↦ f ≫ a) (pullbackSymmetry_hom_comp_snd a b)).trans
        (pullback.condition (f := a) (g := b)))))).hom ≫
  (push P (pullback.snd a b ≫ b)).map (swapTensor P a b sY sZ H J)
```

The leg module imports `Sheaf.Paper.FiniteProperProductTranspose` publicly.

## New

The following identical constructions are in the new public construction module:

```lean
variable (P : PurityFiniteSetting.{u})

/-- The existing positive-level coefficient ring, with index level-1.
Source: purity conventions (blueprint: def-pur-finite-proper-product-maps). -/
abbrev A := finiteCoefficientRing P.coefficients.l P.extension (P.level - 1 + 1)

/-- The recorded ordinary unbounded category, at the positive coefficient level.
Source: purity conventions (blueprint: def-pur-finite-proper-product-maps). -/
abbrev D (X : Scheme.{u}) := proEtaleDerivedCategory X (A P)

/-- The recorded intrinsic tensor bifunctor, with its K-flat normalization.
Source: Stacks 07A4 (blueprint: def-pur-finite-proper-product-maps). -/
def tensor (X : Scheme.{u}) : D P X × D P X ⥤ D P X :=
  finiteIntrinsicDerivedTensor P.coefficients.l P.extension X (P.level - 1)

/-- The recorded exact inverse image on the whole unbounded category.
Source: Stacks 0735 (blueprint: def-pur-finite-proper-product-maps). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) : D P Y ⥤ D P X :=
  finiteDerivedPullback P.coefficients.l P.extension (P.level - 1) f

/-- Ordinary K-injective direct image on the intrinsic coefficient category.
Source: Stacks 07A5 (blueprint: def-pur-finite-proper-product-maps). -/
def push {X Y : Scheme.{u}} (f : X ⟶ Y) : D P X ⥤ D P Y :=
  proEtaleConstantDerivedDirectImage f (A P)

/-- The normalized ordinary inverse-image/direct-image derived adjunction.
Source: Stacks 07A6 (blueprint: def-pur-finite-proper-product-maps). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : pull P f ⊣ push P f :=
  letI := pullbackTensorCoefficientFinite P.coefficients.l P.extension (P.level - 1)
  (sfIntrinsicConstantModuleAdjunction f (A P)).mapDerivedCategoryRightDerivedAdjunction

/-- The existing normalized composition of intrinsic inverse images.
Source: Stacks 0D6D (blueprint: def-pur-finite-proper-product-maps). -/
def comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull P (f ≫ g) ≅ pull P g ⋙ pull P f :=
  letI := pullbackTensorCoefficientFinite P.coefficients.l P.extension (P.level - 1)
  sfIntrinsicDerivedPullbackComp (A P) f g

/-- The signed symmetry fixed on K-flat homogeneous tensors by the Koszul rule.
Source: Stacks 06YS (blueprint: def-pur-finite-proper-product-maps). -/
def sigma (X : Scheme.{u}) (M N : D P X) :
    (tensor P X).obj (M,N) ≅ (tensor P X).obj (N,M) :=
  (pullbackTensorBraiding (ProEt.topology X)
    (integralCoefficientCommRingSheaf P.coefficients.l P.extension X (P.level - 1))
    (finiteIntrinsicClosed P.coefficients.l P.extension X (P.level - 1))
    (finiteIntrinsicTensorModels P.coefficients.l P.extension X (P.level - 1))).app (M,N)

/-- The source-implied inverse of ell in a residue field; no new assumption is made.
Source: purity conventions, ell distinct from p
(blueprint: def-pur-finite-proper-product-maps). -/
@[instance_reducible]
def residueInverse (X : Scheme.{u}) (s : X ⟶ Spec (.of P.field.k)) (x : X) :
    Invertible (P.coefficients.l : X.residueField x) :=
  (show IsUnit (P.coefficients.l : X.residueField x) by
    simpa only [map_natCast] using
      (P.coefficientPrime_isUnit_stalk X s x).map
        (IsLocalRing.residue (X.presheaf.stalk x))).invertible

/-- The canonical tensor comparison of the recorded pullback, with inherited units.
Source: Stacks 07A4 (blueprint: def-pur-finite-proper-product-maps). -/
def mu {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : X ⟶ Spec (.of P.field.k)) (sY : Y ⟶ Spec (.of P.field.k))
    (M N : D P Y) :
    (pull P f).obj ((tensor P Y).obj (M,N)) ≅
      (tensor P X).obj ((pull P f).obj M, (pull P f).obj N) :=
  @canonicalFinitePullbackTensor P.coefficients.l _ P.extension _ _ _ X Y f
    (P.level - 1) (residueInverse P X sX) (residueInverse P Y sY) M N

/-- The specified canonical equivalence with fixed-scalar sheaves.
Source: Stacks 00YV (blueprint: def-pur-finite-proper-product-maps). -/
def realization (X : Scheme.{u}) :=
  letI := pullbackTensorCoefficientFinite P.coefficients.l P.extension (P.level - 1)
  sfIntrinsicDerivedEquivalence X (A P)

/-- The normalized change to fixed-scalar direct image, on K-injective representatives.
Source: Stacks 07A5 (blueprint: def-pur-finite-proper-product-maps). -/
def pushModel {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push P f ≅ (realization P X).inverse ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (A P))) f).rightDerivedFunctor ⋙
        (realization P Y).functor :=
  letI := pullbackTensorCoefficientFinite P.coefficients.l P.extension (P.level - 1)
  ((realization P X).invFunIdAssoc (push P f)).symm ≪≫
    isoWhiskerLeft (realization P X).inverse (sfIntrinsicDerivedDirectImageComparison f (A P))

/-- Iterated direct image in fixed-scalar coordinates, inserting only realization units.
Source: Stacks 00YV, 0D6E (blueprint: def-pur-finite-proper-product-maps). -/
def iteratedPushModel {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push P f ⋙ push P g ≅ (realization P X).inverse ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (A P))) f).rightDerivedFunctor ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (A P))) g).rightDerivedFunctor ⋙
        (realization P Z).functor :=
  isoWhiskerRight (pushModel P f) (push P g) ≪≫
    (associator _ _ _ ) ≪≫
    isoWhiskerLeft (realization P X).inverse
      (associator _ _ _ ≪≫
        isoWhiskerLeft _ (isoWhiskerLeft (realization P Y).functor (pushModel P g)) ≪≫
        isoWhiskerLeft _ ((realization P Y).funInvIdAssoc _))

/-- Exactly the recorded finite direct-image compositor in intrinsic coordinates.
It is transported through the existing section/K-injective-normalized equivalences.
Source: Stacks 0D6E (blueprint: def-pur-finite-proper-product-maps). -/
def kappa {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    push P (f ≫ g) ≅ push P f ⋙ push P g :=
  pushModel P (f ≫ g) ≪≫
    isoWhiskerLeft (realization P X).inverse
      (isoWhiskerRight (ProEtale.finiteDirectImageComposition
        (ULift.{u + 1} (A P)) f g) (realization P Z).functor ≪≫ associator _ _ _) ≪≫
    (iteratedPushModel P f g).symm

/-- The specified square pullback comparison, in the direction used by exchange.
Source: Stacks 0E48 (blueprint: def-pur-finite-proper-product-maps). -/
def theta {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B) :
    pull P b ⋙ pull P (pullback.snd a b) ≅ pull P a ⋙ pull P (pullback.fst a b) :=
  (comp P (pullback.snd a b) b).symm ≪≫
    eqToIso (congrArg (pull P) (pullback.condition (f := a) (g := b)).symm) ≪≫
    comp P (pullback.fst a b) a

/-- The ordinary counit-defined exchange, specialized to this fibre-product square.
Source: def-exchange-projection and Stacks 0E48
(blueprint: def-pur-finite-proper-product-maps). -/
def exchange {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B) (H : D P Y) :
    (pull P b).obj ((push P a).obj H) ⟶
      (push P (pullback.snd a b)).obj ((pull P (pullback.fst a b)).obj H) :=
  (mateEquiv (adj P a) (adj P (pullback.snd a b))
    (TwoSquare.mk _ _ _ _ (theta P a b).hom)).natTrans.app H

/-- The component of the counit-defined ordinary projection map, without invertibility.
This is precisely the inverse Hom bijection on mu followed by epsilon tensor identity.
Source: def-exchange-projection; Stacks projection-formula-map preceding 0E48
(blueprint: def-pur-finite-proper-product-maps). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : X ⟶ Spec (.of P.field.k)) (sY : Y ⟶ Spec (.of P.field.k))
    (M : D P X) (N : D P Y) :
    (tensor P Y).obj ((push P f).obj M,N) ⟶
      (push P f).obj ((tensor P X).obj (M,(pull P f).obj N)) :=
  (adj P f).homEquiv _ _
    ((mu P f sX sY _ N).hom ≫
      (tensor P X).map (Prod.mkHom ((adj P f).counit.app M) (𝟙 _)))

/-- The external tensor object E on the actual fibre product.
Source: node's first display (blueprint: def-pur-finite-proper-product-maps). -/
abbrev external {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (H : D P Y) (J : D P Z) : D P (pullback a b) :=
  (tensor P (pullback a b)).obj
    ((pull P (pullback.fst a b)).obj H, (pull P (pullback.snd a b)).obj J)

/-- The displayed map v: exchange tensor identity followed by projection along t.
Source: Stacks 0E48, node display (blueprint: def-pur-finite-proper-product-maps). -/
def v {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sZ : Z ⟶ Spec (.of P.field.k)) (H : D P Y) (J : D P Z) :
    (tensor P Z).obj ((pull P b).obj ((push P a).obj H), J) ⟶
      (push P (pullback.snd a b)).obj (external P a b H J) :=
  (tensor P Z).map (Prod.mkHom (exchange P a b H) (𝟙 J)) ≫
    projection P (pullback.snd a b) (pullback.snd a b ≫ sZ) sZ
      ((pull P (pullback.fst a b)).obj H) J

/-- The displayed map w, retaining both signed symmetries.
Source: Stacks 0E48, node display (blueprint: def-pur-finite-proper-product-maps). -/
def w {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sB : B ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) :
    (tensor P B).obj ((push P a).obj H, (push P b).obj J) ⟶
      (push P b).obj ((tensor P Z).obj ((pull P b).obj ((push P a).obj H), J)) :=
  (sigma P B ((push P a).obj H) ((push P b).obj J)).hom ≫
    projection P b sZ sB J ((push P a).obj H) ≫
    (push P b).map ((sigma P Z J ((pull P b).obj ((push P a).obj H))).hom)

/-- The specified forward product, using the recorded direct-image compositor.
Source: Stacks 0E48, node display (blueprint: def-pur-finite-proper-product-maps). -/
def omega {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sB : B ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) :
    (tensor P B).obj ((push P a).obj H, (push P b).obj J) ⟶
      (push P (pullback.snd a b ≫ b)).obj (external P a b H J) :=
  w P a b sB sZ H J ≫ (push P b).map (v P a b sZ H J) ≫
    (kappa P (pullback.snd a b) b).inv.app (external P a b H J)


/-- Pull back the swapped external tensor and apply the signed interchange.
The two component identifications are the canonical pullback compositors and the
projection equations for the actual fibre-product swap.
Source: Stacks 0E48, node swap paragraph
(blueprint: def-pur-finite-proper-product-maps). -/
def swapTensor {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sY : Y ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) :
    (pull P (pullbackSymmetry a b).hom).obj (external P b a J H) ⟶ external P a b H J :=
  (mu P (pullbackSymmetry a b).hom (pullback.snd a b ≫ sZ)
    (pullback.snd b a ≫ sY) _ _).hom ≫
  (tensor P (pullback a b)).map
    (Prod.mkHom
      ((comp P (pullbackSymmetry a b).hom (pullback.fst b a)).inv.app J ≫
        (eqToIso (congrArg (fun f ↦ (pull P f).obj J)
          (pullbackSymmetry_hom_comp_fst a b))).hom)
      ((comp P (pullbackSymmetry a b).hom (pullback.snd b a)).inv.app H ≫
        (eqToIso (congrArg (fun f ↦ (pull P f).obj H)
          (pullbackSymmetry_hom_comp_snd a b))).hom)) ≫
  (sigma P (pullback a b) ((pull P (pullback.snd a b)).obj J)
    ((pull P (pullback.fst a b)).obj H)).hom

/-- Transport along the actual swap, using its unit and the same direct-image compositor,
then the signed tensor interchange. This is the specified S_{a,b}, with no arbitrary map.
Source: Stacks 0E48, node proof Step 6
(blueprint: def-pur-finite-proper-product-maps). -/
def swapPush {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sY : Y ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (H : D P Y) (J : D P Z) :
    (push P (pullback.snd b a ≫ a)).obj (external P b a J H) ⟶
      (push P (pullback.snd a b ≫ b)).obj (external P a b H J) :=
  (push P (pullback.snd b a ≫ a)).map
    ((adj P (pullbackSymmetry a b).hom).unit.app (external P b a J H)) ≫
  (kappa P (pullbackSymmetry a b).hom (pullback.snd b a ≫ a)).inv.app
    ((pull P (pullbackSymmetry a b).hom).obj (external P b a J H)) ≫
  (eqToIso (congrArg
    (fun f ↦ (push P f).obj
      ((pull P (pullbackSymmetry a b).hom).obj (external P b a J H)))
    ((Category.assoc (pullbackSymmetry a b).hom (pullback.snd b a) a).symm.trans
      ((congrArg (fun f ↦ f ≫ a) (pullbackSymmetry_hom_comp_snd a b)).trans
        (pullback.condition (f := a) (g := b)))))).hom ≫
  (push P (pullback.snd a b ≫ b)).map (swapTensor P a b sY sZ H J)
```

The item publicly imports `Sheaf.Paper.FiniteProperProductMaps`. The leg module's
single changed line publicly imports `Sheaf.Paper.FiniteProperProductMaps`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteProperProductTranspose | S9 | Publicly reexports identical constructions; complete proof from named steps. |
| Sheaf.Paper.OrdinaryDerivedProductLegTransposes | A5 | Required one-line public-import adaptation to avoid the import cycle; signatures unchanged. |
| Sheaf.Paper.FiniteTripleProductDefinitions | unclaimed | Direct importer of the item; uses A, D, tensor and external through the public reexport; no source adaptation. Compiles unchanged against the new modules (reviewer, 2026-10-26). |
| Sheaf.Paper.FiniteProductOpenRestrictionPasting | unclaimed | Uses A, D and external through FiniteTripleProductDefinitions; no source adaptation; compiles unchanged. |
| Sheaf.Paper.FiniteProductOrdinaryNaturality | unclaimed | Uses A and D through FiniteTripleProductDefinitions; no source adaptation; compiles unchanged. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Uses A, D, tensor, external and v through its imports; no source adaptation; compiles unchanged. |

These are all the modules downstream of the item (the import closure in the library).
None needs a source change for tensor, pull and push becoming plain definitions with
explicit result types: each compiles unchanged against the delivered modules.
The leg module directly uses adj and the other constructions, with identical types.

## Status

landed 20261026T002706-L-108957 2026-10-26 (merge of deliver/S9/Sheaf.Paper.FiniteProperProductTranspose)
