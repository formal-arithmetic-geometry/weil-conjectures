/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.IntegralFinitePullbackComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Canonical maps in the ordinary finite proper external product

Source: Stacks Project, sites-cohomology.tex, Tag 0E48 and the preceding
projection-formula-map; Tag 0D6E. The explicit seven-step counit calculation is
lem-pur-finite-proper-product-transpose, refining the symmetry paragraph of
blueprint main-20261015, lem-sf-kunneth-coherence.proof.md.
(blueprint: def-pur-finite-proper-product-maps).

All operations are the recorded ordinary unbounded intrinsic finite operations.
The helpers specialize canonical constructions and name the maps displayed in the node.
The index level-1 uses the existing positive-level API, whose exponent is index+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteProperProduct

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

/-- The common tensor of two evaluation maps, with all pullback comparisons retained.
This is a construction for arbitrary arrows, independent of exchange and projection.
Source: Stacks Tag 0E48, two-counit calculation
(blueprint: def-pur-finite-proper-product-maps). -/
def pairEvaluation {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sB : B ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (F G : D P B) (H : D P Y) (J : D P Z)
    (e : (pull P a).obj F ⟶ H) (d : (pull P b).obj G ⟶ J) :
    (pull P (pullback.snd a b ≫ b)).obj ((tensor P B).obj (F, G)) ⟶
      external P a b H J :=
  (mu P (pullback.snd a b ≫ b) (pullback.snd a b ≫ sZ) sB F G).hom ≫
    (tensor P (pullback a b)).map (Prod.mkHom
      ((eqToIso (congrArg (fun f ↦ (pull P f).obj F)
        (pullback.condition (f := a) (g := b)).symm)).hom ≫
          (comp P (pullback.fst a b) a).hom.app F ≫
          (pull P (pullback.fst a b)).map e)
      ((comp P (pullback.snd a b) b).hom.app G ≫
          (pull P (pullback.snd a b)).map d))

/-- The equality of structure maps for the actual pullback swap.
Source: the pullback projection equations, Stacks Tag 001U
(blueprint: def-pur-finite-proper-product-maps). -/
theorem swapStructure {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B) :
    (pullbackSymmetry a b).hom ≫ (pullback.snd b a ≫ a) = pullback.snd a b ≫ b :=
  ((Category.assoc (pullbackSymmetry a b).hom (pullback.snd b a) a).symm.trans
    ((congrArg (fun f ↦ f ≫ a) (pullbackSymmetry_hom_comp_snd a b)).trans
      (pullback.condition (f := a) (g := b))))

/-- Naturality of an objectwise equality comparison followed by a natural isomorphism.
Source: equality elimination and naturality
(blueprint: def-pur-finite-proper-product-maps). -/
theorem objectwiseComparison_naturality
    {C E : Type*} [Category* C] [Category* E] {F G K : C ⥤ E}
    (h : F = G) (e : G ≅ K) {M N : C} (m : M ⟶ N) :
    F.map m ≫ ((eqToIso (congrArg (fun L : C ⥤ E ↦ L.obj N) h)).hom ≫
      (e.app N).hom) =
    ((eqToIso (congrArg (fun L : C ⥤ E ↦ L.obj M) h)).hom ≫
      (e.app M).hom) ≫ K.map m := by
  subst h
  simpa only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Iso.app_hom] using
    e.hom.naturality m

/-- An equality comparison with explicit object components, followed by e.
Source: equality elimination and natural-isomorphism composition
(blueprint: def-pur-finite-proper-product-maps). -/
def objectwiseComparison
    {C E : Type*} [Category* C] [Category* E] {F G K : C ⥤ E}
    (h : F = G) (e : G ≅ K) : F ≅ K :=
  NatIso.ofComponents
    (fun M ↦ eqToIso (congrArg (fun L : C ⥤ E ↦ L.obj M) h) ≪≫ e.app M)
    (objectwiseComparison_naturality h e)

/-- The pullback source comparison for the structure map of the actual swap.
Source: Stacks Tags 001U and 0D6D
(blueprint: def-pur-finite-proper-product-maps). -/
def swapPull {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B) :
    pull P (pullback.snd a b ≫ b) ≅
      pull P (pullback.snd b a ≫ a) ⋙ pull P (pullbackSymmetry a b).hom :=
  objectwiseComparison (congrArg (pull P) (swapStructure a b).symm)
    (comp P (pullbackSymmetry a b).hom (pullback.snd b a ≫ a))

end WeilConjectures.FiniteProperProduct
