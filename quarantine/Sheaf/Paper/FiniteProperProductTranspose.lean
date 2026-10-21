/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage

/-! # Counit transposes of the ordinary finite proper external product

Source: Stacks Project, sites-cohomology.tex, Tag 0E48 and the preceding
projection-formula-map; Tag 0D6E. The explicit seven-step counit calculation is
lem-pur-finite-proper-product-transpose, refining the symmetry paragraph of
blueprint main-20261015, lem-sf-kunneth-coherence.proof.md.
(blueprint: lem-pur-finite-proper-product-transpose).

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

/-- Counit transpose and swap of the finite proper external product.
Source: Stacks sites-cohomology.tex, Tag 0E48 and projection-formula-map; Tag 0D6E;
blueprint main-20261015, lem-sf-kunneth-coherence.proof.md, symmetry paragraph.
(blueprint: lem-pur-finite-proper-product-transpose).

Proof: (1) The constant-ring structural maps compose, so the recorded canonical
pullback/tensor and K-injective pushforward compositors preserve the actual ordinary
adjunctions (lem-pur-proetale-constant-ring-composition and
lem-sfb-ringed-derived-monoidal-comparisons). The transported kappa is exactly that
of lem-weil-derived-direct-image-composition, with its K-injective normalization.
(2) Exchange transposes to theta followed by the pulled-back a-counit. Projection
transposes to mu followed by epsilon tensor identity. Naturality of mu therefore
identifies the transpose of v with Lr*(epsilon_a) tensor identity.
(3) For w, counit naturality moves the pushed-forward symmetry through transposition.
The projection transpose and signed symmetry naturality cancel the two symmetries,
leaving identity tensor epsilon_b. No Koszul sign is discarded.
(4) The compositor compatibility and the composite Hom bijection identify the transpose
of omega with Lt*(the transpose of w) followed by the transpose of v. This follows
also by moving v through the b-counit by naturality.
(5) Insert (2) and (3), use tensor naturality and the canonical pullback composition
comparisons. Bifunctorial composition gives Lr*(epsilon_a) tensor Lt*(epsilon_b).
(6) For the swap, expand swapPush: Rc'(eta_s), kappa inverse, then Rc(swapTensor).
Its transpose is swapTensor followed after pullback of the original transpose:
counit naturality moves eta_s left and the adjunction triangle cancels it.
(7) Apply (5) to the reversed pair. Naturality and involutivity of signed symmetry
make its transported transpose equal to (5). Injectivity of the ordinary adjunction
Hom bijection gives the forward-map equality. Arbitrary unbounded objects are used
throughout; neither exchange nor projection is assumed invertible. -/
theorem finiteProperProductTranspose (P : PurityFiniteSetting.{u})
    (B Y Z : Over (Spec (.of P.field.k))) (a : Y ⟶ B) (b : Z ⟶ B)
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsProper a.left] [IsProper b.left] (H : D P Y.left) (J : D P Z.left) :
    ((adj P (pullback.snd a.left b.left)).homEquiv _ _).symm
        (v P a.left b.left Z.hom H J) =
      (mu P (pullback.snd a.left b.left) (pullback.snd a.left b.left ≫ Z.hom)
        Z.hom _ J).hom ≫
      (tensor P (pullback a.left b.left)).map
        (Prod.mkHom
          ((theta P a.left b.left).hom.app ((push P a.left).obj H) ≫
            (pull P (pullback.fst a.left b.left)).map ((adj P a.left).counit.app H))
          (𝟙 _)) ∧
    ((adj P b.left).homEquiv _ _).symm (w P a.left b.left B.hom Z.hom H J) =
      (mu P b.left Z.hom B.hom _ _).hom ≫
        (tensor P Z.left).map (Prod.mkHom (𝟙 _) ((adj P b.left).counit.app J)) ∧
    ((adj P (pullback.snd a.left b.left ≫ b.left)).homEquiv _ _).symm
        (omega P a.left b.left B.hom Z.hom H J) =
      (mu P (pullback.snd a.left b.left ≫ b.left)
        (pullback.snd a.left b.left ≫ Z.hom) B.hom _ _).hom ≫
      (tensor P (pullback a.left b.left)).map
        (Prod.mkHom
          ((eqToIso (congrArg
            (fun f ↦ (pull P f).obj ((push P a.left).obj H))
            (pullback.condition (f := a.left) (g := b.left)).symm)).hom ≫
            (comp P (pullback.fst a.left b.left) a.left).hom.app ((push P a.left).obj H) ≫
            (pull P (pullback.fst a.left b.left)).map ((adj P a.left).counit.app H))
          ((comp P (pullback.snd a.left b.left) b.left).hom.app ((push P b.left).obj J) ≫
            (pull P (pullback.snd a.left b.left)).map ((adj P b.left).counit.app J))) ∧
    ((adj P (pullback.snd a.left b.left ≫ b.left)).homEquiv _ _).symm
        (omega P a.left b.left B.hom Z.hom H J) =
      (comp P (pullback.snd a.left b.left) b.left).hom.app
        ((tensor P B.left).obj ((push P a.left).obj H, (push P b.left).obj J)) ≫
      (((adj P b.left).comp (adj P (pullback.snd a.left b.left))).homEquiv _ _).symm
        (w P a.left b.left B.hom Z.hom H J ≫
          (push P b.left).map (v P a.left b.left Z.hom H J)) ∧
    (((adj P b.left).comp (adj P (pullback.snd a.left b.left))).homEquiv _ _).symm
        (w P a.left b.left B.hom Z.hom H J ≫
          (push P b.left).map (v P a.left b.left Z.hom H J)) =
      (pull P (pullback.snd a.left b.left)).map
        (((adj P b.left).homEquiv _ _).symm (w P a.left b.left B.hom Z.hom H J)) ≫
      ((adj P (pullback.snd a.left b.left)).homEquiv _ _).symm
        (v P a.left b.left Z.hom H J) ∧
    omega P a.left b.left B.hom Z.hom H J =
      (sigma P B.left ((push P a.left).obj H) ((push P b.left).obj J)).hom ≫
        omega P b.left a.left B.hom Y.hom J H ≫
        swapPush P a.left b.left Y.hom Z.hom H J := by
  sorry

end WeilConjectures.FiniteProperProduct
