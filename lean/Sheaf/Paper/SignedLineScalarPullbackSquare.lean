/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.Paper.SignedLineScalarTensorTower
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
public import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses

/-! # Pullback of the signed line scalar square

Source: blueprint main-20261015, prop-weil-twist-preserves.proof.md, first and final
sentences; Stacks Project, Modules on Sites, Tags 03EL, 0GMX and 04J0.
(blueprint: lem-pur-signed-line-scalar-pullback-square)

The structural ring maps are written as adjuncts R → u_* R' and S → u_* S'.
The pullbacks are Mathlib's actual module left adjoints, with existence supplied by
`module_pushforward_isRightAdjoint_of_universes`, hence the sheafified relative tensors.
The square is tested on the adjunction-unit images of scalar tensors. These generate
by the two adjunctions, so this is the morphism equality under canonical reassociation,
not an equality restricted to bases or to global sections. The evaluation clause likewise
specifies the transpose of pulled evaluation, precomposed by the inverse positive map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]

/-- Unit, degree one, positive tensor recursion, and negative evaluation normalization.
Source: Stacks 03EL and 0GMX; node proof steps 1, 3--5.
(blueprint: lem-pur-signed-line-scalar-pullback-square)
The last equation is the pulled evaluation pairing on generators. Since the positive
map is invertible it says exactly that the negative map is the transpose of that pairing
followed by precomposition with the inverse positive map. All source objects V are tested,
including after restriction; bilinearity and the module adjunction extend it to the
entire tensor product of the pullbacks. -/
def SignedLinePullbackNormalized
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (P : ∀ m : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m) : Prop :=
  (∀ (V : C) (r : R.obj.obj (op V)),
    (P 0).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L 0) V r) = a.hom.app (op V) r) ∧
  (P 1).hom = p.hom ∧
  (∀ (n : ℕ) (V : C) (x : (scalarTensorPower R L (n + 1)).val.obj (op V))
    (y : L.val.obj (op V)),
    (P (.ofNat (n + 2))).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (scalarTensorPower R L (n + 2)) V
          (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L (op V) x y)) =
      siteSheafTensorTmul (scalarTensorPower R' L' (n + 1)) L' (op (U.obj V))
        ((P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            (scalarTensorPower R L (n + 1)) V x))
        (p.hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            L V y))) ∧
  (∀ (n : ℕ) (V : C)
    (φ : (signedLinePower.{u, v, w} L (.negSucc n)).val.obj (op V))
    (x : (scalarTensorPower R L (n + 1)).val.obj (op V)),
    (((P (.negSucc n)).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L (.negSucc n)) V φ)).app
          (op (Over.mk (𝟙 (U.obj V)))))
      ((P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          (scalarTensorPower R L (n + 1)) V x)) =
      a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) x))

/-- The actual scalar/pullback square, tested on its canonical local generators.
Source: Stacks 03EL, tensor balancing; blueprint first-line square; node proof steps 2, 8.
(blueprint: lem-pur-signed-line-scalar-pullback-square)
Under Θ, the pulled image of x tensor s is (pulled x tensor 1) tensor b(s).
Thus this equation is exactly q F_S(c) = c' (p tensor 1) Θ. Equality on these
sections determines the two morphisms by scalar-extension and pullback adjunctions.
No surjectivity of the sectionwise sheafification unit is assumed. -/
def SignedLineScalarPullbackSquare
    {R S : Sheaf J CommRingCat.{max u v w}}
    {R' S' : Sheaf K CommRingCat.{max u v w}} (ι : R ⟶ S) (ι' : R' ⟶ S')
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (b : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (N' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (c : changeOfRingsOfUniverses ι L ≅ N)
    (c' : changeOfRingsOfUniverses ι' L' ≅ N')
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (q : (ringedSitePullbackFunctor b
      (module_pushforward_isRightAdjoint_of_universes b)).obj N ≅ N') : Prop :=
  ∀ (V : C) (x : L.val.obj (op V)) (s : S.obj.obj (op V)),
    q.hom.val.app (op (U.obj V))
      ((ringedSitePullbackFunctor b (module_pushforward_isRightAdjoint_of_universes b)).map
        c.hom |>.val.app (op (U.obj V))
          (ringedSitePullbackSection b (module_pushforward_isRightAdjoint_of_universes b)
            (changeOfRingsOfUniverses ι L) V (scalarExtensionSection ι L (op V) s x))) =
      c'.hom.val.app (op (U.obj V))
        (scalarExtensionSection ι' L' (op (U.obj V)) (b.hom.app (op V) s)
          (p.hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
              L V x)))

/-- Unique normalized signed pullbacks and compatibility with the scalar square in every
integer degree. Source: blueprint prop-weil-twist-preserves.proof.md, first/final sentences;
Stacks 03EL, 0GMX, 0FNY and 04J0.
(blueprint: lem-pur-signed-line-scalar-pullback-square)

Proof:
1. The inverse image and module tensor comparison give normalized tensor and unit maps.
The unit multiplies the coefficient factors and its inverse inserts 1.
2. Reassociate scalar extension across the commuting coefficient square. On generators
(x tensor y) tensor t goes to (x tensor 1) tensor b(y)t. The reverse inserts 1 and
multiplies by ι'(r'); balancing and b ι = ι' a prove they are mutual inverses.
3. Starting with the unit and p (respectively q), iterate the tensor comparison. All
positive powers remain locally free rank one by their tensor bases.
4. Apply finite_free_dual_pullback to each positive power. Compose its evaluation-defined
comparison with precomposition by the inverse positive map. The evaluation identity
follows by cancelling the positive map. The same construction gives the q-family.
5. Degree zero and one are fixed; tensor recursion forces all positive maps. Pulled
evaluation and invertibility of the positive maps force every negative map, proving
uniqueness. This is equality of sheaf Hom sections on every localized site.
6. Pullback localization identifies local and global units and carries every trivializing
cover to a trivializing cover. The slice continuity follows from cover preservation.
7. Choose a local basis e for L and its image v = c(e tensor 1) for N. Their pulled images
under p and q are compatible target bases by the assumed square. Positive recursion
and dual evaluation carry every signed basis to its corresponding target basis.
8. On these charts both scalar-square composites carry the signed generator to the same
target signed basis. Linearity gives equality on every scalar multiple; sheaf uniqueness
glues the equality. This includes zero and negative degrees and uses no flatness.
-/
theorem existsUnique_signedLineScalarPullbackSquare
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R S : Sheaf J CommRingCat.{max u v w}}
    {R' S' : Sheaf K CommRingCat.{max u v w}} (ι : R ⟶ S) (ι' : R' ⟶ S')
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (b : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (_hab : (sheafCompose J (forget₂ CommRingCat RingCat)).map ι ≫ b =
      a ≫ (U.sheafPushforwardContinuous RingCat J K).map
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map ι'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (N' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (_hL : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (L.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))))
    (_hN : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (N.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (V i))))
    (_hL' : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (L'.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R').over (V i))))
    (_hN' : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (N'.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S').over (V i))))
    (c : changeOfRingsOfUniverses ι L ≅ N)
    (c' : changeOfRingsOfUniverses ι' L' ≅ N')
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (q : (ringedSitePullbackFunctor b
      (module_pushforward_isRightAdjoint_of_universes b)).obj N ≅ N')
    (_hc : SignedLineScalarPullbackSquare ι ι' a b L N L' N' c c' p q)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses ι (signedLinePower.{u, v, w} L m) ≅
      signedLinePower.{u, v, w} N m)
    (B' : ∀ m : ℤ, changeOfRingsOfUniverses ι' (signedLinePower.{u, v, w} L' m) ≅
      signedLinePower.{u, v, w} N' m)
    (_hB : SignedLineComparisonNormalized.{u, v, w} ι L N c B)
    (_hB' : SignedLineComparisonNormalized.{u, v, w} ι' L' N' c' B') :
    ∃! PQ :
      (∀ m : ℤ, (ringedSitePullbackFunctor a
        (module_pushforward_isRightAdjoint_of_universes a)).obj
          (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m) ×
      (∀ m : ℤ, (ringedSitePullbackFunctor b
        (module_pushforward_isRightAdjoint_of_universes b)).obj
          (signedLinePower.{u, v, w} N m) ≅ signedLinePower.{u, v, w} N' m),
      SignedLinePullbackNormalized a L L' p PQ.1 ∧
      SignedLinePullbackNormalized b N N' q PQ.2 ∧
      ∀ m : ℤ, SignedLineScalarPullbackSquare ι ι' a b
        (signedLinePower.{u, v, w} L m) (signedLinePower.{u, v, w} N m)
        (signedLinePower.{u, v, w} L' m) (signedLinePower.{u, v, w} N' m)
        (B m) (B' m) (PQ.1 m) (PQ.2 m) := by
  sorry

end SheafOfModules
