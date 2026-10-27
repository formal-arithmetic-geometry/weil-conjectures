module

public import Sheaf.Paper.ClopenCommonCompactSupport
public import Sheaf.Paper.ClopenStrictSystemSupport
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.Paper.ClopenStrictSystemComparison
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Counit-normalized clopen exceptional comparisons

Source: Zheng, arXiv:1006.3810, after Lemma 5.16 and Lemma 5.22, pp. 35--36;
finite-clopen adjunction argument retained in the DAG
(blueprint: lem-pur-clopen-counit-adjoint-comparison).

All finite functors use the existing intrinsic constant-ring presentation. The
system functors are the actual unbounded derived functors of strict systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

-- Since build 2026-10-28 another derived-category instance of the strict levels is in scope here;
-- keep the ones this module was written against.
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- The ordinary étale right adjoint with the specified compactification instance.
Source: Zheng, after Lemma 5.16 (blueprint: lem-pur-clopen-counit-adjoint-comparison). -/
def clopenCounitEtaleRight (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g) :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) g

/-- Its ordinary étale adjunction, retaining the canonical compactification comparison.
Source: Zheng, after Lemma 5.16 (blueprint: lem-pur-clopen-counit-adjoint-comparison). -/
def clopenCounitEtaleAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {g : X ⟶ Y} [QuasiCompact g] (c : Compactification g) :
    Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⊣ clopenCounitEtaleRight A c :=
  letI := c.hasCompactification
  (Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A) c).symm

/-- The bounded-below witness needed solely to evaluate the existing D+ support
comparison. Its existence is part of the finite conclusion below, not a hypothesis.
Source: Zheng Lemma 5.22 (blueprint: lem-pur-clopen-counit-adjoint-comparison). -/
def ClopenCounitBound (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (L : Scheme.proEtaleDerivedCategory Y A) : Prop :=
  DerivedCategory.TStructure.t.plus
    ((clopenCounitEtaleRight A c).obj
      ((ProEtale.comparisonLowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).rightDerivedFunctor.obj
          ((Scheme.sfIntrinsicDerivedEquivalence Y A).inverse.obj L)))

/-- The relative counit is the actual étale counit transported by the canonical
support comparison, comparison-site adjunction, and coefficient realization.
Source: Zheng Lemma 5.22 and the DAG Step 1
(blueprint: lem-pur-clopen-counit-adjoint-comparison). -/
def clopenFiniteCounit (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {g : X ⟶ Y} [QuasiCompact g] (c : Compactification g)
    (L : Scheme.proEtaleDerivedCategory Y A) (hL : ClopenCounitBound A c L) :
    (Scheme.sfIntrinsicCompactSupport c A).obj
      ((ProEtale.sfFiniteExceptional A c).obj L) ⟶ L :=
  (ProEtale.sfIntrinsicCompactSupportComparison A c).hom.app _ ≫
    (Scheme.sfIntrinsicDerivedEquivalence Y A).functor.map
      ((ProEtale.fixedCompactSupportComparisonIso (ULift.{u + 1} A) c).hom.app
          ⟨_, hL⟩ ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).mapDerivedCategory.map
            ((clopenCounitEtaleAdjunction A c).counit.app _) ≫
        (ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).counit.app _) ≫
    (Scheme.sfIntrinsicDerivedEquivalence Y A).counitIso.hom.app L

section Finite
variable (P : PurityFiniteSetting.{u})
  (X Y : Over (Spec (.of P.field.k)))
  [hXft : LocallyOfFiniteType X.hom] [hXqc : QuasiCompact X.hom]
  [hYft : LocallyOfFiniteType Y.hom] [hYqc : QuasiCompact Y.hom]
  (g : X ⟶ Y) [hgsep : IsSeparated g.left]
  [hgft : LocallyOfFiniteType g.left] [hgqc : QuasiCompact g.left]
  {I : Type w} [Finite I]
  (Xi : I → Over (Spec (.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left) (Set.range (j k).left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hXft hXqc hYft hYqc hgsep hgft hgqc hdisjoint hcover

/-- Finite comparison in the full bounded constructible input category, with unique
counit normalization and the natural represented Hom chain. No ambient pro-étale
adjunction is asserted.
Source: Zheng, after Lemma 5.16 and Lemma 5.22, pp. 35--36
(blueprint: lem-pur-clopen-counit-adjoint-comparison).

Proof: (1) use clopenSupport_insertion and its constructible preservation, and
clopenSupport_restriction_constructible, to restrict the specified component
adjunction to full bounded constructible categories. Compose its Hom bijection
with specifiedExceptionalHomEquiv, then precompose with the inverse of
clopenSupportComponentComparison. (2) The composite-adjunction counit is b inverse,
then compact support of the insertion counit, then the exceptional counit. Apply
det-sp-unique-right-adjoint inside the full constructible category. Its injective
Hom transpose proves uniqueness even for a family of component arrows.
(3) The i-th inclusion of the support sum is b inverse followed by support of the
insertion counit, hence its right-adjoint component has this same transpose.
Canonical compactification comparisons preserve the Hom chain; uniqueness gives
compatibility and the cocycle. Empty components are zero categories; for an empty
index type there are no comparisons. Every positive level is represented by P.level. -/
theorem clopenCounitAdjointComparison_finite (c : Compactification g.left) :
    ∃ (hG : ∀ (d : Compactification g.left)
        (L : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos Y.left).FullSubcategory),
          ClopenCounitBound P.Ring d L.obj)
      (hGi : ∀ (d : Compactification g.left) (i : I)
        (L : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos Y.left).FullSubcategory),
          ClopenCounitBound P.Ring (d.precomp (j i).left) L.obj)
      (adj : ∀ i, Scheme.sfIntrinsicDerivedOpen P.Ring (j i).left ⊣
        Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left),
      (∀ i, (adj i).unit = Scheme.sfIntrinsicDerivedOpenUnit P.Ring (j i).left) ∧
      (∀ L : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos Y.left).FullSubcategory,
        Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos X.left ((ProEtale.sfFiniteExceptional P.Ring c).obj L.obj) ∧
        ∀ i, Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos (Xi i).left
            ((Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj
              ((ProEtale.sfFiniteExceptional P.Ring c).obj L.obj)) ∧
          Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
            P.level P.level_pos (Xi i).left
              ((ProEtale.sfFiniteExceptional P.Ring (c.precomp (j i).left)).obj L.obj)) ∧
      ∀ i : I, ∃! rho :
        (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
            P.level P.level_pos Y.left).ι ⋙ ProEtale.sfFiniteExceptional P.Ring c ⋙
          Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left ≅
        (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
            P.level P.level_pos Y.left).ι ⋙
          ProEtale.sfFiniteExceptional P.Ring (c.precomp (j i).left),
        ∀ (d : Compactification g.left) L,
          (Scheme.sfIntrinsicCompactSupport (d.precomp (j i).left) P.Ring).map
              (rho.hom.app L) ≫ clopenFiniteCounit P.Ring (d.precomp (j i).left)
                L.obj (hGi d i L) =
            (P.clopenSupportComponentComparison d (j i).left).inv.app _ ≫
              (Scheme.sfIntrinsicCompactSupport d P.Ring).map
                ((adj i).counit.app ((ProEtale.sfFiniteExceptional P.Ring c).obj L.obj)) ≫
              clopenFiniteCounit P.Ring d L.obj (hG d L) ∧
          ∀ M : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
            P.level P.level_pos (Xi i).left).FullSubcategory,
            Function.Bijective (fun a : M.obj ⟶
                (Scheme.sfIntrinsicDerivedPullback P.Ring (j i).left).obj
                  ((ProEtale.sfFiniteExceptional P.Ring c).obj L.obj) ↦
              (Scheme.sfIntrinsicCompactSupport (d.precomp (j i).left) P.Ring).map a ≫
                (P.clopenSupportComponentComparison d (j i).left).inv.app _ ≫
                  (Scheme.sfIntrinsicCompactSupport d P.Ring).map
                    ((adj i).counit.app
                      ((ProEtale.sfFiniteExceptional P.Ring c).obj L.obj)) ≫
                    clopenFiniteCounit P.Ring d L.obj (hG d L)) := by
  sorry

end Finite

section Systems
variable (P : PurityFiniteSetting.{u})
  {I : Type u} [Finite I] {X Y : Scheme.{u}} {g : X ⟶ Y}
  (Xi : I → Scheme.{u}) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
  (c : Compactification g)
  (S : StrictEtaleCompactSupport (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) c)
  (Si : ∀ i, StrictEtaleCompactSupport (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) (c.precomp (j i)))
  (R : StrictEtaleClopenOrdinary (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) Xi j)
  (D : StrictEtaleClopenDerived (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) Xi j c S Si R)
  (B : StrictEtaleClopenSupport (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) Xi j c S Si R D)
  (G : StrictEtaleExceptionalAdjoint (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) c S)
  (Gi : ∀ i, StrictEtaleExceptionalAdjoint (clopenSystemRing P.coefficients.l P.extension)
    (clopenSystemUniformizer P.coefficients.l P.extension) (c.precomp (j i)) (Si i))

/-- The normalized component counit in the actual derived category of strict systems.
Source: Zheng, after Lemma 5.16 (blueprint: lem-pur-clopen-counit-adjoint-comparison). -/
def clopenSystemComponentCounit (i : I)
    (L : DerivedCategory (strictEtaleCoefficientSystem Y
      (clopenSystemRing P.coefficients.l P.extension)
      (clopenSystemUniformizer P.coefficients.l P.extension))) :=
  (B.val.support i).inv.app ((D.val.image i).system.inverse.obj (G.right.obj L)) ≫
    S.functor.map ((D.val.reverseAdj i).counit.app (G.right.obj L)) ≫
      G.adjunction.counit.app L

/-- The same normalized counit at an ordinary étale finite coefficient level.
Source: Zheng Lemma 5.22 (blueprint: lem-pur-clopen-counit-adjoint-comparison). -/
def clopenLevelComponentCounit (i : I) (n : ℕ)
    (L : DerivedCategory (strictEtaleLevel Y
      (clopenSystemRing P.coefficients.l P.extension)
      (clopenSystemUniformizer P.coefficients.l P.extension) n)) :=
  (B.val.levelSupport i n).inv.app (((D.val.image i).level n).inverse.obj
      ((G.levelRight n).obj L)) ≫
    (S.levelFunctor n).map ((D.val.reverseLevelAdj i n).counit.app
      ((G.levelRight n).obj L)) ≫ (G.levelAdjunction n).counit.app L

/-- The restriction quotient mate, with the inverse orientation used in the square.
Its data is the existing scalar-image comparison, normalized by the ordinary tensor
unit and the flat-term K-flat representative equation; it is not an arbitrary map.
Source: Zheng Construction 4.1 and Lemma 4.10; DAG proof Step 7
(blueprint: lem-pur-clopen-counit-adjoint-comparison). -/
def clopenRestrictionQuotient (i : I) {m n : ℕ} (h : n ≤ m) :
    ((D.val.image i).level m).inverse ⋙ ((Si i).PX.scalar h).derived ≅
      (S.PX.scalar h).derived ⋙ ((D.val.image i).level n).inverse :=
  ((D.val.scalar i).derivedTensor h).symm

/-- The actual system comparison, its unique finite evaluations, scalar action,
and quotient-transition square with the prescribed exceptional adjunction mate.
The input records are precisely the support and right adjoints fixed in the node;
their existence is already supplied by its two dependency theorems.
Source: Zheng, after Lemma 5.16 and Lemma 5.22, pp. 35--36
(blueprint: lem-pur-clopen-counit-adjoint-comparison).

Proof: (4) compose the insertion adjunction D.reverseAdj with G.adjunction,
then change the left functor by the specified B.support. Right-adjoint uniqueness
against Gi.adjunction gives rho and its counit formula. (5) The formula is the
Gi-transpose of the displayed component counit. The two right adjoints and
geometric restriction are O-linear, so the scalar square holds. (6) Evaluate this
transpose, using both evaluated units and counits from the system-adjoint theorem
and the insertion and support equations from the strict-support theorem. Each
factor becomes the level factor; injectivity of the level transpose identifies
rhoLevel n, naturally on every derived system morphism. (7) Retain all levels
as one family. Paste the canonical restriction quotient mate
(D.scalar i).derivedTensor.inv, characterized by its K-flat representative formula,
with G.quotientComparison, and compare with Gi.quotientComparison. The support
compositor respects ordinary quotient transitions; transposing its counit formula
therefore identifies the two pasted mates by level-adjunction uniqueness.
The final square is on arbitrary level objects L, for arbitrary, successive and
identity quotients. No equality of system arrows is inferred from joint
faithfulness of evaluation. Empty components have only the unique zero maps,
and there are no indexed comparisons for an empty cover. -/
theorem clopenCounitAdjointComparison_system
    (sY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType sY] [QuasiCompact sY]
    [LocallyOfFiniteType (g ≫ sY)] [QuasiCompact (g ≫ sY)]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (_hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i)) (Set.range (j k)))
    (_hcover : (⋃ i, Set.range (j i)) = Set.univ) (i : I) :
    ∃ rho : G.right ⋙ (D.val.image i).system.inverse ≅ (Gi i).right,
      (∀ L, (Si i).functor.map (rho.hom.app L) ≫ (Gi i).adjunction.counit.app L =
        clopenSystemComponentCounit P Xi j c S Si R D B G i L) ∧
      (∀ sigma : G.right ⋙ (D.val.image i).system.inverse ≅ (Gi i).right,
        (∀ L, (Si i).functor.map (sigma.hom.app L) ≫ (Gi i).adjunction.counit.app L =
          clopenSystemComponentCounit P Xi j c S Si R D B G i L) → sigma = rho) ∧
      (∀ a L,
        (D.val.image i).system.inverse.map ((G.val.scalarX.derived a).app (G.right.obj L)) ≫
            rho.hom.app L =
          rho.hom.app L ≫ ((Gi i).val.scalarX.derived a).app ((Gi i).right.obj L)) ∧
      ∃ rhoLevel : ∀ n : ℕ,
          G.levelRight n ⋙ ((D.val.image i).level n).inverse ≅ (Gi i).levelRight n,
        (∀ n L, ((Si i).levelFunctor n).map ((rhoLevel n).hom.app L) ≫
            ((Gi i).levelAdjunction n).counit.app L =
          clopenLevelComponentCounit P Xi j c S Si R D B G i n L) ∧
        (∀ n (sigma : G.levelRight n ⋙ ((D.val.image i).level n).inverse ≅
            (Gi i).levelRight n),
          (∀ L, ((Si i).levelFunctor n).map (sigma.hom.app L) ≫
              ((Gi i).levelAdjunction n).counit.app L =
            clopenLevelComponentCounit P Xi j c S Si R D B G i n L) →
          sigma = rhoLevel n) ∧
        (∀ n L, ((Si i).PX.evaluation n).map (rho.hom.app L) ≫
            ((Gi i).evaluation n).hom.app L =
          ((D.val.image i).inverseEvaluation n).hom.app (G.right.obj L) ≫
            ((D.val.image i).level n).inverse.map ((G.evaluation n).hom.app L) ≫
            (rhoLevel n).hom.app ((S.PY.evaluation n).obj L) ≫
            ((Gi i).levelRight n).map
              (eqToHom (congrArg (fun Q ↦ (Q.evaluation n).obj L)
                (B.val.sameTarget i).symm))) ∧
        ∀ {m n : ℕ} (h : n ≤ m)
          (L : DerivedCategory (strictEtaleLevel Y
            (clopenSystemRing P.coefficients.l P.extension)
            (clopenSystemUniformizer P.coefficients.l P.extension) m)),
          ((Si i).PX.scalar h).derived.map ((rhoLevel m).hom.app L) ≫
              ((Gi i).quotientComparison h).hom.app L =
            (clopenRestrictionQuotient P Xi j c S Si R D i h).hom.app
              ((G.levelRight m).obj L) ≫
              ((D.val.image i).level n).inverse.map ((G.quotientComparison h).hom.app L) ≫
              (rhoLevel n).hom.app ((S.PY.scalar h).derived.obj L) ≫
              ((Gi i).levelRight n).map
                (eqToHom (congrArg (fun Q ↦ (Q.scalar h).derived.obj L)
                  (B.val.sameTarget i).symm)) := by
  sorry

end Systems
end WeilConjectures.PurityFiniteSetting
