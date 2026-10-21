/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Sectionwise localization and sheafification of an internal ring

Source: Stacks Project, Modules on Sites, Tag 0EMC, lemma-simple-invert;
ordinary localization: Algebra, Tags 00CO and 00CP.
(blueprint: lem-sfb-ring-localization-sheafification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Opposite
namespace CategoryTheory

attribute [instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable {C : Type u} [Category.{v} C]

/-- Fractions in the actual localization, including power torsion.
Source: Stacks Tags 00CO and 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationFraction {A : Type w} [CommRing A] (t r : A) (n : ℕ) :
    Localization.Away t :=
  Localization.mk r ⟨t ^ n, ⟨n, rfl⟩⟩

/-- The actual sectionwise localization presheaf; restrictions are localization maps.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationPresheaf (A : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := CommRingCat.of (Localization.Away (M := A.obj U) (t.val U))
  map {U V} f := CommRingCat.ofHom (IsLocalization.map (Localization.Away (M := A.obj V) (t.val V))
    (P := A.obj V) (R := A.obj U) (S := Localization.Away (M := A.obj U) (t.val U))
    (M := Submonoid.powers (t.val U : A.obj U))
    (T := Submonoid.powers (t.val V : A.obj V)) (A.map f).hom (by
    rintro x ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change (t.val V : A.obj V) ^ n = (A.map f).hom ((t.val U : A.obj U) ^ n)
    rw [map_pow]
    exact congrArg (fun a : A.obj V => a ^ n) (t.property f).symm))
  map_id U := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (R := A.obj U)
      (Submonoid.powers (t.val U : A.obj U))
    ext r
    simp
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (R := A.obj U)
      (Submonoid.powers (t.val U : A.obj U))
    ext r
    simp

/-- The canonical sectionwise map r ↦ r/1.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationPresheafUnit (A : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) : A ⟶ sfbLocalizationPresheaf A t where
  app U := CommRingCat.ofHom (algebraMap (A.obj U) (Localization.Away (M := A.obj U) (t.val U)))
  naturality U V f := by
    ext r
    simp [sfbLocalizationPresheaf]

/-- The presheaf consists of fractions with the stated power-torsion relation,
ring operations and restriction formula; no cancellation is used.
Source: Stacks Tags 00CO, 00CP and 0EMC
(blueprint: lem-sfb-ring-localization-sheafification).

Proof: apply the fraction description of def-weil-ring-localization-away at each
object. Every denominator is a power of t. Cross multiplication in localization
says that two fractions agree precisely after multiplication by another power of t.
The localization addition and multiplication formulas give the displayed operations.
For a restriction, lem-weil-pbc-localization-away-universal-property characterizes
its lift by the restriction on r/1 and sends the denominator to the same power of
the restricted section. It therefore gives the displayed fraction formula.
Identity and composition follow by the uniqueness clause of that same node. -/
theorem sfbLocalizationPresheaf_spec (A : Cᵒᵖ ⥤ CommRingCat.{w})
    (t : (A ⋙ forget CommRingCat).sections) :
    (∀ (U : Cᵒᵖ) (x : Localization.Away (M := A.obj U) (t.val U)),
      ∃ (r : A.obj U) (n : ℕ), x = sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n) ∧
    (∀ (U : Cᵒᵖ) (r r' : A.obj U) (n m : ℕ),
      sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n = sfbLocalizationFraction (@id (A.obj
          U) (t.val U)) r' m ↔
        ∃ k : ℕ, (@id (A.obj U) (t.val U)) ^ k * ((@id (A.obj U) (t.val U)) ^ m * r - (@id (A.obj
          U) (t.val U)) ^ n * r') = 0) ∧
    (∀ (U : Cᵒᵖ) (r r' : A.obj U) (n m : ℕ),
      sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n + sfbLocalizationFraction (@id (A.obj
          U) (t.val U)) r' m =
        sfbLocalizationFraction (@id (A.obj U) (t.val U)) ((@id (A.obj U) (t.val U)) ^ m * r +
          (@id (A.obj U) (t.val U)) ^ n * r') (n + m) ∧
      sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n * sfbLocalizationFraction (@id (A.obj
          U) (t.val U)) r' m =
        sfbLocalizationFraction (@id (A.obj U) (t.val U)) (r * r') (n + m)) ∧
    (∀ {U V : Cᵒᵖ} (f : U ⟶ V) (r : A.obj U) (n : ℕ),
      (sfbLocalizationPresheaf A t).map f (sfbLocalizationFraction (@id (A.obj U) (t.val U)) r n) =
        sfbLocalizationFraction (t.val V) (A.map f r) n) := by
  sorry

variable (J : GrothendieckTopology C)

/-- The size assumption in the node supplies left exact abelian sheafification.
Source: Stacks, Sites, Tag 00W1; the sheafification used in Tag 0EMC
(blueprint: lem-sfb-ring-localization-sheafification).

Proof: use UnivLE to replace the site by a small equivalent category in universe w.
Apply GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian to abelian groups on
that small model and transport the left exact reflector along the equivalence,
as in hasSheafifyEssentiallySmallSite. Thus this is supplied by the size convention,
rather than an additional hypothesis of the localization theorem. -/
@[instance 20000] theorem sfbLocalization_hasSheafify [UnivLE.{max u v, w}] :
    HasSheafify J AddCommGrpCat.{w} := by
  sorry

/-- Sheafification equivalences are stable under the tensor product of abelian presheaves.
Source: blueprint sk-def-sfb-sheaf-tensor, strong monoidality, applied in Stacks Tag 0EMC
(blueprint: lem-sfb-ring-localization-sheafification).

Proof: use the small-model end constructions in sk-def-sfb-sheaf-tensor. Its strong
symmetric monoidal comparison identifies sheafification of q tensor H with the tensor
of the sheafifications. If sheafification inverts q it therefore inverts q tensor H;
symmetry gives the other variable. This is exactly the two fields of IsMonoidal. -/
@[instance 20000] theorem sfbLocalization_monoidalLocalEquivalences [UnivLE.{max u v, w}] :
    (J.W (A := AddCommGrpCat.{w})).IsMonoidal := by
  sorry

/-- Sheafify the sectionwise localization as a commutative internal ring, using the
strong symmetric monoidal abelian sheafification functor.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationRingObject (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    CommMon (Sheaf J AddCommGrpCat.{max u v w}) := by
  let P := sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t
  let Q := P ⋙ forget₂ CommRingCat RingCat
  letI : IsCommMonObj (Q ⋙ forget₂ RingCat AddCommGrpCat.{max u v w}) :=
    Q.isCommMonObj_compForget₂ (fun U a b => @mul_comm (P.obj U) _ a b)
  exact (presheafToSheaf J AddCommGrpCat.{max u v w}).mapCommMon.obj
    (CommMon.mk (Q ⋙ forget₂ RingCat AddCommGrpCat.{max u v w}))

/-- A morphism of internal commutative rings acts by ring homomorphisms on sections.
Source: Stacks Tag 00YV, and the section-ring reconstruction used in Tag 0EMC
(blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbRingSectionMap {R D : CommMon (Sheaf J AddCommGrpCat.{max u v w})}
    (f : R ⟶ D) : InternalAbelianSheafModule.sectionRings J R.X ⟶
      InternalAbelianSheafModule.sectionRings J D.X :=
  Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{max u v w}).functor.map
      ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapCommMon.map f))
    InternalAbelianSheafModule.commMonToRing.{max u v w}

/-- The underlying abelian sheaf map into the sheafified localization.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationUnderlyingUnit (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    R.X ⟶ (sfbLocalizationRingObject.{u, v, w} J R t).X :=
  (asIso ((sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit.app R.X)).inv ≫
    (presheafToSheaf J AddCommGrpCat.{max u v w}).map
      (Functor.whiskerRight
        (sfbLocalizationPresheafUnit (InternalAbelianSheafModule.sectionRings J R.X) t)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{max u v w}))

/-- The canonical localization unit preserves the internal multiplication and unit.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification).

Proof: reconstruct the section rings of R by evaluating its multiplication on pure
 tensors and its unit on 1, as in def-weil-pbc-internal-abelian-sheaf-module-equivalence.
 The sectionwise algebra maps commute with restriction by the uniqueness in
 lem-weil-pbc-localization-away-universal-property and preserve multiplication and one.
 Strong monoidal sheafification from sk-def-sfb-sheaf-tensor sends this presheaf ring
 map to an internal ring map. The inverse sheafification counit is an internal ring
 isomorphism by det-def-sfb-ring-object-sheaf and the section-ring reconstruction.
 Their composite is the displayed map. -/
theorem sfbLocalizationUnderlyingUnit_isMonHom
    (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    IsMonHom (sfbLocalizationUnderlyingUnit.{u, v, w} J R t) := by
  sorry

/-- The canonical internal ring map R → aP, with no chosen undetermined data.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification). -/
def sfbLocalizationUnit (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    R ⟶ sfbLocalizationRingObject.{u, v, w} J R t := by
  letI := sfbLocalizationUnderlyingUnit_isMonHom.{u, v, w} J R t
  exact CommMon.homMk (Mon.Hom.mk (sfbLocalizationUnderlyingUnit.{u, v, w} J R t))

/-- Sheafification of the sectionwise localization is the universal internal
commutative ring in which the given global section is invertible. Its underlying
section-ring sheaf is ring sheafification, normalized by the abelian sheafification
unit. The comparison with any other localization is the unique compatible isomorphism.
Source: Stacks Tag 0EMC (blueprint: lem-sfb-ring-localization-sheafification).

Proof, following the node's six steps:
1. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence to recover section
rings by multiplication on pure tensors and evaluation of the unit at 1.
The monoidal-local-equivalence condition follows from sk-def-sfb-sheaf-tensor.
The inverse reconstruction and morphism equations follow by the unique extension
in det-def-sfb-ring-object-sheaf and def-weil-pbc-sheafification.
2. Form the actual objectwise localization and its restrictions, using
lem-weil-pbc-localization-away-universal-property. The same uniqueness proves the
presheaf laws and naturality of r ↦ r/1; sfbLocalizationPresheaf_spec records the
fractions, relation and operations of def-weil-ring-localization-away.
3. Sheafify its internal commutative ring structure by the strong symmetric
monoidal abelian sheafification. The canonical unit is the sheafified r ↦ r/1
composed with the inverse counit. The compatible fractions 1/t give a global
inverse of its image of t. The first displayed equality is counit normalization.
4. For f:R→D inverting t, extend each f_U uniquely to the section localization
by lem-weil-pbc-localization-away-universal-property. Its value on r/t^n is
f_U(r)f_U(t)^(-n). Uniqueness on r/1 makes these extensions natural.
5. Extend this presheaf ring morphism uniquely through sheafification, using
def-weil-pbc-sheafification and the ring-object correspondence in step 1. This
also proves the displayed ring-sheafification universal property for arbitrary
presheaf ring maps h. If two maps out of aP agree after the localization unit,
localization uniqueness makes their presheaf restrictions agree, and
sheafification uniqueness makes the maps equal.
6. Apply both localization universal properties to get maps aP→L and L→aP.
Their composites are identities by uniqueness, and the map aP→L is unique even
among all maps, hence among isomorphisms. No cancellation of t and no stalks or
enough-points assumption enter the argument. -/
theorem sfbRingLocalizationSheafification
    (R : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
    (t : (InternalAbelianSheafModule.sectionRings J R.X ⋙ forget CommRingCat).sections) :
    (∀ (U : Cᵒᵖ) (r : (InternalAbelianSheafModule.sectionRings J R.X).obj U),
      (sfbRingSectionMap.{u, v, w} J (sfbLocalizationUnit.{u, v, w} J R t)).app U r =
        (toSheafify J
          ((sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t) ⋙ forget₂
          CommRingCat RingCat ⋙
            forget₂ RingCat AddCommGrpCat.{max u v w})).app U
          ((sfbLocalizationPresheafUnit (InternalAbelianSheafModule.sectionRings J R.X) t).app U
          r)) ∧
    (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap.{u, v, w} J (sfbLocalizationUnit.{u, v, w} J R t)).app
          U (t.val U))) ∧
    (∀ (D : CommMon (Sheaf J AddCommGrpCat.{max u v w})) (f : R ⟶ D),
      (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap.{u, v, w} J f).app U (t.val U))) →
        ∃! g : (sfbLocalizationRingObject.{u, v, w} J R t) ⟶ D, (sfbLocalizationUnit.{u, v, w} J R
          t) ≫ g = f) ∧
    (∀ (L : CommMon (Sheaf J AddCommGrpCat.{max u v w})) (j : R ⟶ L),
      (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap.{u, v, w} J j).app U (t.val U))) →
      (∀ (D : CommMon (Sheaf J AddCommGrpCat.{max u v w})) (f : R ⟶ D),
        (∀ U : Cᵒᵖ, IsUnit ((sfbRingSectionMap.{u, v, w} J f).app U (t.val U))) →
          ∃! g : L ⟶ D, j ≫ g = f) →
      ∃! γ : (sfbLocalizationRingObject.{u, v, w} J R t) ≅ L, (sfbLocalizationUnit.{u, v, w} J R
          t) ≫ γ.hom = j) ∧
    (∀ (D : CommMon (Sheaf J AddCommGrpCat.{max u v w}))
      (h : (sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t) ⟶
          InternalAbelianSheafModule.sectionRings J D.X),
      ∃! g : (sfbLocalizationRingObject.{u, v, w} J R t) ⟶ D,
        ∀ (U : Cᵒᵖ) (x : (sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X)
          t).obj U),
          (sfbRingSectionMap.{u, v, w} J g).app U
            ((toSheafify J
              ((sfbLocalizationPresheaf (InternalAbelianSheafModule.sectionRings J R.X) t) ⋙
          forget₂ CommRingCat RingCat ⋙
                forget₂ RingCat AddCommGrpCat.{max u v w})).app U x) = h.app U x) := by
  sorry

end CategoryTheory
