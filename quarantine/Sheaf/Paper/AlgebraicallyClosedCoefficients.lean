/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.ScalarExtensionExact
public import Sheaf.Paper.ScalarExtensionComposition
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.CategoryTheory.StageSystemVerdier
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.LinearAlgebra.Dimension.Free

/-! # Algebraically closed coefficients without idempotent completion

Source: blueprint `sec-smooth-purity/sk-def-sf-operations`, order 1462
(blueprint: def-weil-algebraically-closed-coefficients).
Objects are actual pairs and Hom is the directed colimit of the stated abelian groups.
The existing upstream pair category supplies its quotient, identities and composition;
its Hom groups are canonically the displayed abelian-group colimits.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe d u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace WeilConjectures
namespace AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- Finite coefficient fields in the fixed closure.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev Index := Padic.FiniteCoefficientFields l Ω

/-- A finite-dimensional coefficient field has a model in every site universe.
The finite-basis coordinate equivalence constructs its Small proof without an axiom.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance coefficientSmall (E : Index l Ω) : Small.{u} E.val :=
  small_map (Module.finBasis (Padic l) E.val).equivFun.toEquiv

/-- The canonical size transport of a finite field to the scheme's universe.
Its algebra equivalence is Shrink.algEquiv; no coefficient closure/site size equality
is imposed. Source: blueprint order 1462
(blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Coefficient (E : Index l Ω) : Type u := Shrink.{u} E.val

/-- Finite dimensionality survives the canonical size transport.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance coefficientFinite (E : Index l Ω) :
    FiniteDimensional (Padic l) (Coefficient.{u} l Ω E) :=
  Module.Finite.equiv (Shrink.algEquiv (Padic l) E.val).symm.toLinearEquiv

/-- Inclusion transported through the actual algebra equivalences of the small models.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def coefficientInclusion (E L : Index l Ω) (h : E ≤ L) :
    Coefficient.{u} l Ω E →ₐ[Padic l] Coefficient.{u} l Ω L :=
  (Shrink.algEquiv (Padic l) L.val).symm.toAlgHom.comp
    ((IntermediateField.inclusion h).comp (Shrink.algEquiv (Padic l) E.val).toAlgHom)

/-- The size transports preserve identity and composition of field inclusions.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: expand the conjugated inclusions. The inverse algebra equivalences cancel;
extensionality reduces both identities to identity/composition of subtype inclusions. -/
theorem coefficientInclusion_laws :
    (∀ E : Index l Ω, coefficientInclusion.{u} l Ω E E le_rfl =
      AlgHom.id (Padic l) (Coefficient.{u} l Ω E)) ∧
    (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
      (coefficientInclusion.{u} l Ω L M k).comp (coefficientInclusion.{u} l Ω E L h) =
        coefficientInclusion.{u} l Ω E M (h.trans k)) := by
  sorry

/-- The specified raw rational stage, using its equivalent small coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def Stage (E : Index l Ω) :=
  rationalConstructibleCategory D l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage D l hl Ω Y E) :=
  inferInstanceAs (Category (rationalConstructibleCategory D l hl (Coefficient.{u} l Ω E) Y))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stagePreadditive (E : Index l Ω) :
    Preadditive (Stage D l hl Ω Y E) :=
  inferInstanceAs (Preadditive
    (rationalConstructibleCategory D l hl (Coefficient.{u} l Ω E) Y))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageZero (E : Index l Ω) :
    HasZeroObject (Stage D l hl Ω Y E) :=
  rationalConstructibleZero D l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShift (E : Index l Ω) :
    HasShift (Stage D l hl Ω Y E) ℤ :=
  rationalConstructibleShift D l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShiftAdditive (E : Index l Ω) (n : ℤ) :
    (shiftFunctor (Stage D l hl Ω Y E) n).Additive :=
  rationalConstructibleShiftAdditive D l hl (Coefficient.{u} l Ω E) Y n

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stagePretriangulated (E : Index l Ω) :
    Pretriangulated (Stage D l hl Ω Y E) :=
  rationalConstructiblePretriangulated D l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTriangulated (E : Index l Ω) :
    IsTriangulated (Stage D l hl Ω Y E) :=
  rationalConstructibleTriangulated D l hl (Coefficient.{u} l Ω E) Y

/-- The actual finite-field scalar transition, with both coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transition (E L : Index l Ω) (h : E ≤ L) :
    Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L :=
  rationalScalarExtension D l hl (Coefficient.{u} l Ω E) Y
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The supplied scalar transition structure on the named rational stages.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).CommShift ℤ :=
  rationalConstructibleScalarCommShift D l hl (Coefficient.{u} l Ω E) Y
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The supplied scalar transition structure on the named rational stages.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionExact (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).IsTriangulated :=
  rationalConstructibleScalar_exact D l hl (Coefficient.{u} l Ω E) Y
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The supplied scalar transition structure on the named rational stages.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionAdditive (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).Additive :=
  rationalConstructibleScalar_additive D l hl (Coefficient.{u} l Ω E) Y
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The canonical scalar associator, with its tensor-generator normalization.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition D l hl Ω Y E L h ⋙ transition D l hl Ω Y L M k ≅
      transition D l hl Ω Y E M (h.trans k) :=
  rationalConstructibleScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω L M k) D hl ≪≫
    eqToIso (congrArg (rationalScalarExtension D l hl
      (Coefficient.{u} l Ω E) Y (Coefficient.{u} l Ω M))
      ((coefficientInclusion_laws l Ω).2 E L M h k))

/-- The normalized scalar unit, transported through the coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def unitor (E : Index l Ω) : transition D l hl Ω Y E E le_rfl ≅
    𝟭 (Stage D l hl Ω Y E) :=
  eqToIso (congrArg (rationalScalarExtension D l hl
    (Coefficient.{u} l Ω E) Y (Coefficient.{u} l Ω E))
    ((coefficientInclusion_laws l Ω).1 E)) ≪≫
    rationalConstructibleScalarUnit l (Coefficient.{u} l Ω E) Y D hl

/-- The coefficient fields form a directed order by the recorded compositum.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance indexDirected : IsDirectedOrder (Index l Ω) where
  directed E L := ⟨Padic.finiteCoefficientCompositum l Ω E L,
    (Padic.finiteCoefficientFields_properties l Ω).1 E L⟩

/-- The base coefficient field supplies a stage, including for the empty scheme.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance indexNonempty : Nonempty (Index l Ω) :=
  ⟨Padic.finiteCoefficientBase l Ω⟩

/-- The normalized tensor associators satisfy the stage-system cocycle.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: rationalConstructibleScalar_coherence proves the tensor pentagon. The small
coefficient inclusions compose by coefficientInclusion_laws. Substitution gives the
displayed cocycle, including repeated fields and identity inclusions. -/
theorem associator_cocycle (E L M N : Index l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) (K : Stage D l hl Ω Y E) :
    (transition D l hl Ω Y M N m).map ((associator D l hl Ω Y E L M h k).hom.app K) ≫
        (associator D l hl Ω Y E M N (h.trans k) m).hom.app K =
      (associator D l hl Ω Y L M N k m).hom.app
          ((transition D l hl Ω Y E L h).obj K) ≫
        (associator D l hl Ω Y E L N h (k.trans m)).hom.app K := by
  sorry

/-- The tensor transitions and associators uniquely determine the stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take T to be transition and assoc to be associator; associator_cocycle is
precisely the required coherence equation. Conversely the displayed equalities fix
all data fields of StageSystem; the remaining cocycle proof is proof irrelevant. -/
theorem stageSystem_existsUnique :
    ∃! S : StageSystem (Stage D l hl Ω Y),
      (∀ (E L : Index l Ω) (h : E ≤ L), S.T h = transition D l hl Ω Y E L h) ∧
      (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
        HEq (S.assoc h k) (associator D l hl Ω Y E L M h k)) := by
  sorry

/-- The stage system with exactly the specified tensor functors and associators.
It is chosen only from a theorem determining all its data uniquely.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageSystem : StageSystem (Stage D l hl Ω Y) :=
  (stageSystem_existsUnique D l hl Ω Y).exists.choose

/-- The existing tensor functor as a transition of the uniquely fixed stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageTransition (E L : Index l Ω) (h : E ≤ L) :=
  (stageSystem D l hl Ω Y).T h

/-- The specified shift comparison transported by equality of the transition functors.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).CommShift ℤ :=
  cast (congrArg (fun F : Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L ↦ F.CommShift ℤ)
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h).symm)
    (transitionCommShift D l hl Ω Y E L h)

/-- Exactness of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: stageSystem_existsUnique identifies this functor and its shift comparison
with the specified tensor extension. Apply rationalConstructibleScalar_exact. -/
@[instance]
theorem stageTransition_exact (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).IsTriangulated := by
  sorry

/-- Additivity of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: equality of functors with transition reduces the claim to transitionAdditive. -/
@[instance]
theorem stageTransition_additive (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).Additive := by
  sorry

/-- The upstream common-stage pair category, specialized to the specified rational stages.
Its objects are literal pairs, and no idempotents are adjoined.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Pair := (stageSystem D l hl Ω Y).PairCategory

/-- Cache the existing upstream category on the named concrete pair type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pairCategory : Category (Pair D l hl Ω Y) :=
  inferInstanceAs (Category (stageSystem D l hl Ω Y).PairCategory)

variable {D l hl Ω Y}

/-- The directed index of common finite coefficient overfields of two pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev Common (A B : Pair D l hl Ω Y) :=
  {L : Index l Ω // A.stage ≤ L ∧ B.stage ≤ L}

/-- Hom at one common coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def StageHom (A B : Pair D l hl Ω Y) (L : Common A B) :=
  ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
    (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj)

/-- Cache the abelian group of a stage Hom before forming the dependent colimit family.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageHomAddCommGroup (A B : Pair D l hl Ω Y) (L : Common A B) :
    AddCommGroup (StageHom A B L) :=
  inferInstanceAs (AddCommGroup
    ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
      (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj))

/-- Extend the representative and conjugate by the specified associators.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transport (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L) : StageHom A B M :=
  ((stageSystem D l hl Ω Y).assoc L.property.1 h).inv.app A.obj ≫
    (stageTransition D l hl Ω Y L.val M.val h).map f ≫
    ((stageSystem D l hl Ω Y).assoc L.property.2 h).hom.app B.obj

/-- Transport is additive and preserves zero.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: scalar extension is additive. Left and right composition by each fixed
associator component are additive by preadditivity of the rational target stage. -/
theorem transport_additive (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M) :
    transport A B L M h 0 = 0 ∧
      ∀ f g, transport A B L M h (f + g) =
        transport A B L M h f + transport A B L M h g := by
  sorry

/-- The transition homomorphism of the directed Hom system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transportHom (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M) :
    StageHom A B L →+ StageHom A B M where
  toFun := transport A B L M h
  map_zero' := (transport_additive A B L M h).1
  map_add' := (transport_additive A B L M h).2

/-- Decidable equality is used only to realize Mathlib's algebraic direct limit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDecidableEq (A B : Pair D l hl Ω Y) :
    DecidableEq (Common A B) := Classical.decEq _

/-- The actual abelian-group colimit, with no completion of its objects.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def ColimitHom (A B : Pair D l hl Ω Y) :=
  AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)

/-- The direct limit's abelian group structure, on the fixed Hom type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance colimitHomGroup (A B : Pair D l hl Ω Y) : AddCommGroup (ColimitHom A B) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)))

/-- The class of a map over a common finite coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def colimitOf (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : ColimitHom A B :=
  AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B) ⟨L, hA, hB⟩ f

/-- The upstream quotient Hom has exactly the stated abelian-colimit coordinates.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: send each common-stage representative to its direct-limit class. The tensor
cocycle and unit law make transport a directed system; the quotient relation is exactly
equality after extension. The direct-limit representative criterion therefore makes
this map well-defined and bijective. Every Hom is represented, proving uniqueness. -/
theorem homCoordinates_existsUnique (A B : Pair D l hl Ω Y) :
    ∃! e : (A ⟶ B) ≃ ColimitHom A B,
      ∀ (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (f : StageHom A B ⟨L, hA, hB⟩),
        e (StageSystem.PairCategory.mkHom L hA hB f) = colimitOf A B L hA hB f := by
  sorry

/-- The canonical Hom coordinates, fixed on every common-stage representative.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def homCoordinates (A B : Pair D l hl Ω Y) :=
  (homCoordinates_existsUnique A B).exists.choose

/-- The abelian group transported from the specified directed colimit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance homAddCommGroup (A B : Pair D l hl Ω Y) : AddCommGroup (A ⟶ B) :=
  (homCoordinates A B).addCommGroup

/-- The map represented at L, using the existing upstream quotient constructor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev ofHom (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : A ⟶ B :=
  StageSystem.PairCategory.mkHom L hA hB f

/-- The fixed composition is additive in each variable.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: represent the three maps at a common compositum. Colimit structure maps are
additive and stage composition is bilinear, giving both asserted equations. -/
theorem composition_bilinear :
    (∀ (A B C : Pair D l hl Ω Y) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : Pair D l hl Ω Y) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  sorry

/-- Preadditivity uses the actual colimit abelian groups.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance preadditive : Preadditive (Pair D l hl Ω Y) where
  homGroup A B := homAddCommGroup A B
  add_comp A B C f f' g := composition_bilinear.1 A B C f f' g
  comp_add A B C f g g' := composition_bilinear.2 A B C f g g'

/-- The existing upstream inclusion of the actual rational finite stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev inclusion (E : Index l Ω) : Stage D l hl Ω Y E ⥤ Pair D l hl Ω Y :=
  (stageSystem D l hl Ω Y).ι E

/-- The inclusion preserves the abelian-colimit addition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: inclusion sends f to its normalized representative, and homCoordinates sends
that representative to its direct-limit class. Both normalization by fixed unit
components and the direct-limit structure maps are additive. -/
@[instance]
theorem inclusion_additive (E : Index l Ω) : (inclusion E : Stage D l hl Ω Y E ⥤ _).Additive := by
  sorry

/-- Every class has a finite representative, and equality is equality at a later stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: composita make each common-overfield index nonempty and directed. The normalized
tensor unit and associator pentagon make transport an actual directed system. Apply
Mathlib's directed-colimit representation and zero-exactness criteria to the difference
of two representatives. This gives precisely equality after one further extension. -/
theorem representatives (A B : Pair D l hl Ω Y) :
    (∀ f : A ⟶ B, ∃ (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (u : StageHom A B ⟨L, hA, hB⟩), f = ofHom A B L hA hB u) ∧
    (∀ (L M : Common A B) (f : StageHom A B L) (g : StageHom A B M),
      ofHom A B L.val L.property.1 L.property.2 f =
          ofHom A B M.val M.property.1 M.property.2 g ↔
        ∃ (N : Common A B) (hL : L ≤ N) (hM : M ≤ N),
          transport A B L N hL f = transport A B M N hM g) := by
  sorry

/-- Stagewise object shift, with the coefficient field unchanged.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftPair (n : ℤ) (A : Pair D l hl Ω Y) : Pair D l hl Ω Y :=
  ⟨A.stage, (shiftFunctor (Stage D l hl Ω Y A.stage) n).obj A.obj⟩

/-- The shifted representative uses the prescribed scalar-extension shift comparison.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftRepresentative (n : ℤ) (A B : Pair D l hl Ω Y)
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) :
    StageHom (shiftPair n A) (shiftPair n B) ⟨L, hA, hB⟩ :=
  ((stageTransition D l hl Ω Y A.stage L hA).commShiftIso n).hom.app A.obj ≫
    (shiftFunctor (Stage D l hl Ω Y L) n).map f ≫
    ((stageTransition D l hl Ω Y B.stage L hB).commShiftIso n).inv.app B.obj

/-- The induced shift is specified on every object, representative and stage inclusion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: shift each finite representative using shiftRepresentative. Exact scalar
extension and associator compatibility with shifts make this independent of stage.
The finite-stage shift units and addition isomorphisms descend componentwise; equality
and coherence may be checked after moving the finite diagrams to a common field.
The inclusion comparisons are identities on the displayed shifted pairs. Thus these
formulas determine the functors and their coherent comparisons on the generators. -/
theorem shift_exists :
    ∃ s : HasShift (Pair D l hl Ω Y) ℤ,
      (fun [shiftInst : HasShift (Pair D l hl Ω Y) ℤ] ↦
        (∀ n : ℤ, (shiftFunctor (Pair D l hl Ω Y) n).Additive) ∧
        (∀ (n : ℤ) (A : Pair D l hl Ω Y),
          (shiftFunctor (Pair D l hl Ω Y) n).obj A = shiftPair n A) ∧
        (∀ (n : ℤ) (A B : Pair D l hl Ω Y) (L : Index l Ω)
          (hA : A.stage ≤ L) (hB : B.stage ≤ L) (f : StageHom A B ⟨L, hA, hB⟩),
          HEq ((shiftFunctor (Pair D l hl Ω Y) n).map (ofHom A B L hA hB f))
            (ofHom (shiftPair n A) (shiftPair n B) L hA hB
              (shiftRepresentative n A B L hA hB f))) ∧
        ∃ c : ∀ E : Index l Ω, (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ,
          (fun [commInst : ∀ E : Index l Ω,
              (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ] ↦
            ∀ (n : ℤ) (E : Index l Ω) (K : Stage D l hl Ω Y E),
              HEq (((inclusion E : Stage D l hl Ω Y E ⥤ _).commShiftIso n).hom.app K)
                (𝟙 ((inclusion E : Stage D l hl Ω Y E ⥤ _).obj
                  ((shiftFunctor (Stage D l hl Ω Y E) n).obj K)))) (commInst := c))
        (shiftInst := s) := by
  sorry

/-- The stagewise shift with the representative formula of shift_exists.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance hasShift : HasShift (Pair D l hl Ω Y) ℤ := shift_exists.choose

/-- Each induced integer shift is additive.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (Pair D l hl Ω Y) n).Additive := shift_exists.choose_spec.1 n

/-- The normalized exact-stage shift comparison, fixed to identity on shifted pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusionCommShift (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ :=
  shift_exists.choose_spec.2.2.2.choose E

/-- A stage zero object remains zero after forming directed Hom colimits.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take the zero object at the bottom coefficient field. Every transition is exact
and therefore preserves zero. At every common field its Hom groups to and from any
object vanish. Their directed colimits vanish, giving the zero-object universal property. -/
theorem zero_exists : HasZeroObject (Pair D l hl Ω Y) := by
  sorry

attribute [instance] zero_exists

/-- The canonical coefficient-stage identifications commute with shifts.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: on finite representatives this is scalar-extension shift compatibility and
rationalConstructibleScalar_coherence. The normalized inclusion comparisons are
identities on shifted pairs. The cocycle equation identifies both composites. -/
@[instance]
theorem transitionIso_commShift (E L : Index l Ω) (h : E ≤ L) :
    NatTrans.CommShift ((stageSystem D l hl Ω Y).transIso h).hom ℤ := by
  sorry

/-- The recorded common-stage distinguished-triangle criterion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Distinguished (T : Triangle (Pair D l hl Ω Y)) : Prop :=
  (stageSystem D l hl Ω Y).CommonStageDistinguished T

/-- The unique pretriangulation supplied by the common-stage Verdier theorem.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pretriangulated : Pretriangulated (Pair D l hl Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose

/-- The Verdier axiom for the specified common-stage triangles.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance isTriangulated : IsTriangulated (Pair D l hl Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose_spec.2.1

/-- Each actual rational finite-stage inclusion is exact.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusion_exact (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).IsTriangulated :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose_spec.2.2 E

/-- The triangle criterion, exposing the finite-field-of-definition clause.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: this is the distinguished-set clause of commonStage_verdier_existsUnique
for the actual scalar-extension stage system. -/
theorem distinguished_iff (T : Triangle (Pair D l hl Ω Y)) :
    T ∈ distTriang (Pair D l hl Ω Y) ↔ Distinguished T := by
  sorry

/-- A cone represented over L has the actual pair (L, C) as its third object.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: apply the exact inclusion at L to the given cone triangle. The normalized
scalar units and associators give canonical isomorphisms from the first two image
objects to A and B. Conjugate the three arrows by these isomorphisms and the shift
comparison; common-stage composition identifies the first with the stated class.
Its third object remains precisely (L, S.obj₃), and isomorphism closure gives the claim. -/
theorem commonStage_cone (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L) (u : StageHom A B ⟨L, hA, hB⟩)
    (S : Triangle (Stage D l hl Ω Y L)) (hS : S ∈ distTriang (Stage D l hl Ω Y L))
    (h₁ : S.obj₁ = (stageTransition D l hl Ω Y A.stage L hA).obj A.obj)
    (h₂ : S.obj₂ = (stageTransition D l hl Ω Y B.stage L hB).obj B.obj) (hu : HEq S.mor₁ u) :
    ∃ T : Triangle (Pair D l hl Ω Y),
      T.obj₁ = A ∧ T.obj₂ = B ∧ T.obj₃ = (inclusion L).obj S.obj₃ ∧
        HEq T.mor₁ (ofHom A B L hA hB u) ∧ T ∈ distTriang (Pair D l hl Ω Y) := by
  sorry

end AlgebraicallyClosedCoefficients

/-- The algebraically closed coefficient category is the pair category itself.
No Karoubi envelope occurs: its objects are finite-field pairs and its Hom groups are
canonically the displayed directed colimits. The companion declarations specify shift,
composition, common-stage distinguished triangles and the Verdier axioms.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev algebraicallyClosedConstructibleCategory
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  AlgebraicallyClosedCoefficients.Pair D l hl Ω Y

end WeilConjectures
