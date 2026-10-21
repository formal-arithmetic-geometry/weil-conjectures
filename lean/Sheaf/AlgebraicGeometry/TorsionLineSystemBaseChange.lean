/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.CategoryTheory.SheafificationTensorLocalIso

/-! # Normalized base change of compatible torsion systems

Source: Stacks Project, Modules on Sites, Tags 03EK, 03EL and 0GMW; the Finite A
paragraph of the blueprint det-prop-sfb-cartesian-coefficients-twists
(blueprint: lem-pur-torsion-line-system-base-change).

The scalar extension is the recorded sheafification of A tensor P. The function
`pure` takes its arguments in the order P, A, using the symmetry of the ordinary
commutative-ring tensor product. No local-freeness or rank hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtaleTensorComparison
open scoped ChangeOfRings

section IdentityCoordinates

set_option backward.isDefEq.respectTransparency false
universe v w
attribute [instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace CategoryTheory.InternalAbelianSheafModule

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]

/-- The internal module on precisely the original underlying abelian sheaf.
Source: Stacks 00YV
(blueprint: lem-pur-torsion-line-system-base-change). -/
def identitySectionModule
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) : Mod (Sheaf J AddCommGrpCat.{u}) R where
  X := (SheafOfModules.toSheaf _).obj M
  mod := by
    let e : (liftedSheafModule J R M).X ≅ (SheafOfModules.toSheaf _).obj M :=
      (SheafOfModules.toSheaf _).mapIso (sectionModuleFunctor_counit J R M)
    exact ModObj.ofIso (asIso (𝟙 R)) e

/-- The forward section functor recovers the original module with identity coordinates.
Source: Stacks 00YV
(blueprint: lem-pur-torsion-line-system-base-change).
Proof: the counit used in identitySectionModule is a module isomorphism. Conjugating
its internal action makes its section action the original action of M. Thus the
identity on each section is linear and natural, giving an isomorphism. Any other
isomorphism with the displayed formula has the same components and is equal to it. -/
theorem identitySectionCoordinates_exists
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) :
    ∃! e : (sectionModuleFunctor J R).obj (identitySectionModule J R M) ≅ M,
      ∀ (U : Cᵒᵖ) (x : M.val.obj U), e.hom.val.app U x = x := by
  sorry

/-- The uniquely identity-normalized coordinates, independent of a choice counit.
Source: Stacks 00YV
(blueprint: lem-pur-torsion-line-system-base-change). -/
def identitySectionCoordinates
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) :
    (sectionModuleFunctor J R).obj (identitySectionModule J R M) ≅ M :=
  Classical.choose (identitySectionCoordinates_exists J R M)

/-- Interpret a sectionwise map internally through the fixed identity coordinates.
Source: Stacks 00YV
(blueprint: lem-pur-torsion-line-system-base-change). -/
def identitySectionModuleMap
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))} (m : M ⟶ N) :
    identitySectionModule J R M ⟶ identitySectionModule J R N :=
  (sectionModuleFunctor_fullyFaithful J R).preimage
    ((identitySectionCoordinates J R M).hom ≫ m ≫ (identitySectionCoordinates J R N).inv)

/-- The internal arrow is exactly the original abelian-sheaf map, without counits.
Source: Stacks 00YV
(blueprint: lem-pur-torsion-line-system-base-change).
Proof: the forward functor leaves the underlying map unchanged. Its fully faithful
preimage therefore has the underlying composite of the two coordinates and m.
Both coordinate maps are identity on every section, so this composite equals m. -/
theorem identitySectionModuleMap_hom
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))} (m : M ⟶ N) :
    (identitySectionModuleMap J R m).hom = (SheafOfModules.toSheaf _).map m := by
  sorry

end CategoryTheory.InternalAbelianSheafModule

end IdentityCoordinates

namespace AlgebraicGeometry.ProEtaleTorsionSystem

/-- The constant sheaf of a coefficient ring, using the recorded sheafification.
Source: Stacks 0H7J (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev constant (T : Scheme.{u}) (A : CommRingCat.{u + 1}) : Rings T :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).obj A

/-- The canonical map on constant ring sheaves.
Source: Stacks 0H7J (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev constantMap (T : Scheme.{u}) {A B : CommRingCat.{u + 1}} (v : A ⟶ B) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map v

/-- The lifted residue ring, retaining the coefficient universe of the small site.
Source: the Finite A paragraph (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev residue (ell : ℕ) (r : ℕ+) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (ZMod (ell ^ (r : ℕ))))

/-- The canonical reduction of residue rings.
Source: the Finite A paragraph (blueprint: lem-pur-torsion-line-system-base-change). -/
def reduction (ell : ℕ) {s r : ℕ+} (hrs : r ≤ s) : residue.{u} ell s ⟶ residue ell r :=
  CommRingCat.ofHom ((ULift.ringEquiv.symm.toRingHom.comp
    (ZMod.castHom (pow_dvd_pow ell hrs) (ZMod (ell ^ (r : ℕ))))).comp
      ULift.ringEquiv.toRingHom)

/-- A finite coefficient ring with its positive annihilating exponent; the zero ring is
allowed. This merely bundles the pairs (r,A) quantified in the statement.
Source: the Finite A paragraph (blueprint: lem-pur-torsion-line-system-base-change). -/
structure Coefficient (ell : ℕ) where
  exponent : ℕ+
  ring : CommRingCat.{u + 1}
  [finite : Finite ring]
  killed : ((ell ^ (exponent : ℕ) : ℕ) : ring) = 0

/-- The unique unital scalar map, not an unspecified algebra structure.
Source: Stacks 03EK (blueprint: lem-pur-torsion-line-system-base-change). -/
def Coefficient.scalar {ell : ℕ} (a : Coefficient.{u} ell) :
    residue ell a.exponent ⟶ a.ring :=
  CommRingCat.ofHom ((ZMod.castHom (ringChar.dvd a.killed) a.ring).comp
    ULift.ringEquiv.toRingHom)

/-- Scalar extension is the existing sectionwise tensor followed by sheafification.
Source: Stacks 03EK (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev extend {T : Scheme.{u}} {R S : Rings T} (a : R ⟶ S) (M : Modules R) :
    Modules S := SheafOfModules.changeOfRings.{u, u + 1, u + 1} a M

set_option backward.isDefEq.respectTransparency false in
/-- The actual sheafification-unit pure tensor x tensor a, represented as a tensor x.
Source: Stacks 03EK and 0GMW (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def pure {T : Scheme.{u}} {R S : Rings T} (a : R ⟶ S) (M : Modules R)
    (V : T.ProEt) (x : M.val.obj (op V)) (b : S.obj.obj (op V)) :
    (extend a M).val.obj (op V) :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    (𝟙 _)).unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M)).app (op V))
      (b ⊗ₜ[R.obj.obj (op V), (a.hom.app (op V)).hom] x)

set_option backward.isDefEq.respectTransparency false in
/-- The hypotheses on one of the two compatible torsion systems. The final field
specifies the induced reduction map itself by its pure-tensor formula.
Source: the Finite A paragraph (blueprint: lem-pur-torsion-line-system-base-change). -/
structure System (ell : ℕ) (T : Scheme.{u}) where
  obj : (r : ℕ+) → Modules (constant T (residue ell r))
  q : ∀ (s r : ℕ+) (hrs : r ≤ s), obj s ⟶
    (restrict (constantMap T (reduction ell hrs))).obj (obj r)
  identity : ∀ (r : ℕ+) (V : T.ProEt) (x : (obj r).val.obj (op V)),
    (q r r le_rfl).val.app (op V) x = x
  composition : ∀ (s r t : ℕ+) (hrs : r ≤ s) (htr : t ≤ r)
    (V : T.ProEt) (x : (obj s).val.obj (op V)),
    (q r t htr).val.app (op V) ((q s r hrs).val.app (op V) x) =
      (q s t (htr.trans hrs)).val.app (op V) x
  reduction_iso : ∀ (s r : ℕ+) (hrs : r ≤ s),
    ∃ e : extend (constantMap T (reduction ell hrs)) (obj s) ≅ obj r,
      ∀ (V : T.ProEt) (x : (obj s).val.obj (op V))
        (b : (constant T (residue ell r)).obj.obj (op V)),
        e.hom.val.app (op V) (pure (constantMap T (reduction ell hrs)) (obj s) V x b) =
          b • (@id ((obj r).val.obj (op V)) ((q s r hrs).val.app (op V) x))

/-- The module P_T(A;r), with its actual A-action.
Source: Stacks 03EK (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev extension {ell : ℕ} {T : Scheme.{u}} (P : System ell T) (a : Coefficient ell) :=
  extend (constantMap T a.scalar) (P.obj a.exponent)

/-- The canonical constant-section comparison, in the commutative-ring presentation.
Source: Stacks 0H7J and 09A5 (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev gamma {X Y : Scheme.{u}} (h : X ⟶ Y) (A : CommRingCat.{u + 1}) :=
  proEtaleConstantInverseImageMap h CommRingCat.{u + 1} A

/-- The underlying set-sheaf map of a semilinear inverse-image module map. The source
identification is the existing, adjunction-unit-normalized one.
Source: Stacks 00YV and 03D2 (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def underlyingBaseMap {X Y : Scheme.{u}} (h : X ⟶ Y) (A : CommRingCat.{u + 1})
    (M : Modules (constant Y A)) (N : Modules (constant X A))
    (c : (inverse h (constant Y A)).obj M ⟶ (restrict (gamma h A)).obj N) :
    (AlgebraicGeometry.ProEtale.setPullback h).obj (moduleSets M) ⟶ moduleSets N :=
  (moduleSetsIdentification h M).hom ≫ moduleMapSets c

/-- A transition between arbitrary exponents and finite scalar rings is determined
uniquely by x tensor a mapped to q(x) tensor v(a).
Source: Stacks 03EK and 0GMW, node proof step 4
(blueprint: lem-pur-torsion-line-system-base-change).
Proof: the formula is balanced since q is semilinear for residue reduction and the
unital map v commutes with the residue scalars. The bilinear universal property and
module sheafification give the map; the same universal property gives uniqueness. -/
theorem transition_exists {ell : ℕ} {T : Scheme.{u}} (P : System ell T)
    (a b : Coefficient ell) (hrs : b.exponent ≤ a.exponent) (v : a.ring ⟶ b.ring) :
    ∃! d : extension P a ⟶ (restrict (constantMap T v)).obj (extension P b),
      ∀ (V : T.ProEt) (x : (P.obj a.exponent).val.obj (op V))
        (z : (constant T a.ring).obj.obj (op V)),
        d.val.app (op V) (pure (constantMap T a.scalar) (P.obj a.exponent) V x z) =
          pure (constantMap T b.scalar) (P.obj b.exponent) V
            ((P.q a.exponent b.exponent hrs).val.app (op V) x)
            ((constantMap T v).hom.app (op V) z) := by
  sorry

/-- The specified diagram arrow; uniqueness, rather than mere existence, fixes its data.
Source: Stacks 03EK (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def transition {ell : ℕ} {T : Scheme.{u}} (P : System ell T)
    (a b : Coefficient ell) (hrs : b.exponent ≤ a.exponent) (v : a.ring ⟶ b.ring) :
    extension P a ⟶ (restrict (constantMap T v)).obj (extension P b) :=
  Classical.choose (transition_exists P a b hrs v)

/-- The actual underlying set-sheaf transition, with both endpoints explicit.
Source: Stacks 03EK (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def transitionSets {ell : ℕ} {T : Scheme.{u}} (P : System ell T)
    (a b : Coefficient ell) (hrs : b.exponent ≤ a.exponent) (v : a.ring ⟶ b.ring) :
    moduleSets (extension P a) ⟶ moduleSets (extension P b) :=
  moduleMapSets (transition P a b hrs v)

/-- The normalized comparison is uniquely specified on inverse images of local pure
tensors; its type expresses semilinearity over the canonical gamma_A.
Source: Stacks 03EL and 0GMW, node proof steps 1--3
(blueprint: lem-pur-torsion-line-system-base-change).
Proof: naturality of constant-section comparisons identifies the scalar square.
Apply lem-pur-proetale-inverse-image-tensor-comparison to P and the coefficient
sheaf, then tensor c with gamma. Tensoring the inverses gives the inverse.
For uniqueness, take adjoints and use lem-pc-sites-sheaf-tensor-bilinear-universal;
this tests the original pure tensors, without assuming all inverse-image sections
are individual unit sections. -/
def IsNormalized {ell : ℕ} {X Y : Scheme.{u}} (h : X ⟶ Y)
    (PX : System ell X) (PY : System ell Y)
    (c : ∀ r : ℕ+, (inverse h (constant Y (residue ell r))).obj (PY.obj r) ≅
      (restrict (gamma h (residue ell r))).obj (PX.obj r))
    (a : Coefficient ell)
    (e : (inverse h (constant Y a.ring)).obj (extension PY a) ≅
      (restrict (gamma h a.ring)).obj (extension PX a)) : Prop :=
  ∀ (V : Y.ProEt) (x : (PY.obj a.exponent).val.obj (op V))
    (z : (constant Y a.ring).obj.obj (op V)),
    e.hom.val.app (op ((proEtaleBaseChange h).obj V))
      (inverseSection h (extension PY a) V
        (pure (constantMap Y a.scalar) (PY.obj a.exponent) V x z)) =
    pure (constantMap X a.scalar) (PX.obj a.exponent)
      ((proEtaleBaseChange h).obj V)
      ((c a.exponent).hom.val.app (op ((proEtaleBaseChange h).obj V))
        (inverseSection h (PY.obj a.exponent) V x))
      ((gamma h a.ring).hom.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app
          (constant Y a.ring)).hom.app (op V) z))

/-- Existence and uniqueness of the pure-tensor-normalized isomorphism.
Source: Stacks 03EL and 0GMW; node proof steps 1--3
(blueprint: lem-pur-torsion-line-system-base-change).
Proof: tensor the recorded inverse-image comparison with c and gamma. Tensoring
inverses gives its inverse. For uniqueness take adjoints, use the bilinear
universal property on every original local pure tensor, and take adjoints back. -/
theorem comparison_exists {ell : ℕ} {X Y : Scheme.{u}} (h : X ⟶ Y)
    (PX : System ell X) (PY : System ell Y)
    (c : ∀ r : ℕ+, (inverse h (constant Y (residue ell r))).obj (PY.obj r) ≅
      (restrict (gamma h (residue ell r))).obj (PX.obj r))
    (a : Coefficient ell) :
    ∃! e : (inverse h (constant Y a.ring)).obj (extension PY a) ≅
        (restrict (gamma h a.ring)).obj (extension PX a),
      IsNormalized h PX PY c a e := by
  sorry

/-- C_{A,r} is chosen from its unique normalized characterization.
Source: Stacks 03EL (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def comparison {ell : ℕ} {X Y : Scheme.{u}} (h : X ⟶ Y)
    (PX : System ell X) (PY : System ell Y)
    (c : ∀ r : ℕ+, (inverse h (constant Y (residue ell r))).obj (PY.obj r) ≅
      (restrict (gamma h (residue ell r))).obj (PX.obj r))
    (a : Coefficient ell) :
    (inverse h (constant Y a.ring)).obj (extension PY a) ≅
      (restrict (gamma h a.ring)).obj (extension PX a) :=
  Classical.choose (comparison_exists h PX PY c a)

/-- Changing only the exponent retains the same ring and its canonical scalar map.
Source: the Finite A paragraph (blueprint: lem-pur-torsion-line-system-base-change). -/
def Coefficient.atExponent {ell : ℕ} (a : Coefficient.{u} ell) (r : ℕ+)
    (hr : ((ell ^ (r : ℕ) : ℕ) : a.ring) = 0) : Coefficient ell :=
  { exponent := r, ring := a.ring, finite := a.finite, killed := hr }

/-- The diagram identities and the invertibility of the specified exponent changes.
Source: Stacks 03EK and 0GMW; node proof steps 4--6
(blueprint: lem-pur-torsion-line-system-base-change). -/
def DiagramLaws {ell : ℕ} {T : Scheme.{u}} (P : System ell T) : Prop :=
  (∀ a : Coefficient ell,
    transitionSets P a a le_rfl (𝟙 a.ring) = 𝟙 (moduleSets (extension P a))) ∧
  (∀ (a b d : Coefficient ell) (hab : b.exponent ≤ a.exponent)
    (hbd : d.exponent ≤ b.exponent) (v : a.ring ⟶ b.ring) (w : b.ring ⟶ d.ring),
    transitionSets P a d (hbd.trans hab) (v ≫ w) =
      transitionSets P a b hab v ≫ transitionSets P b d hbd w) ∧
  (∀ (a : Coefficient ell) (r : ℕ+) (hrs : r ≤ a.exponent)
    (hr : ((ell ^ (r : ℕ) : ℕ) : a.ring) = 0),
    IsIso (transition P a (a.atExponent r hr) hrs (𝟙 a.ring)))

/-- The actual abelian sheaf underlying R, with the existing internal ring structure.
Source: Stacks 00YV (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev internalRing {T : Scheme.{u}} (R : Rings T) :
    Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  (sheafCompose (ProEt.topology T) (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The internal ring reconstructed from a commutative ring sheaf is commutative.
Source: Stacks 00YV; node proof step 8
(blueprint: lem-pur-torsion-line-system-base-change).
Proof: apply Sheaf.isCommMonObj_sheafCompose_obj to the underlying ring sheaf;
its sectionwise multiplication is commutative since every R(U) is commutative. -/
instance internalRing_comm {T : Scheme.{u}} (R : Rings T) :
    IsCommMonObj (internalRing R) :=
  Sheaf.isCommMonObj_sheafCompose_obj (ProEt.topology T)
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (fun V a b ↦ @mul_comm (R.obj.obj V) _ a b)

/-- Reconstructing sections of the internal ring has its unique identity-on-sections
ring isomorphism to the original ring sheaf. This determines all coordinate data.
Source: Stacks 00YV; node proof step 8
(blueprint: lem-pur-torsion-line-system-base-change).
Proof: the existing internal ring structure is transported from the sheafification
of the original ring presheaf. Naturality of its counit says its sectionwise
multiplication and unit are the original multiplication and unit. The identity
on each section group is therefore a ring isomorphism, natural in the site object.
Any isomorphism with the stated section formula is the same sheaf morphism. -/
theorem sectionCoordinates_exists {T : Scheme.{u}} (R : Rings T) :
    ∃! e : CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (ProEt.topology T) (internalRing R) ≅ R,
      ∀ (V : T.ProEt) (a : R.obj.obj (op V)), e.hom.hom.app (op V) a = a := by
  sorry

/-- The canonical ring coordinates, fixed by identity on all local sections.
Source: Stacks 00YV (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def sectionCoordinates {T : Scheme.{u}} (R : Rings T) :
    CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (ProEt.topology T) (internalRing R) ≅ R :=
  Classical.choose (sectionCoordinates_exists R)

/-- Interpret the module on its actual underlying abelian sheaf, using identity
ring coordinates and the identity-normalized inverse section functor.
Source: Stacks 00YV (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev internalModule {T : Scheme.{u}} {R : Rings T} (M : Modules R) :
    Mod (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) (internalRing R) :=
  CategoryTheory.InternalAbelianSheafModule.identitySectionModule
    (ProEt.topology T) (internalRing R) ((restrict (sectionCoordinates R).hom).obj M)

/-- The internal arrow through fixed identity coordinates on the underlying sheaves.
Source: Stacks 00YV (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def internalMap {T : Scheme.{u}} {R : Rings T} {M N : Modules R} (m : M ⟶ N) :
    internalModule M ⟶ internalModule N :=
  CategoryTheory.InternalAbelianSheafModule.identitySectionModuleMap
    (ProEt.topology T) (internalRing R) ((restrict (sectionCoordinates R).hom).map m)

/-- The coefficient sheaf with its actual action restricted to the residue ring.
Source: Stacks 03EK (blueprint: lem-pur-torsion-line-system-base-change). -/
abbrev scalarModule {T : Scheme.{u}} {R S : Rings T} (a : R ⟶ S) : Modules R :=
  (restrict a).obj (SheafOfModules.unit
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))

/-- The actual internal relative tensor, named to keep its coequalizer construction
opaque while elaborating the normalized comparison and local formulas.
Source: Stacks 03EK (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def internalExtensionTensor {T : Scheme.{u}} {R S : Rings T}
    (a : R ⟶ S) (M : Modules R) :
    Mod (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) (internalRing R) :=
  internalModule M ⊗ internalModule (scalarModule a)

set_option backward.isDefEq.respectTransparency false in
/-- The internal coequalizer pairing in the named tensor, with unchanged sections.
Source: Stacks 03EK (blueprint: lem-pur-torsion-line-system-base-change). -/
def internalExtensionTmul {T : Scheme.{u}} {R S : Rings T}
    (a : R ⟶ S) (M : Modules R) (V : T.ProEt)
    (x : M.val.obj (op V)) (b : S.obj.obj (op V)) :
    (internalExtensionTensor a M).X.obj.obj (op V) := by
  let : IsCommMonObj (internalRing R) := internalRing_comm R
  unfold internalExtensionTensor
  exact CategoryTheory.InternalAbelianSheafModule.comparison_internalTmul
    (ProEt.topology T) (internalRing R)
    (internalModule M) (internalModule (scalarModule a)) (op V) x b

/-- The internal tensor has a unique comparison to ordinary scalar extension, fixed
on the internal coequalizer pure tensors, not merely up to an unspecified iso.
Source: Stacks 03EK and 0GMW; node proof step 8
(blueprint: lem-pur-torsion-line-system-base-change).
Proof: apply internal_section_tensor_comparison to internalModule M and internalModule
(scalarModule a). Its comparison_internalTmul normalization identifies the internal
pairing with the sectionwise balanced pairing. The identity section coordinates
preserve both factors. The bilinear and sheafification universal properties then
identify this tensor with changeOfRings a M, reversing the two factors by symmetry.
The inverse sends a tensor x to x tensor a; these maps are inverse on local pure
tensors. Uniqueness follows from the coequalizer and sheafification universal
properties. This also identifies the additional S-action on the second factor. -/
theorem internalExtensionComparison_exists {T : Scheme.{u}} {R S : Rings T}
    (a : R ⟶ S) (M : Modules R) :
    ∃! e : (internalExtensionTensor a M).X ≅
        (SheafOfModules.toSheaf _).obj (extend a M),
      ∀ (V : T.ProEt) (x : M.val.obj (op V)) (b : S.obj.obj (op V)),
        e.hom.hom.app (op V)
          (internalExtensionTmul a M V x b) =
          pure a M V x b := by
  sorry

/-- The uniquely normalized internal tensor comparison for scalar extension.
Source: Stacks 03EK and 0GMW (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def internalExtensionComparison {T : Scheme.{u}} {R S : Rings T}
    (a : R ⟶ S) (M : Modules R) :
    (internalExtensionTensor a M).X ≅
      (SheafOfModules.toSheaf _).obj (extend a M) :=
  Classical.choose (internalExtensionComparison_exists a M)

/-- An internal coequalizer pure tensor in the fixed scalar-extension coordinates.
The normalization in internalExtensionComparison_exists fixes these coordinates.
Source: Stacks 03EK and 0GMW (blueprint: lem-pur-torsion-line-system-base-change). -/
@[irreducible] def internalPure {T : Scheme.{u}} {R S : Rings T} (a : R ⟶ S) (M : Modules R)
    (V : T.ProEt) (x : M.val.obj (op V)) (b : S.obj.obj (op V)) :
    (extend a M).val.obj (op V) :=
  (internalExtensionComparison a M).hom.hom.app (op V)
    (internalExtensionTmul a M V x b)

/-- The specific internal comparison C has the same abelian map under the fixed
identity identifications, and sends internal pure tensors to c(x) tensor gamma(a).
Source: Stacks 00YV, 03EL and 0GMW; node proof step 8
(blueprint: lem-pur-torsion-line-system-base-change). -/
def InternalComparisonAgreement {ell : ℕ} {X Y : Scheme.{u}} (h : X ⟶ Y)
    (PX : System ell X) (PY : System ell Y)
    (c : ∀ r : ℕ+, (inverse h (constant Y (residue ell r))).obj (PY.obj r) ≅
      (restrict (gamma h (residue ell r))).obj (PX.obj r))
    (a : Coefficient ell) : Prop :=
  (internalMap (comparison h PX PY c a).hom).hom =
    (SheafOfModules.toSheaf _).map (comparison h PX PY c a).hom ∧
  ∀ (V : Y.ProEt) (x : (PY.obj a.exponent).val.obj (op V))
    (z : (constant Y a.ring).obj.obj (op V)),
    (internalMap (comparison h PX PY c a).hom).hom.hom.app
      (op ((proEtaleBaseChange h).obj V))
      (inverseSection h (extension PY a) V
        (internalPure (constantMap Y a.scalar) (PY.obj a.exponent) V x z)) =
    internalPure (constantMap X a.scalar) (PX.obj a.exponent)
      ((proEtaleBaseChange h).obj V)
      ((c a.exponent).hom.val.app (op ((proEtaleBaseChange h).obj V))
        (inverseSection h (PY.obj a.exponent) V x))
      ((gamma h a.ring).hom.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app
          (constant Y a.ring)).hom.app (op V) z))

/-- The specific internal mixed transition has the same abelian map under identity
identifications, and sends internal pure tensors to q(x) tensor v(a).
Source: Stacks 00YV, 03EK and 0GMW; node proof step 8
(blueprint: lem-pur-torsion-line-system-base-change). -/
def InternalTransitionAgreement {ell : ℕ} {T : Scheme.{u}} (P : System ell T)
    (a b : Coefficient ell) (hrs : b.exponent ≤ a.exponent) (v : a.ring ⟶ b.ring) : Prop :=
  (internalMap (transition P a b hrs v)).hom =
    (SheafOfModules.toSheaf _).map (transition P a b hrs v) ∧
  ∀ (V : T.ProEt) (x : (P.obj a.exponent).val.obj (op V))
    (z : (constant T a.ring).obj.obj (op V)),
    (internalMap (transition P a b hrs v)).hom.hom.app (op V)
      (internalPure (constantMap T a.scalar) (P.obj a.exponent) V x z) =
    internalPure (constantMap T b.scalar) (P.obj b.exponent) V
      ((P.q a.exponent b.exponent hrs).val.app (op V) x)
      ((constantMap T v).hom.app (op V) z)

/-- Normalized base change of compatible torsion systems, simultaneously for all finite
coefficients and positive exponents, including mixed coefficient/exponent transitions.
Source: Stacks 03EK, 03EL and 0GMW; the blueprint Finite A paragraph
(blueprint: lem-pur-torsion-line-system-base-change).
Proof:
1. The constant-presheaf sheafification universal property makes gamma natural in
all unital coefficient maps and residue reductions.
2. The tensor comparison of lem-pur-proetale-inverse-image-tensor-comparison,
followed by c tensor gamma, gives comparison_exists and its inverse and formula.
3. Adjunction and lem-pc-sites-sheaf-tensor-bilinear-universal prove uniqueness by
original local pure tensors, rather than arbitrary inverse-image sections.
4. The balanced formula in transition_exists defines every mixed transition.
Identity and composition follow by evaluating on pure tensors and tensor uniqueness.
5. Reassociation sends x tensor a to (x tensor 1) tensor a; its inverse sends
(x tensor b) tensor a to x tensor ba. Two applications of tensor uniqueness prove
that these maps are inverses.
6. Tensor the assumed reduction isomorphism with A. The resulting isomorphism has
exactly the exponent-transition formula, proving that specified arrow invertible.
7. On an original pure tensor the transition square compares c_r(q_Y(x)) with
q_X(c_s(x)), and gamma_B(v(a)) with v(gamma_A(a)). The assumed square and step 1
identify these factors. Step 3 proves equality of sheaf maps. The invertible
components and these squares give an isomorphism of varying-scalar diagrams.
8. Use sk-def-sfb-sheaf-tensor and det-def-sfb-sheaf-tensor-local-iso, then
lem-pe-internal-section-tensor-comparison. Its normalized tensor comparison fixes
pure tensors, including the extra A-action on the coefficient factor. The
identity-normalized inverse section functor puts every internal module on
its original underlying abelian sheaf. Full faithfulness through identity section
coordinates gives internalMap with precisely the original abelian map, with no
counit in the asserted equality. internalExtensionComparison identifies internal
coequalizer pure tensors with ordinary scalar-extension pure tensors. Apply the
normalization of C and D to obtain InternalComparisonAgreement and
InternalTransitionAgreement, including the displayed c tensor gamma and q tensor v
formulas. Equality of underlying maps also preserves the already proved squares.
-/
theorem torsion_line_system_base_change (ell : ℕ) (_hell : ell.Prime)
    {X Y : Scheme.{u}} (h : X ⟶ Y) (PX : System ell X) (PY : System ell Y)
    (c : ∀ r : ℕ+, (inverse h (constant Y (residue ell r))).obj (PY.obj r) ≅
      (restrict (gamma h (residue ell r))).obj (PX.obj r))
    (_hc : ∀ (s r : ℕ+) (hrs : r ≤ s),
      (AlgebraicGeometry.ProEtale.setPullback h).map (moduleMapSets (PY.q s r hrs)) ≫
          underlyingBaseMap h (residue ell r) (PY.obj r) (PX.obj r) (c r).hom =
        underlyingBaseMap h (residue ell s) (PY.obj s) (PX.obj s) (c s).hom ≫
          moduleMapSets (PX.q s r hrs)) :
    (∀ (a b : Coefficient ell) (hrs : b.exponent ≤ a.exponent) (v : a.ring ⟶ b.ring),
      (AlgebraicGeometry.ProEtale.setPullback h).map
          (transitionSets PY a b hrs v) ≫
        underlyingBaseMap h b.ring (extension PY b) (extension PX b)
          (comparison h PX PY c b).hom =
      underlyingBaseMap h a.ring (extension PY a) (extension PX a)
          (comparison h PX PY c a).hom ≫ transitionSets PX a b hrs v) ∧
    (DiagramLaws PX ∧ DiagramLaws PY) ∧
    (∀ a : Coefficient ell, IsNormalized h PX PY c a (comparison h PX PY c a) ∧
      ∀ e : (inverse h (constant Y a.ring)).obj (extension PY a) ≅
          (restrict (gamma h a.ring)).obj (extension PX a),
        IsNormalized h PX PY c a e → e = comparison h PX PY c a) ∧
    (∀ a : Coefficient ell, IsIso (underlyingBaseMap h a.ring
      (extension PY a) (extension PX a) (comparison h PX PY c a).hom)) ∧
    (∀ a : Coefficient ell, InternalComparisonAgreement h PX PY c a) ∧
    ((∀ (a b : Coefficient ell) (hrs : b.exponent ≤ a.exponent) (v : a.ring ⟶ b.ring),
      InternalTransitionAgreement PX a b hrs v) ∧
    (∀ (a b : Coefficient ell) (hrs : b.exponent ≤ a.exponent) (v : a.ring ⟶ b.ring),
      InternalTransitionAgreement PY a b hrs v)) := by
  sorry

end AlgebraicGeometry.ProEtaleTorsionSystem
