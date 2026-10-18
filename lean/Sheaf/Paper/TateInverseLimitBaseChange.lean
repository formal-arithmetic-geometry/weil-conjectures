/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.Paper.PurInverseImageTensorHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.NumberTheory.Padics.RingHoms
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.Paper.StrictTowerOperations
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

/-!
# Base change of an inverse-limit tower and its finite tensor reduction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, final sentence;
Stacks Project, Tags 03DB, 03CO and 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).

The index `op r` denotes the positive level `r + 1`. Scalar extension is the
recorded sheaf tensor construction, with its pure tensors written in the order `a ⊗ x`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The actual constant-coefficient module category.
Source: Stacks Tag 03DB (blueprint: lem-pur-tate-inverse-limit-base-change). -/
abbrev tateModules (T : Scheme.{u}) (R : Type u) [CommRing R] :=
  proEtaleRingModules T (proEtaleConstantRing T R)

/-- The constant sheaf map induced by a coefficient homomorphism.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateConstantMap (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : proEtaleConstantRing T R ⟶ proEtaleConstantRing T A :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (f.comp ULift.ringEquiv.toRingHom)))

/-- Restriction along the indicated constant coefficient map, with unchanged sections.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateRestrict (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : tateModules T A ⥤ tateModules T R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (tateConstantMap T f))

/-- The sheaf tensor `M ⊗_R A_T`, with its natural A-module structure.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTensor (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M : tateModules T R) : tateModules T A :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (tateConstantMap T f) M

/-- A pure tensor in the sheaf tensor, using the module sheafification unit.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTmul {T : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M : tateModules T R) (U : T.ProEt)
    (a : (proEtaleConstantRing T A).obj.obj (op U)) (x : M.val.obj (op U)) :
    (tateTensor T f M).val.obj (op U) :=
  purScalarSection (proEtaleConstantRing T R) (proEtaleConstantRing T A)
    (tateConstantMap T f) M U a x

/-- Inverse image, transported through the stipulated canonical constant-ring isomorphism.
Source: Stacks Tags 03D2 and 09A5
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePullback {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] : tateModules T R ⥤ tateModules T' R :=
  proEtaleRingModulePullback h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
    (asIso (proEtaleCoefficientInverseImageMap h R))

/-- The canonical inverse-image unit on local module sections.
Source: Stacks Tags 03D2 and 09A5
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateUnit {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] (M : tateModules T R)
    (U : T.ProEt) (x : M.val.obj (op U)) :
    ((tatePullback h R).obj M).val.obj (op ((proEtaleBaseChange h).obj U)) :=
  ((proEtaleRingModuleAdjunction h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
    (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U) x

/-- A tower is killed at positive level `r + 1`, sectionwise.
Source: Stacks Tag 03CO (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def TateTowerKilled (l : ℕ) {T : Scheme.{u}} {R : Type u} [CommRing R]
    (F : ℕᵒᵖ ⥤ tateModules T R) : Prop :=
  ∀ (r : ℕ) (U : T.ProEt) (x : (F.obj (op r)).val.obj (op U)),
    (l ^ (r + 1)) • x = 0

/-- The limit comparison is the universal limit comparison followed by the level maps.
It does not assert that inverse image preserves an infinite limit.
Source: Stacks Tags 03DB and 03CO
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateLimitMap {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    (F : ℕᵒᵖ ⥤ tateModules T R) (F' : ℕᵒᵖ ⥤ tateModules T' R)
    (β : F ⋙ tatePullback h R ≅ F') :
    (tatePullback h R).obj (limit F) ⟶ limit F' :=
  limit.post F (tatePullback h R) ≫ limMap β.hom

/-- Compatible level isomorphisms induce exactly one linear limit comparison.
Source: Stacks Tags 03DB and 03CO
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: apply inverse image to the source limit cone and postcompose with β.
Naturality of β gives the cone equations. The target limit gives the map, and its
jointly monic coordinate projections give uniqueness. This is proof steps 1--3. -/
theorem tateInverseLimitBaseChange (l : ℕ) [Fact l.Prime]
    {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (PadicInt l)))]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l)))
    (F' : ℕᵒᵖ ⥤ tateModules T' (ULift.{u} (PadicInt l)))
    (hF : TateTowerKilled l F) (hF' : TateTowerKilled l F')
    (β : F ⋙ tatePullback h (ULift.{u} (PadicInt l)) ≅ F') :
    (∀ r : ℕ,
      tateLimitMap h _ F F' β ≫ limit.π F' (op r) =
        (tatePullback h _).map (limit.π F (op r)) ≫ β.hom.app (op r)) ∧
    ∀ c : (tatePullback h _).obj (limit F) ⟶ limit F',
      (∀ r : ℕ, c ≫ limit.π F' (op r) =
        (tatePullback h _).map (limit.π F (op r)) ≫ β.hom.app (op r)) →
      c = tateLimitMap h _ F F' β := by
  sorry

/-- The constant-ring unit on sections, before extending the module scalars.
Source: Stacks Tag 09A5 (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateRingUnit {T T' : Scheme.{u}} (h : T' ⟶ T) (A : Type u) [CommRing A]
    (U : T.ProEt) (a : (proEtaleConstantRing T A).obj.obj (op U)) :
    (proEtaleConstantRing T' A).obj.obj (op ((proEtaleBaseChange h).obj U)) :=
  (proEtaleCoefficientDirectImageMap h A).hom.app (op U) a

/-- The pure-tensor normalization of `c ⊗ 1` under canonical inverse-image transport.
Source: Stacks Tag 03EL (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def IsTateTensorMap {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M')
    (b : (tatePullback h A).obj (tateTensor T φ M) ⟶ tateTensor T' φ M') : Prop :=
  ∀ (U : T.ProEt) (a : (proEtaleConstantRing T A).obj.obj (op U))
    (x : M.val.obj (op U)),
    b.val.app (op ((proEtaleBaseChange h).obj U))
        (tateUnit h A (tateTensor T φ M) U (tateTmul φ M U a x)) =
      tateTmul φ M' ((proEtaleBaseChange h).obj U) (tateRingUnit h A U a)
        (c.val.app (op ((proEtaleBaseChange h).obj U)) (tateUnit h R M U x))

/-- Canonical tensor transport followed by `c ⊗ 1`, characterized rather than assumed.
Source: Stacks Tag 03EL (blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: inverse image preserves the bilinear universal property of the tensor.
Constant coefficient comparisons commute with coefficient homomorphisms, since both
maps extend the same constant sections. Sheafify the induced balanced map. Pure tensors
and inverse-image units locally generate, so the displayed formula gives uniqueness.
This is the construction in proof steps 5--6. -/
theorem tateTensorMap_existsUnique {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') :
    ∃! b : (tatePullback h A).obj (tateTensor T φ M) ⟶ tateTensor T' φ M',
      IsTateTensorMap h φ M M' c b := by
  sorry

/-- The uniquely normalized `c ⊗ 1` after the canonical tensor pullback comparison.
Source: Stacks Tag 03EL (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTensorMap {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (M : tateModules T R) (M' : tateModules T' R)
    (c : (tatePullback h R).obj M ⟶ M') :
    (tatePullback h A).obj (tateTensor T φ M) ⟶ tateTensor T' φ M' :=
  (tateTensorMap_existsUnique h φ M M' c).exists.choose

/-- The constant quotient map from p-adic integers at positive level `n + 1`.
Source: Stacks Tag 03PK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePadicReduction (l n : ℕ) [Fact l.Prime] :
    ULift.{u} (PadicInt l) →+* ULift.{u} (ZMod (l ^ (n + 1))) :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)

/-- The projection tensor formula, using the finite module's quotient-scalar presentation.
The isomorphism i identifies its restriction to R with the specified finite level.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def IsTateReduction {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F)
    (α : tateTensor T (a.comp q) L ⟶ tateTensor T a G) : Prop :=
  ∀ (U : T.ProEt) (z : (proEtaleConstantRing T A).obj.obj (op U))
    (x : L.val.obj (op U)),
    α.val.app (op U) (tateTmul (a.comp q) L U z x) =
      tateTmul a G U z (i.inv.val.app (op U) (p.val.app (op U) x))

/-- The map α is defined by the projection on the first factor, with no chosen square.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: the projection is R-linear after restricting G along q. Thus its tensor with A
is balanced: p(rx) ⊗ z = p(x) ⊗ a(q(r))z. The tensor universal property and
sheafification produce α; pure tensors locally generate, proving uniqueness.
This is the balancing calculation of proof step 6. -/
theorem tateReduction_existsUnique {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F) :
    ∃! α : tateTensor T (a.comp q) L ⟶ tateTensor T a G,
      IsTateReduction q a L F G i p α := by
  sorry

/-- The uniquely balanced projection tensor map α.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateReduction {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F) :
    tateTensor T (a.comp q) L ⟶ tateTensor T a G :=
  (tateReduction_existsUnique q a L F G i p).exists.choose

/-- The finite-level `β_N ⊗ 1`, normalized on pulled back local pure tensors.
Source: Stacks Tag 03EL (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def IsTateFiniteTensorMap {T T' : Scheme.{u}} (h : T' ⟶ T)
    {R Q A : Type u} [CommRing R] [CommRing Q] [CommRing A]
    (q : R →+* Q) (a : Q →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (F : tateModules T R) (F' : tateModules T' R)
    (G : tateModules T Q) (G' : tateModules T' Q)
    (i : (tateRestrict T q).obj G ≅ F) (i' : (tateRestrict T' q).obj G' ≅ F')
    (β : (tatePullback h R).obj F ≅ F')
    (d : (tatePullback h A).obj (tateTensor T a G) ⟶ tateTensor T' a G') : Prop :=
  ∀ (U : T.ProEt) (z : (proEtaleConstantRing T A).obj.obj (op U))
    (y : G.val.obj (op U)),
    d.val.app (op ((proEtaleBaseChange h).obj U))
        (tateUnit h A (tateTensor T a G) U (tateTmul a G U z y)) =
      tateTmul a G' ((proEtaleBaseChange h).obj U) (tateRingUnit h A U z)
        (i'.inv.val.app (op ((proEtaleBaseChange h).obj U))
          (β.hom.val.app (op ((proEtaleBaseChange h).obj U))
            (tateUnit h R F U (i.hom.val.app (op U) y))))

/-- The quotient action on a killed module is unique up to its unique compatible isomorphism.
The universal property fixes the object up to exactly the isomorphisms used downstream.
Source: Stacks Tag 03EK and the quotient coefficient action in the finite Kummer-level proof
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: locally lift a section of the constant Z/l^N sheaf to Z_l. Act by a lift;
two lifts differ locally by l^N times a section, which annihilates M. Independence
and the sheaf condition glue this action. Ring and restriction identities are local.
This gives G on the same underlying abelian sheaf and its restriction identification.
Every other presentation has this same action, so the two identifications determine
the unique Q-linear isomorphism between them. -/
theorem tateFinitePresentation_exists (l n : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (M : tateModules T (ULift.{u} (PadicInt l)))
    (hM : ∀ (U : T.ProEt) (x : M.val.obj (op U)), (l ^ (n + 1)) • x = 0) :
    ∃ G : tateModules T (ULift.{u} (ZMod (l ^ (n + 1)))),
      ∃ i : (tateRestrict T (tatePadicReduction l n)).obj G ≅ M,
        ∀ (H : tateModules T (ULift.{u} (ZMod (l ^ (n + 1)))))
          (j : (tateRestrict T (tatePadicReduction l n)).obj H ≅ M),
          ∃! e : G ≅ H,
            (tateRestrict T (tatePadicReduction l n)).mapIso e ≪≫ j = i := by
  sorry

/-- The finite Q-module, selected from the quotient action's universal property.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateFiniteModule (l n : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l))) (hF : TateTowerKilled l F) :
    tateModules T (ULift.{u} (ZMod (l ^ (n + 1)))) :=
  (tateFinitePresentation_exists l n T (F.obj (op n)) (hF n)).choose

/-- The canonical restriction identification of the finite quotient action.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateFiniteModuleIso (l n : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l))) (hF : TateTowerKilled l F) :
    (tateRestrict T (tatePadicReduction l n)).obj (tateFiniteModule l n F hF) ≅
      F.obj (op n) :=
  (tateFinitePresentation_exists l n T (F.obj (op n)) (hF n)).choose_spec.choose

/-- The finite tensor square and its isomorphism conclusion.
The finite Q-module presentations i and i' express exactly the quotient actions on
F_N and F'_N; the coefficient map a is the action of Z/l^N on A, fixed by ha.
Source: the final sentence of the finite Kummer-level blueprint proof; Stacks Tag 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: steps 5--6 identify the inverse image of each tensor with the tensor of the
inverse images. The R-linear level isomorphism is Q-linear because R → Q is locally
surjective. Tensor it with A to obtain d and tensor c with A to obtain b. On a pure
tensor the two square composites are β_N(h⁻¹p_N(x)) ⊗ a and p'_N(c(h⁻¹x)) ⊗ a;
the limit projection equation identifies them. Local generation gives equality.
For step 8, tensor the inverse of β_N to invert d. If both α maps are invertible,
the square expresses b as a composite of three isomorphisms. -/
theorem tateInverseLimitFiniteTensorBaseChange (l n : ℕ) [Fact l.Prime]
    {T T' : Scheme.{u}} (h : T' ⟶ T)
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0)
    (a : ULift.{u} (ZMod (l ^ (n + 1))) →+* A)
    (ha : a.comp (tatePadicReduction l n) =
      (algebraMap (PadicInt l) A).comp ULift.ringEquiv.toRingHom)
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (PadicInt l)))]
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (ZMod (l ^ (n + 1)))))]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l)))
    (F' : ℕᵒᵖ ⥤ tateModules T' (ULift.{u} (PadicInt l)))
    (hF : TateTowerKilled l F) (hF' : TateTowerKilled l F')
    (β : F ⋙ tatePullback h (ULift.{u} (PadicInt l)) ≅ F')
    (G : tateModules T (ULift.{u} (ZMod (l ^ (n + 1)))))
    (G' : tateModules T' (ULift.{u} (ZMod (l ^ (n + 1)))))
    (i : (tateRestrict T (tatePadicReduction l n)).obj G ≅ F.obj (op n))
    (i' : (tateRestrict T' (tatePadicReduction l n)).obj G' ≅ F'.obj (op n)) :
    ∃ d : (tatePullback h A).obj (tateTensor T a G) ⟶ tateTensor T' a G',
      IsTateFiniteTensorMap h (tatePadicReduction l n) a
        (F.obj (op n)) (F'.obj (op n)) G G' i i' (β.app (op n)) d ∧
      IsIso d ∧
      tateTensorMap h (a.comp (tatePadicReduction l n)) (limit F) (limit F')
          (tateLimitMap h _ F F' β) ≫
          tateReduction (tatePadicReduction l n) a
            (limit F') (F'.obj (op n)) G' i' (limit.π F' (op n)) =
        (tatePullback h A).map
          (tateReduction (tatePadicReduction l n) a
            (limit F) (F.obj (op n)) G i (limit.π F (op n))) ≫ d ∧
      (IsIso (tateReduction (tatePadicReduction l n) a
          (limit F) (F.obj (op n)) G i (limit.π F (op n))) →
        IsIso (tateReduction (tatePadicReduction l n) a
          (limit F') (F'.obj (op n)) G' i' (limit.π F' (op n))) →
        IsIso (tateTensorMap h (a.comp (tatePadicReduction l n)) (limit F) (limit F')
          (tateLimitMap h _ F F' β))) := by
  sorry

/-- Unit normalization for the canonical identity inverse-image comparison.
Source: Stacks Tag 09A5 (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def IsTatePullbackId (T : Scheme.{u}) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)]
    (e : tatePullback (𝟙 T) R ≅ 𝟭 (tateModules T R)) : Prop :=
  ∀ (M : tateModules T R) (U : T.ProEt) (x : M.val.obj (op U)),
    (e.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 T)).obj U))
        (tateUnit (𝟙 T) R M U x) =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x

/-- The identity comparison, fixed by its actual inverse-image unit.
Source: Stacks Tag 09A5 (blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: base change by an identity is isomorphic to the identity on the site. Take
the mate of this direct-image identification under the normalized module adjunction.
Its unit equation is the displayed formula. Units locally generate the inverse image,
so this formula fixes every component and hence the natural isomorphism uniquely. -/
theorem tatePullbackId_existsUnique (T : Scheme.{u}) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)] :
    ∃! e : tatePullback (𝟙 T) R ≅ 𝟭 (tateModules T R), IsTatePullbackId T R e := by
  sorry

/-- The canonical identity comparison from its unique unit normalization.
Source: Stacks Tag 09A5 (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePullbackId (T : Scheme.{u}) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)] :
    tatePullback (𝟙 T) R ≅ 𝟭 (tateModules T R) :=
  (tatePullbackId_existsUnique T R).exists.choose

/-- The canonical inverse-image compositor on constant-coefficient modules: the existing
ordinary composition comparison `exchangeModuleComposition`, whose right-adjoint conjugate
is the sectionwise fibre-product pasting, transported along the canonical equality of the
composite constant-coefficient comparison `proEtaleConstantRingCompositeCoefficients_eq`.
No second compositor is constructed.
Source: Stacks Tags 03D8, 0D6D and 09A5
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePullbackComp {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (g : T'' ⟶ T')
    (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap g R)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) R)] :
    tatePullback (g ≫ h) R ≅ tatePullback h R ⋙ tatePullback g R :=
  eqToIso (congrArg (fun c ↦ proEtaleRingModulePullback (g ≫ h)
      (proEtaleConstantRing T R) (proEtaleConstantRing T'' R) c)
      (proEtaleConstantRingCompositeCoefficients_eq g h R).symm) ≪≫
    exchangeModuleComposition g h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
      (proEtaleConstantRing T'' R) (asIso (proEtaleCoefficientInverseImageMap h R))
      (asIso (proEtaleCoefficientInverseImageMap g R))

/-- Identity law for the limit comparison, relative to the canonical identity identification.
Source: finite Kummer-level blueprint proof, final sentence
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: the assumed identity law for β makes the coordinate projections of the two
maps equal. The uniqueness clause of the limit universal property proves equality.
This is the identity case of proof step 4. -/
theorem tateLimitMap_id (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) (ULift.{u} (PadicInt l)))]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l))) (hF : TateTowerKilled l F)
    (β : F ⋙ tatePullback (𝟙 T) (ULift.{u} (PadicInt l)) ≅ F)
    (hβ : ∀ r : ℕ, β.hom.app (op r) =
      (tatePullbackId T (ULift.{u} (PadicInt l))).hom.app (F.obj (op r))) :
    tateLimitMap (𝟙 T) _ F F β =
      (tatePullbackId T (ULift.{u} (PadicInt l))).hom.app (limit F) := by
  sorry

/-- Composition law for the limit comparison with the canonical inverse-image compositor.
Source: finite Kummer-level blueprint proof, final sentence
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: compose each side with p_r. Naturality of the compositor, the defining equations
for c_h and c_g, and the assumed composition law for β give the same coordinate map.
Joint monicity of the projections proves equality. This is proof step 4. -/
theorem tateLimitMap_comp (l : ℕ) [Fact l.Prime]
    {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (g : T'' ⟶ T')
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (PadicInt l)))]
    [IsIso (proEtaleCoefficientInverseImageMap g (ULift.{u} (PadicInt l)))]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) (ULift.{u} (PadicInt l)))]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l)))
    (F' : ℕᵒᵖ ⥤ tateModules T' (ULift.{u} (PadicInt l)))
    (F'' : ℕᵒᵖ ⥤ tateModules T'' (ULift.{u} (PadicInt l)))
    (hF : TateTowerKilled l F) (hF' : TateTowerKilled l F') (hF'' : TateTowerKilled l F'')
    (βh : F ⋙ tatePullback h (ULift.{u} (PadicInt l)) ≅ F')
    (βg : F' ⋙ tatePullback g (ULift.{u} (PadicInt l)) ≅ F'')
    (βgh : F ⋙ tatePullback (g ≫ h) (ULift.{u} (PadicInt l)) ≅ F'')
    (hβ : ∀ r : ℕ, βgh.hom.app (op r) =
      (tatePullbackComp h g (ULift.{u} (PadicInt l))).hom.app (F.obj (op r)) ≫
        (tatePullback g _).map (βh.hom.app (op r)) ≫ βg.hom.app (op r)) :
    tateLimitMap (g ≫ h) _ F F'' βgh =
      (tatePullbackComp h g (ULift.{u} (PadicInt l))).hom.app (limit F) ≫
        (tatePullback g _).map (tateLimitMap h _ F F' βh) ≫
          tateLimitMap g _ F' F'' βg := by
  sorry

/-- Tensoring preserves the canonical identity law, in particular for b_id.
Source: finite Kummer-level blueprint proof, final sentence; Stacks Tag 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: apply the pure-tensor normalization of the tensor comparison and the
unit-normalized identity comparison. Both sides act identically on the pulled back
pure tensors; these locally generate the source. This is the identity case of step 7. -/
theorem tateTensorMap_id (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) R)]
    [IsIso (proEtaleCoefficientInverseImageMap (𝟙 T) A)] (M : tateModules T R) :
    tateTensorMap (𝟙 T) φ M M ((tatePullbackId T R).hom.app M) =
      (tatePullbackId T A).hom.app (tateTensor T φ M) := by
  sorry

/-- Tensoring preserves the canonical composition law, in particular for b_h and b_g.
Source: finite Kummer-level blueprint proof, final sentence; Stacks Tag 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: the compositor's conjugate is fibre-product pasting, so by the unit equations of
the normalized adjunctions it carries a pulled back pure tensor to the iterated one.
Apply the pure-tensor formula for
the two tensor maps. Both sides apply c_h, then c_g, to the first factor, and preserve
the coefficient factor. Constant-section maps compose by the same normalization.
Local generation gives equality. With step 4 this is proof step 7 for the b maps. -/
theorem tateTensorMap_comp {T T' T'' : Scheme.{u}} (h : T' ⟶ T) (g : T'' ⟶ T')
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [IsIso (proEtaleCoefficientInverseImageMap h R)]
    [IsIso (proEtaleCoefficientInverseImageMap g R)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) R)]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    [IsIso (proEtaleCoefficientInverseImageMap g A)]
    [IsIso (proEtaleCoefficientInverseImageMap (g ≫ h) A)]
    (M : tateModules T R) (M' : tateModules T' R) (M'' : tateModules T'' R)
    (ch : (tatePullback h R).obj M ⟶ M') (cg : (tatePullback g R).obj M' ⟶ M'') :
    tateTensorMap (g ≫ h) φ M M''
        ((tatePullbackComp h g R).hom.app M ≫ (tatePullback g R).map ch ≫ cg) =
      (tatePullbackComp h g A).hom.app (tateTensor T φ M) ≫
        (tatePullback g A).map (tateTensorMap h φ M M' ch) ≫
          tateTensorMap g φ M' M'' cg := by
  sorry

/-- Every killed Z_l-algebra has its unique finite quotient action, with no extra data.
Source: Stacks Tag 03EK; PadicInt.toZModPow and its kernel
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: the kernel of reduction to Z/l^N is the ideal generated by l^N.
The given algebra map kills this ideal because l^N is zero in A. Factor through
the quotient and its standard identification with Z/l^N. Surjectivity of reduction
gives uniqueness. Universe lifts transport this unique map without changing it. -/
theorem tateFiniteAlgebraMap_existsUnique (l n : ℕ) [Fact l.Prime]
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0) :
    ∃! a : ULift.{u} (ZMod (l ^ (n + 1))) →+* A,
      a.comp (tatePadicReduction l n) =
        (algebraMap (PadicInt l) A).comp ULift.ringEquiv.toRingHom := by
  sorry

/-- The canonical finite scalar action of Z/l^N on the killed algebra A.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateFiniteAlgebraMap (l n : ℕ) [Fact l.Prime]
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0) : ULift.{u} (ZMod (l ^ (n + 1))) →+* A :=
  (tateFiniteAlgebraMap_existsUnique l n A hA).exists.choose

/-- The actual α_S, with the canonical quotient actions and the coordinate projection p_N.
Source: finite Kummer-level blueprint proof, final sentence; Stacks Tag 03EK
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTowerReduction (l n : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0)
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l))) (hF : TateTowerKilled l F) :
    tateTensor T ((tateFiniteAlgebraMap l n A hA).comp (tatePadicReduction l n))
        (limit F) ⟶
      tateTensor T (tateFiniteAlgebraMap l n A hA) (tateFiniteModule l n F hF) :=
  tateReduction (tatePadicReduction l n) (tateFiniteAlgebraMap l n A hA)
    (limit F) (F.obj (op n)) (tateFiniteModule l n F hF) (tateFiniteModuleIso l n F hF)
    (limit.π F (op n))

/-- The canonical finite tensor square, with no quotient presentations assumed as data.
Source: finite Kummer-level blueprint proof, final sentence; Stacks Tag 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).
Proof: apply the finite tensor square above to the quotient actions uniquely fixed
by tateFinitePresentation_exists and tateFiniteAlgebraMap_existsUnique. Its pure-tensor
equations are exactly α_S(x ⊗ a) = p_N(x) ⊗ a and d_h = β_N ⊗ 1. The limit
projection equation proves the commuting square. Tensor β_N inverse to invert d_h;
if α_T and α_T' are invertible, solve the square for b_h to obtain an isomorphism.
These are proof steps 5--6 and 8. Identity and composition for b_h follow from
steps 4 and 7, stated as tateLimitMap_id/comp and tateTensorMap_id/comp. -/
theorem tateInverseLimitCanonicalFiniteTensorBaseChange (l n : ℕ) [Fact l.Prime]
    {T T' : Scheme.{u}} (h : T' ⟶ T)
    (A : Type u) [CommRing A] [Algebra (PadicInt l) A]
    (hA : (l ^ (n + 1) : A) = 0)
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (PadicInt l)))]
    [IsIso (proEtaleCoefficientInverseImageMap h (ULift.{u} (ZMod (l ^ (n + 1)))))]
    [IsIso (proEtaleCoefficientInverseImageMap h A)]
    (F : ℕᵒᵖ ⥤ tateModules T (ULift.{u} (PadicInt l)))
    (F' : ℕᵒᵖ ⥤ tateModules T' (ULift.{u} (PadicInt l)))
    (hF : TateTowerKilled l F) (hF' : TateTowerKilled l F')
    (β : F ⋙ tatePullback h (ULift.{u} (PadicInt l)) ≅ F') :
    ∃ d : (tatePullback h A).obj
        (tateTensor T (tateFiniteAlgebraMap l n A hA) (tateFiniteModule l n F hF)) ⟶
      tateTensor T' (tateFiniteAlgebraMap l n A hA) (tateFiniteModule l n F' hF'),
      IsTateFiniteTensorMap h (tatePadicReduction l n) (tateFiniteAlgebraMap l n A hA)
        (F.obj (op n)) (F'.obj (op n))
        (tateFiniteModule l n F hF) (tateFiniteModule l n F' hF')
        (tateFiniteModuleIso l n F hF) (tateFiniteModuleIso l n F' hF')
        (β.app (op n)) d ∧ IsIso d ∧
      tateTensorMap h ((tateFiniteAlgebraMap l n A hA).comp (tatePadicReduction l n))
          (limit F) (limit F') (tateLimitMap h _ F F' β) ≫
          tateTowerReduction l n A hA F' hF' =
        (tatePullback h A).map (tateTowerReduction l n A hA F hF) ≫ d ∧
      (IsIso (tateTowerReduction l n A hA F hF) →
        IsIso (tateTowerReduction l n A hA F' hF') →
        IsIso (tateTensorMap h
          ((tateFiniteAlgebraMap l n A hA).comp (tatePadicReduction l n))
          (limit F) (limit F') (tateLimitMap h _ F F' β))) := by
  sorry

end AlgebraicGeometry.Scheme
