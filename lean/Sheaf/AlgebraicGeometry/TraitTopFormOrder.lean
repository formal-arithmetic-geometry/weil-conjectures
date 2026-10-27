/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.SmoothTraitModel
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Topology.KrullDimension

/-! # Top differential forms and their orders on trait models

Source: BLR, Néron Models, 4.2 and 4.3, printed pp.99--105
(blueprint: def-sfb-trait-top-form-order).

## Main definitions

- `traitTopForms`: the recorded exterior sheaf of relative differentials.
- `IsTopDifferentialMap`, `TopFormPullsTo`: pullback pinned on differential wedges.
- `IsLeftInvariantTopForm`: relative multiplication invariance.
- `IsTraitVolumeOrder`: the local normalized-frame relation.
- `HasTraitUnitSection`: the strict-henselian valuation-zero condition.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
namespace AlgebraicGeometry

/-- The existing exterior sheaf of the existing relative differential sheaf.
Source: BLR 4.3, printed p.104 (blueprint: def-sfb-trait-top-form-order). -/
noncomputable abbrev traitTopForms {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) : X.Modules :=
  Scheme.Modules.exteriorSheaf f.relativeDifferentials d

/-- The canonical differential map is specified on wedges of universal differentials.
The base change of scalars is already part of the module pushforward. This relation
pins the map on local generators, including the empty wedge in degree zero.
Source: BLR 2.1, 4.2 and 4.3 (blueprint: def-sfb-trait-top-form-order). -/
def IsTopDifferentialMap {X Y S T : Scheme.{u}} (f : Y ⟶ S) (g : X ⟶ T)
    (h : X ⟶ Y) (d : ℕ)
    (D : traitTopForms f d ⟶ (Scheme.Modules.pushforward h).obj (traitTopForms g d)) :
    Prop :=
  ∀ (W : Y.Opens) (a : Fin d → Γ(Y, W)),
    D.app W (Scheme.Modules.exteriorSheafSection f.relativeDifferentials d W
      (fun i ↦ f.relativeDifferentialsDerivation.d (X := op W) (a i))) =
    Scheme.Modules.exteriorSheafSection g.relativeDifferentials d (h ⁻¹ᵁ W)
      (fun i ↦ g.relativeDifferentialsDerivation.d (X := op (h ⁻¹ᵁ W)) (h.app W (a i)))

/-- Pullback of a global top form, using the differential map pinned on local wedges.
The existential map is uniquely characterized, rather than supplied as arbitrary data.
Source: BLR 2.1 and 4.3 (blueprint: def-sfb-trait-top-form-order). -/
def TopFormPullsTo {X Y S T : Scheme.{u}} (f : Y ⟶ S) (g : X ⟶ T)
    (h : X ⟶ Y) (d : ℕ) (ω : Γ(traitTopForms f d, ⊤))
    (η : Γ(traitTopForms g d, ⊤)) : Prop :=
  ∃ D : traitTopForms f d ⟶ (Scheme.Modules.pushforward h).obj (traitTopForms g d),
    IsTopDifferentialMap f g h d D ∧
      D.app ⊤ ω = (traitTopForms g d).presheaf.map (homOfLE le_top).op η

/-- Left invariance means that multiplication and the second projection pull the
form to the same form relative to the first projection. Taking relative differentials
here is essential: absolute differentials would also differentiate the translating factor.
Source: BLR 4.2, printed pp.99--102 (blueprint: def-sfb-trait-top-form-order). -/
def IsLeftInvariantTopForm {E : Type u} [Field E]
    (G : Over (Spec (.of E))) [GrpObj G] (d : ℕ)
    (ω : Γ(traitTopForms G.hom d, ⊤)) : Prop :=
  ∃ η : Γ(traitTopForms (fst G G).left d, ⊤),
    TopFormPullsTo G.hom (fst G G).left (MonObj.mul (X := G)).left d ω η ∧
      TopFormPullsTo G.hom (fst G G).left (snd G G).left d ω η

/-- A scalar of the generic field as a constant global function on G.
Source: BLR 4.3, printed p.104 (blueprint: def-sfb-trait-top-form-order). -/
noncomputable def traitGenericScalar {E : Type u} [Field E]
    (G : Over (Spec (.of E))) : E →+* Γ(G.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of E)).inv ≫ G.hom.appTop).hom

/-- The order is the integer for which the normalized generic form extends to a frame
near the specified special-fibre generic point. A frame on some neighbourhood is
exactly a generator of the stalk of this line bundle. No integer is chosen here.
Source: BLR 4.3 order construction, printed p.104
(blueprint: def-sfb-trait-top-form-order). -/
def IsTraitVolumeOrder {R E : Type u} [CommRing R] [Field E] [Algebra R E]
    {G : Over (Spec (.of E))} (M : SmoothTraitModel (R := R) G)
    (π : R) (d : ℕ) (ω : Γ(traitTopForms G.hom d, ⊤)) (z : M.scheme) (n : ℤ) : Prop :=
  ∃ (V : M.scheme.Opens) (_ : z ∈ V) (s : Γ(traitTopForms M.hom d, V)),
    Scheme.Modules.IsFreeGenerator s ∧
      ∃ D : traitTopForms M.hom d ⟶
          (Scheme.Modules.pushforward M.genericInclusion).obj (traitTopForms G.hom d),
        IsTopDifferentialMap M.hom G.hom M.genericInclusion d D ∧
          D.app V s = (traitTopForms G.hom d).presheaf.map (homOfLE le_top).op
            (traitGenericScalar G ((algebraMap R E π) ^ (-n)) • ω)

/-- The component open consists of that special-fibre component and the entire generic
fibre. It is specified as a set here; smoothness makes special components disjoint and
closed, so this set is open. It also handles a disconnected generic fibre.
Source: BLR 4.3, printed pp.104--107 (blueprint: def-sfb-trait-top-form-order). -/
def traitComponentSet {R E : Type u} [CommRing R] [IsLocalRing R]
    [Field E] [Algebra R E] {G : Over (Spec (.of E))}
    (M : SmoothTraitModel (R := R) G)
    (C : Set (M.hom.fiber (IsLocalRing.closedPoint R))) : Set M.scheme :=
  Set.range M.genericInclusion ∪ M.hom.fiberι (IsLocalRing.closedPoint R) '' C

/-- The valuation-zero hypothesis: a strict-henselian section, lying in the specified
component open, whose generic point evaluates the multiplier to an integral unit.
The equality on the total fraction ring is precisely v(a(x)) = 0, once the strict
henselization is known to be a DVR. All arrows are the canonical spectrum arrows.
Source: BLR 4.3 Lemma 1 and the preceding normalization paragraph, printed p.104
(blueprint: def-sfb-trait-top-form-order). -/
def HasTraitUnitSection {R E : Type u} [CommRing R] [Field E] [Algebra R E]
    {G : Over (Spec (.of E))} (M : SmoothTraitModel (R := R) G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of R))
    (a : Γ(G.left, ⊤)ˣ) (U : Set M.scheme) : Prop :=
  ∃ (x : Scheme.strictHenselizationScheme s ⟶ M.scheme)
    (l : Spec (.of (FractionRing (Scheme.strictHenselizationRing s))) ⟶ G.left)
    (c : Γ(Scheme.strictHenselizationScheme s, ⊤)ˣ),
    x ≫ M.hom = traitStrictBase s ∧ Set.range x ⊆ U ∧
      l ≫ M.genericInclusion =
        Spec.map (CommRingCat.ofHom (algebraMap (Scheme.strictHenselizationRing s)
          (FractionRing (Scheme.strictHenselizationRing s)))) ≫ x ∧
      l.appTop (a : Γ(G.left, ⊤)) =
        (Spec.map (CommRingCat.ofHom (algebraMap (Scheme.strictHenselizationRing s)
          (FractionRing (Scheme.strictHenselizationRing s))))).appTop
          (c : Γ(Scheme.strictHenselizationScheme s, ⊤))

end AlgebraicGeometry
