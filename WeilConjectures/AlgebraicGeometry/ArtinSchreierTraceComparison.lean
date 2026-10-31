/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Finite.Trace

/-! # The trace comparison between the two Artin–Schreier models

Source: latest blueprint, sec-fourier-transform/sk-lem-as-properties,
lem-wft-as-comparison, clauses (1)–(3) and its proof
(blueprint: lem-wft-as-comparison).

The cover is the existing polynomial-quotient cover, also for exponent q.
The maps on direct images are the actual pullbacks of coefficient sections.
The condensed version uses internal modules over the pulled-back coefficient ring;
its scalars are global sections of the condensed ring, that is, its value at the point.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.upperStarLowerStarAdjunction

/-- The image of a scalar in the structure sheaf of a k-scheme.
Source: blueprint lem-wft-as-comparison (2), the function af
(blueprint: lem-wft-as-comparison). -/
def scalar (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (a : k) : Γ(X, ⊤) :=
  (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv.hom a)

/-- Pullback of coefficient functions along a morphism of covers, with the canonical
composition identification of direct images.
Source: blueprint lem-wft-as-comparison (2), h_a^*
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def etalePull (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    {Y Z : Over X} (h : Y ⟶ Z) :
    (Etale.lowerStar (ModuleCat Λ) Z.hom).obj (𝟙_ _) ⟶
      (Etale.lowerStar (ModuleCat Λ) Y.hom).obj (𝟙_ _) :=
  (Etale.lowerStar (ModuleCat Λ) Z.hom).map
      (Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat Λ) h.left)) ≫
    (Etale.lowerStarComp (ModuleCat Λ) h.left Z.hom Y.hom (Over.w h).symm).hom.app _

/-- Averaging on an actual finite cover with its specified translations.
Source: blueprint lem-wft-as-comparison, projector convention
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def etaleProjector (Λ : Type (u + 1)) [CommRing Λ]
    (G : Type v) [AddGroup G] [Fintype G] {X : Scheme.{u}} (Y : Over X)
    (σ : G → (Y ⟶ Y)) (χ : AddChar G Λ) :
    End ((Etale.lowerStar (ModuleCat Λ) Y.hom).obj (𝟙_ _)) :=
  ∑ c : G, (Ring.inverse (Fintype.card G : Λ) * χ (-c)) • etalePull Λ (σ c)

/-- Evaluation at a chosen point of a cover, as the adjoint of pullback of functions.
Source: blueprint lem-wft-as-comparison (3), evaluation at the selected root
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def etaleEvaluation (Λ : Type (u + 1)) [CommRing Λ] {X T : Scheme.{u}}
    (x : T ⟶ X) {Y : Over X} (s : Over.mk x ⟶ Y)
    {M : Sheaf X.smallEtaleTopology (ModuleCat Λ)}
    (ι : M ⟶ (Etale.lowerStar (ModuleCat Λ) Y.hom).obj (𝟙_ _)) :
    (Etale.upperStar (ModuleCat Λ) x).obj M ⟶ (𝟙_ _) :=
  ((Etale.upperStarLowerStarAdjunction (ModuleCat Λ) x).homEquiv _ _).symm
    (ι ≫ etalePull Λ s)

/-- The constant coefficient module, retaining its actual internal-module structure.
Source: blueprint lem-wft-as-comparison, condensed coefficient paragraph
(blueprint: lem-wft-as-comparison). -/
def condensedUnit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :=
  Mod.regular (ProEtale.condensedRingObj Λ X)

/-- Pullback of condensed coefficient sections as a morphism of coefficient modules.
The linear lift sends 1 to the canonical coefficient unit eta_h(1); hence it is eta_h.
Source: blueprint lem-wft-as-comparison (2), coefficient-module h_a^*
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def condensedPull (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {Y Z : Over X} (h : Y ⟶ Z) :
    (ProEtale.CondensedRing.lowerStar Λ Z.hom).obj (condensedUnit Λ Z.left) ⟶
      (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left) :=
  (ProEtale.CondensedRing.lowerStar Λ Z.hom).map
      (Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ h.left).obj (condensedUnit Λ Y.left))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ h.left)) ≫
    (ProEtale.CondensedRing.lowerStarComp Λ h.left Z.hom).hom.app _ ≫
      (ProEtale.CondensedRing.lowerStarCongr Λ (Over.w h)).hom.app _

/-- The condensed averaging projector. Each coefficient is first transported by p_Y^*
and then acts on the regular coefficient module, before direct image.
Source: blueprint lem-wft-as-comparison, explicit projector e_chi
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def condensedProjector (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (G : Type v) [AddGroup G] [Fintype G]
    {X : Scheme.{u}} (Y : Over X) (σ : G → (Y ⟶ Y)) (χ : AddChar G (MonObj.Γ Λ)) :
    End ((ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :=
  ∑ c : G, condensedPull Λ (σ c) ≫
    (ProEtale.CondensedRing.lowerStar Λ Y.hom).map
      (Mod.regularEndRingHom (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y.left)
        (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c))))

/-- Evaluation of a condensed eigensection at a chosen root, in internal modules.
Source: blueprint lem-wft-as-comparison (3), evaluation trivializations
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def condensedEvaluation (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} (x : T ⟶ X)
    {Y : Over X} (s : Over.mk x ⟶ Y)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}
    (ι : M ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :
    (ProEtale.CondensedRing.upperStar Λ x).obj M ⟶ condensedUnit Λ T :=
  (ProEtale.CondensedRing.upperStar Λ x).map (ι ≫ condensedPull Λ s) ≫
    (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ x).counit.app (condensedUnit Λ T)

/-- The degree-q Artin–Schreier sheaf with condensed coefficients. The same universal
Artin–Schreier map and translations as in the recorded etale definition are used;
only the coefficient category is changed to the recorded internal modules.
Source: blueprint lem-wft-as-comparison, condensed coefficient convention and (2)
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def condensedSheafOf (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (χ : AddChar k (MonObj.Γ Λ)) (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (f : Γ(X, ⊤)) :=
  (ProEtale.CondensedRing.upperStar Λ
    (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ : PUnit ↦ f)).obj
      (image (condensedProjector Λ k
        (Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)))
        (fun c ↦ Over.homMk (Etale.artinSchreierTranslation k c)
          (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)) χ))

/-- The precise ordinary-coefficient comparison, including its induced-map equation.
The last equation is compatibility of evaluation at roots carried to one another;
it specializes at the two zero roots to the stalk normalization of (3).
Source: blueprint lem-wft-as-comparison (2)–(3)
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def EtaleComparison (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k]
    [Algebra (ZMod p) k] (Λ : Type (u + 1)) [CommRing Λ]
    [Invertible (Fintype.card k : Λ)] (Ψ : AddChar (ZMod p) Λ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) (a : k)
    (σq : k → (artinSchreierCover (Fintype.card k) X f ⟶
      artinSchreierCover (Fintype.card k) X f))
    (σp : ZMod p → (artinSchreierCover p X (scalar k X a * f) ⟶
      artinSchreierCover p X (scalar k X a * f)))
    (h : artinSchreierCover (Fintype.card k) X f ⟶
      artinSchreierCover p X (scalar k X a * f)) : Prop :=
  ∃ e : image (etaleProjector Λ (ZMod p) _ σp Ψ) ≅
      image (etaleProjector Λ k _ σq ((Ψ.compTrace k).mulShift a)),
    e.hom ≫ image.ι (etaleProjector Λ k _ σq ((Ψ.compTrace k).mulShift a)) =
      image.ι (etaleProjector Λ (ZMod p) _ σp Ψ) ≫ etalePull Λ h ∧
    Nonempty (image (etaleProjector Λ k _ σq ((Ψ.compTrace k).mulShift a)) ≅
      Etale.artinSchreierSheafOf X ((Ψ.compTrace k).mulShift a) f) ∧
    ∀ (T : Scheme.{u}) (x : T ⟶ X)
      (s : Over.mk x ⟶ artinSchreierCover (Fintype.card k) X f)
      (t : Over.mk x ⟶ artinSchreierCover p X (scalar k X a * f)),
      s ≫ h = t →
      IsIso (etaleEvaluation Λ x t (image.ι (etaleProjector Λ (ZMod p) _ σp Ψ))) ∧
      IsIso (etaleEvaluation Λ x s
        (image.ι (etaleProjector Λ k _ σq ((Ψ.compTrace k).mulShift a)))) ∧
      (Etale.upperStar (ModuleCat Λ) x).map e.hom ≫
          etaleEvaluation Λ x s
            (image.ι (etaleProjector Λ k _ σq ((Ψ.compTrace k).mulShift a))) =
        etaleEvaluation Λ x t (image.ι (etaleProjector Λ (ZMod p) _ σp Ψ))

/-- The same comparison in actual modules over p_X^*Lambda. Global-section scalars
are Lambda(*), not scalar stalks replacing the condensed ring.
Source: blueprint lem-wft-as-comparison, condensed paragraph and (2)–(3)
(blueprint: lem-wft-as-comparison). -/
@[irreducible]
def CondensedComparison (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k]
    [Algebra (ZMod p) k]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Ψ : AddChar (ZMod p) (MonObj.Γ Λ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) (a : k)
    (σq : k → (artinSchreierCover (Fintype.card k) X f ⟶
      artinSchreierCover (Fintype.card k) X f))
    (σp : ZMod p → (artinSchreierCover p X (scalar k X a * f) ⟶
      artinSchreierCover p X (scalar k X a * f)))
    (h : artinSchreierCover (Fintype.card k) X f ⟶
      artinSchreierCover p X (scalar k X a * f)) : Prop :=
  ∃ e : image (condensedProjector Λ (ZMod p) _ σp Ψ) ≅
      image (condensedProjector Λ k _ σq ((Ψ.compTrace k).mulShift a)),
    e.hom ≫ image.ι (condensedProjector Λ k _ σq ((Ψ.compTrace k).mulShift a)) =
      image.ι (condensedProjector Λ (ZMod p) _ σp Ψ) ≫ condensedPull Λ h ∧
    Nonempty (image (condensedProjector Λ k _ σq ((Ψ.compTrace k).mulShift a)) ≅
      condensedSheafOf Λ k ((Ψ.compTrace k).mulShift a) X f) ∧
    ∀ (T : Scheme.{u}) (x : T ⟶ X)
      (s : Over.mk x ⟶ artinSchreierCover (Fintype.card k) X f)
      (t : Over.mk x ⟶ artinSchreierCover p X (scalar k X a * f)),
      s ≫ h = t →
      IsIso (condensedEvaluation Λ x t
        (image.ι (condensedProjector Λ (ZMod p) _ σp Ψ))) ∧
      IsIso (condensedEvaluation Λ x s
        (image.ι (condensedProjector Λ k _ σq ((Ψ.compTrace k).mulShift a)))) ∧
      (ProEtale.CondensedRing.upperStar Λ x).map e.hom ≫
          condensedEvaluation Λ x s
            (image.ι (condensedProjector Λ k _ σq ((Ψ.compTrace k).mulShift a))) =
        condensedEvaluation Λ x t (image.ι (condensedProjector Λ (ZMod p) _ σp Ψ))

/-- Character classification in a coefficient field, with the trivial-character case.
Source: blueprint lem-wft-as-comparison (1) (blueprint: lem-wft-as-comparison).

Proof: the trace character Psi∘Tr is primitive (def-fd-additive-character), so
a ↦ (Psi∘Tr)(a·-) is injective, its zero shift is trivial and no nonzero shift is.
By Dedekind independence of characters the additive characters k → Lambda are
linearly independent in the Lambda-vector space of functions k → Lambda, of dimension
#k (def-weil-vector-space-dimension); so there are at most #k of them, and the
injection from k is bijective. -/
theorem trace_character_classification (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Λ : Type v) [Field Λ] [Invertible (Fintype.card k : Λ)]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : Ψ ≠ 1) :
    (∀ ψ : AddChar k Λ, ∃! a : k, ψ = (Ψ.compTrace k).mulShift a) ∧
      ∀ a : k, (Ψ.compTrace k).mulShift a ≠ 1 ↔ a ≠ 0 := by
  classical
  have hlin := (linearIndependent_monoidHom (Multiplicative k) Λ).comp
    AddChar.toMonoidHomEquiv AddChar.toMonoidHomEquiv.injective
  change LinearIndependent Λ (fun ψ : AddChar k Λ ↦ (ψ : k → Λ)) at hlin
  have : Finite (AddChar k Λ) := hlin.finite
  let : Fintype (AddChar k Λ) := Fintype.ofFinite _
  have hcard : Fintype.card (AddChar k Λ) ≤ Fintype.card k := by
    simpa using hlin.fintype_card_le_finrank
  have hprim := AddChar.isPrimitive_compTrace (L := k) hΨ
  have hinj := AddChar.to_mulShift_inj_of_isPrimitive hprim
  have hsurj : Function.Surjective (fun a : k ↦ (Ψ.compTrace k).mulShift a) := by
    by_contra hn
    exact (not_lt_of_ge hcard) (Fintype.card_lt_of_injective_not_surjective _ hinj hn)
  constructor
  · intro ψ
    obtain ⟨a, ha⟩ := hsurj ψ
    exact ⟨a, ha.symm, fun b hb ↦ hinj (hb.symm.trans ha.symm)⟩
  · intro a
    constructor
    · intro ha haz
      exact ha (haz ▸ AddChar.mulShift_zero _)
    · exact fun ha ↦ hprim ha

/-- The two Artin–Schreier models, with their actual induced comparison and root evaluation.
No nonemptiness, separation or finite-type hypothesis is imposed on X.
Source: blueprint lem-wft-as-comparison (2)–(3), including a=1
(blueprint: lem-wft-as-comparison).

Proof: (1) Put u=sum_i (ay)^(p^i). In characteristic p, cancellation of adjacent
Frobenius powers gives u^p-u=a(y^q-y)=af; use lem-weil-finite-field-pow-card and
lem-a1-finite-field-trace-frobenius-sum. The quotient presentations glue to the
specified map h. Applying the same expansion to y+c proves equivariance.
(2) The degree-q cover is the pullback of the finite etale Artin–Schreier torsor
(lem-wft-finite-field-as-map); lem-fd-as-cover gives the prime-degree torsor. Split
both on an etale cover, choosing y0 and u0=h(y0). Their coefficient modules are
products indexed by k and F_p, using def-weil-pbc-direct-image or the condensed
module functors det-def-sfb-module-pushforward-pullback with the pulled-back rings
of det-def-sfb-pulled-back-coefficients. Finite base change (sk-lem-pbc-finite or
lem-a1-finite-etale-condensed-base-change) identifies the q-projector image with
f^*L_psi, naturally for translations.
(3) The averaging image is exactly the eigenmodule: translation by c acts as chi(c),
and averaging fixes any such eigenvector. Evaluation at a chosen root identifies
it with the coefficient unit, with inverse r |-> (c |-> chi(c)r). Pullback along h
sends the Psi-eigenfunction of value r at u0 to the psi-eigenfunction of value r
at y0. Thus its restriction is an isomorphism; the local inverses glue.
(4) At x=y=0 the trace polynomial is zero. Evaluation after pullback is evaluation
at the image root, yielding precisely the zero-stalk normalization. This argument
works on module sheaves for condensed coefficients as well. Setting a=1 identifies
the prime cover of af with the prime cover of f, giving the final clause. -/
theorem artinSchreier_trace_comparison (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) (a : kˣ) :
    ∃ (σq : k → (artinSchreierCover (Fintype.card k) X f ⟶
        artinSchreierCover (Fintype.card k) X f))
      (σp : ZMod p → (artinSchreierCover p X (scalar k X (a : k) * f) ⟶
        artinSchreierCover p X (scalar k X (a : k) * f)))
      (h : artinSchreierCover (Fintype.card k) X f ⟶
        artinSchreierCover p X (scalar k X (a : k) * f)),
      (∀ c : k, (σq c).left.appTop
          (artinSchreierCoverCoordinate (Fintype.card k) X f) =
        artinSchreierCoverCoordinate (Fintype.card k) X f +
          (artinSchreierCover (Fintype.card k) X f).hom.appTop (scalar k X c)) ∧
      (∀ b : ZMod p, (σp b).left.appTop
          (artinSchreierCoverCoordinate p X (scalar k X (a : k) * f)) =
        artinSchreierCoverCoordinate p X (scalar k X (a : k) * f) +
          (b.val : Γ((artinSchreierCover p X (scalar k X (a : k) * f)).left, ⊤))) ∧
      h.left.appTop (artinSchreierCoverCoordinate p X (scalar k X (a : k) * f)) =
        ∑ i ∈ Finset.range (Module.finrank (ZMod p) k),
          ((artinSchreierCover (Fintype.card k) X f).hom.appTop (scalar k X (a : k)) *
            artinSchreierCoverCoordinate (Fintype.card k) X f) ^ (p ^ i) ∧
      (∀ c : k, σq c ≫ h = h ≫ σp (Algebra.trace (ZMod p) k ((a : k) * c))) ∧
      (∀ (T : Scheme.{u}) (s : T ⟶ (artinSchreierCover (Fintype.card k) X f).left),
        s.appTop (artinSchreierCoverCoordinate (Fintype.card k) X f) = 0 →
        (s ≫ h.left).appTop
          (artinSchreierCoverCoordinate p X (scalar k X (a : k) * f)) = 0) ∧
      (∀ (Λ : Type (u + 1)) [CommRing Λ] [Invertible (Fintype.card k : Λ)]
        (Ψ : AddChar (ZMod p) Λ), Ψ ≠ 1 →
        EtaleComparison p k Λ Ψ X f (a : k) σq σp h) ∧
      (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj Λ] [IsCommMonObj Λ],
        ProEtale.CondensedRing.IsAdmissibleCoefficient Λ →
        IsUnit (Fintype.card k : MonObj.Γ Λ) →
        ∀ Ψ : AddChar (ZMod p) (MonObj.Γ Λ), Ψ ≠ 1 →
          CondensedComparison p k Λ Ψ X f (a : k) σq σp h) := by
  sorry

/-- The field clause for condensed coefficients uses precisely the ring Lambda(*).
Source: blueprint lem-wft-as-comparison (1), condensed coefficient paragraph
(blueprint: lem-wft-as-comparison).

Proof: give the existing global-section ring its field structure using the stated
IsField hypothesis and apply trace_character_classification. Its unit hypothesis
supplies invertibility of q. This changes no ring operations or coefficient sheaves. -/
theorem condensed_trace_character_classification (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : ProEtale.CondensedRing.IsAdmissibleCoefficient Λ)
    (hfield : IsField (MonObj.Γ Λ)) (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
    (Ψ : AddChar (ZMod p) (MonObj.Γ Λ)) (hΨ : Ψ ≠ 1) :
    (∀ ψ : AddChar k (MonObj.Γ Λ), ∃! a : k, ψ = (Ψ.compTrace k).mulShift a) ∧
      ∀ a : k, (Ψ.compTrace k).mulShift a ≠ 1 ↔ a ≠ 0 := by
  have _hcoeff := hΛ
  let : Field (MonObj.Γ Λ) := hfield.toField
  let : Invertible (Fintype.card k : MonObj.Γ Λ) := hq.invertible
  exact trace_character_classification p k (MonObj.Γ Λ) Ψ hΨ

/-- The named q-cover at the origin of the affine line; this is the existing cover,
not a new model of it. Source: blueprint lem-wft-as-comparison (3)
(blueprint: lem-wft-as-comparison). -/
abbrev originQCover (k : Type u) [Field k] [Fintype k] :
    Over 𝔸(PUnit; Spec (.of k)) :=
  artinSchreierCover (Fintype.card k) _ (AffineSpace.coord (Spec (.of k)) PUnit.unit)

/-- The named p-cover of ax at the origin, using the existing polynomial quotient.
Source: blueprint lem-wft-as-comparison (3) (blueprint: lem-wft-as-comparison). -/
abbrev originPCover (p : ℕ) (k : Type u) [Field k] (a : k) :
    Over 𝔸(PUnit; Spec (.of k)) :=
  artinSchreierCover p _
    (scalar k _ a * AffineSpace.coord (Spec (.of k)) PUnit.unit)

/-- Lift a specified root by the quotient and pullback universal properties. -/
private theorem cover_root_lift (n : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤))
    (T : Scheme.{u}) (x : T ⟶ X) (t : Γ(T, ⊤))
    (ht : t ^ n - t = x.appTop f) :
    ∃ s : Over.mk x ⟶ artinSchreierCover n X f,
      s.left.appTop (artinSchreierCoverCoordinate n X f) = t := by
  let R := AdjoinRoot (artinSchreierCoverPolynomial n X f)
  have hroot : (artinSchreierCoverPolynomial n X f).eval₂ x.appTop.hom t = 0 := by
    simp only [artinSchreierCoverPolynomial, Polynomial.eval₂_sub,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, ht, sub_self]
  let φ : R →+* Γ(T, ⊤) := AdjoinRoot.lift x.appTop.hom t hroot
  let g : T ⟶ Spec (.of R) :=
    ΓSpec.adjunction.homEquiv T (.op (.of R)) (CommRingCat.ofHom φ).op
  have hg : (Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop = CommRingCat.ofHom φ :=
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _
  let α : Γ(X, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap _ _)
  have hc : x ≫ X.toSpecΓ = g ≫ Spec.map α := by
    apply ext_to_Spec
    change (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ X.toSpecΓ.appTop ≫ x.appTop =
      (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ (Spec.map α).appTop ≫ g.appTop
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, hg]
    apply CommRingCat.hom_ext
    ext r
    exact (AdjoinRoot.lift_of hroot).symm
  let s : Over.mk x ⟶ artinSchreierCover n X f :=
    Over.homMk (pullback.lift x g hc) (by
      change pullback.lift x g hc ≫ pullback.fst X.toSpecΓ (Spec.map α) = x
      exact pullback.lift_fst _ _ _)
  refine ⟨s, ?_⟩
  change (pullback.lift x g hc).appTop
    ((pullback.snd X.toSpecΓ (Spec.map α)).appTop
      ((Scheme.ΓSpecIso (.of R)).inv (AdjoinRoot.root _))) = t
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd]
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop) (AdjoinRoot.root _) = t
  rw [hg]
  exact AdjoinRoot.lift_root hroot

/-- The two specified zero roots exist, and the map with the trace-polynomial formula
carries one to the other. Combining with the evaluation equations in EtaleComparison
or CondensedComparison gives exactly the stated zero-stalk normalization, for the
same induced isomorphism (not an unrelated isomorphism).
Source: blueprint lem-wft-as-comparison (3) (blueprint: lem-wft-as-comparison).

Proof: at the origin x=0 the polynomial equations admit the root 0. The quotient-ring
universal property constructs the corresponding section over Spec k. Substitution
of y=0 into sum_i (ay)^(p^i) gives u=0. Evaluation of a pulled-back eigenfunction at
y=0 is evaluation of the original eigenfunction at u=0, by the induced-map equation
of (2), or its adjunct etaleEvaluation / condensedEvaluation. -/
theorem artinSchreier_trace_origin (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k] (a : kˣ)
    (h : originQCover k ⟶ originPCover p k (a : k))
    (hh : h.left.appTop
      (artinSchreierCoverCoordinate p _
        (scalar k _ (a : k) * AffineSpace.coord (Spec (.of k)) PUnit.unit)) =
      ∑ i ∈ Finset.range (Module.finrank (ZMod p) k),
        ((originQCover k).hom.appTop (scalar k _ (a : k)) *
          artinSchreierCoverCoordinate (Fintype.card k) _
            (AffineSpace.coord (Spec (.of k)) PUnit.unit)) ^ (p ^ i)) :
    ∃ s : Over.mk (AffineSpace.zeroSection PUnit (Spec (.of k))) ⟶ originQCover k,
      s.left.appTop (artinSchreierCoverCoordinate (Fintype.card k) _
        (AffineSpace.coord (Spec (.of k)) PUnit.unit)) = 0 ∧
      (s ≫ h).left.appTop (artinSchreierCoverCoordinate p _
        (scalar k _ (a : k) * AffineSpace.coord (Spec (.of k)) PUnit.unit)) = 0 := by
  classical
  obtain ⟨s, hs⟩ := cover_root_lift (Fintype.card k) _
    (AffineSpace.coord (Spec (.of k)) PUnit.unit) _
    (AffineSpace.zeroSection PUnit (Spec (.of k))) 0 (by
      rw [zero_pow (Fintype.card_pos.ne'), sub_zero,
        AffineSpace.zeroSection_appTop_coord])
  refine ⟨s, hs, ?_⟩
  change (s.left ≫ h.left).appTop _ = 0
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hh]
  simp only [map_sum, map_pow, map_mul, hs, mul_zero,
    zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), Finset.sum_const_zero]

end AlgebraicGeometry.ArtinSchreierTrace
