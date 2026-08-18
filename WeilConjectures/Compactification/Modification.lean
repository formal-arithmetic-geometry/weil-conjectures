/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Admissible
public import WeilConjectures.Compactification.PartialSection
public import WeilConjectures.Compactification.Defs

/-!

# Elimination of indeterminacy, common modifications and graph extension

This file records the modification steps of the proof of Nagata's compactification
theorem, following the blueprint chapter "Nagata compactification", sections
"Boundary preparation" and "Common modifications and graph extension"
(proof order items 30–33):

- `AlgebraicGeometry.exists_admissibleBlowup_strictTransform_open`: **elimination of
  indeterminacy** (Stacks Project Tag 081S; blueprint
  `lemma:nagata-elimination-indeterminacy`): if `q : Z ⟶ X` is separated, of finite
  type and an isomorphism over a quasi-compact open `U` of the qcqs scheme `X`, then
  after a `U`-admissible blow-up the strict transform of `q` is an open immersion;
- `AlgebraicGeometry.Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup`:
  **transport of scheme-theoretic images through admissible blow-ups** (Stacks
  Project Tag 0F3Y; blueprint `lemma:nagata-scheme-image-strict-transform`): the
  scheme-theoretic image of a lift along a `U`-admissible blow-up is the strict
  transform of the scheme-theoretic image;
- `AlgebraicGeometry.CommonModification` and
  `AlgebraicGeometry.exists_commonModification`: **common modification of two models**
  (Stacks Project Tag 0F3X; blueprint `def:nagata-common-modification`,
  `lemma:nagata-common-modification`): two separated finite-type models of a common
  open `U` admit `U`-admissible blow-ups which glue along a common copy of the
  modified `U`-locus to a separated finite-type model;
- `AlgebraicGeometry.Compactification.exists_properExtension`: **graph extension**
  (Stacks Project Tag 0F3Z; blueprint `def:nagata-graph-extension`,
  `lemma:nagata-graph-extension`): a compactification of a quasi-compact open
  `V ⊆ U` extends, after a `V`-admissible blow-up of the compactification, to a
  proper morphism `V^gr ⟶ U` restricting to the identity on `V`;
- `AlgebraicGeometry.exists_admissibleBlowup_strictTransform_isIso_near_closure`:
  **isomorphism near a boundary closure** (Stacks Project Tag 0F3W; blueprint
  `def:nagata-isomorphism-near-closure`, `lemma:nagata-isomorphism-near-closure`): a
  proper morphism which is an isomorphism over a neighbourhood of a closed piece `T`
  of `U` acquires, after a `U`-admissible blow-up, a strict transform which is an
  isomorphism over a neighbourhood of the closure of `T`.

The finite-type helper lemmas of the blueprint
(`lemma:nagata-proper-to-separated-target` = Mathlib's `IsProper.of_comp`,
`lemma:nagata-finite-type-to-separated-target`,
`lemma:nagata-open-immersion-qc-over-separated-target`) are recorded as
`AlgebraicGeometry.Nagata.locallyOfFiniteType_of_comp_of_isSeparated` and
`AlgebraicGeometry.Nagata.quasiCompact_of_comp_of_isSeparated`.

## Dependency structure

`exists_admissibleBlowup_strictTransform_open` (Tag 081S) is the only *primitive*
obligation of this file: `schemeTheoreticImage_after_admissibleBlowup` (0F3Y),
`exists_commonModification` (0F3X), `Compactification.exists_properExtension` (0F3Z)
and `exists_admissibleBlowup_strictTransform_isIso_near_closure` (0F3W) are all
consumers of it, and the two-open compactification theorem (proof order items 43–48)
consumes those. Tag 081S in turn is the application of Raynaud–Gruson flattening,
Stacks Tags 0815 and 081R, which this development does not yet state; see the
"Route" section of the module docstring of `WeilConjectures.Blowup.Admissible`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Nagata

variable {T Y B : Scheme.{u}}

/-- **Finite type over a separated target**, local finite type part: in a commutative
triangle `T ⟶ Y ⟶ B` with `T ⟶ B` locally of finite type, the first leg is locally of
finite type. (Blueprint: `lemma:nagata-finite-type-to-separated-target`; no
separatedness is needed for this part.) -/
theorem locallyOfFiniteType_of_comp_of_isSeparated (f : T ⟶ Y) (g : Y ⟶ B)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f :=
  locallyOfFiniteType_of_comp f g

/-- **Quasi-compactness over a separated target**: in a commutative triangle
`T ⟶ Y ⟶ B` with `T ⟶ B` quasi-compact and `Y ⟶ B` separated, the first leg is
quasi-compact. Together with `locallyOfFiniteType_of_comp_of_isSeparated` this is the
finite-type statement `lemma:nagata-finite-type-to-separated-target` of the blueprint;
applied to an open immersion `T ⟶ Y` it is
`lemma:nagata-open-immersion-qc-over-separated-target`. -/
theorem quasiCompact_of_comp_of_isSeparated (f : T ⟶ Y) (g : Y ⟶ B) [IsSeparated g]
    [QuasiCompact (f ≫ g)] : QuasiCompact f :=
  MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) f g
    inferInstance ‹_›

end Nagata

/-- **Elimination of indeterminacy** (Stacks Project Tag 081S): let `X` be a qcqs
scheme, `U ⊆ X` a quasi-compact open and `q : Z ⟶ X` separated, of finite type and an
isomorphism over `U`. Then there is a `U`-admissible blow-up `X' ⟶ X` such that the
strict transform `Z' ⟶ X'` of `q` is an open immersion.

(Blueprint: `def:nagata-elimination-indeterminacy`,
`lemma:nagata-elimination-indeterminacy`; proof order item 30.) -/
theorem exists_admissibleBlowup_strictTransform_open
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) {Z : Scheme.{u}} (q : Z ⟶ X)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (hq : IsIso (q ∣_ U)) :
    ∃ B : AdmissibleBlowup X U, IsOpenImmersion (B.strictTransformMap q) := by
  -- The Stacks proof flattens the (finite type, flat over `U`) structure sheaf datum
  -- of `q` by a `U`-admissible blow-up (Tags 0815 and 081R) and observes that a flat,
  -- finitely presented strict transform which is a monomorphism over `U` is an open
  -- immersion. Neither flattening theorem is available yet; this is the one primitive
  -- obligation of the modification layer.
  sorry

section ImageTransport

variable {S X Y V : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S)

/-- **Scheme-theoretic images and admissible blow-ups** (Stacks Project Tag 0F3Y):
let `h : V ⟶ X ×_S Y` be quasi-compact and quasi-separated whose first projection
factors through a quasi-compact open `U ⊆ X`, and let `B` be a `U`-admissible blow-up
of `X`. For every lift `h' : V ⟶ X' ×_S Y` of `h` along the base-changed blow-up
`X' ×_S Y ⟶ X ×_S Y` (such a lift exists because the blow-up is an isomorphism over
`U`), the scheme-theoretic image of `h'` is the strict transform of the
scheme-theoretic image of `h`, as closed subschemes of `X' ×_S Y`.

The statement is in kernel ideal sheaf form: both closed subschemes of `X' ×_S Y` are
recorded by the kernels of the corresponding closed immersions. The proof is the
affine saturation computation of the blueprint
(`lemma:nagata-scheme-image-affine-saturation`,
`lemma:nagata-scheme-image-transport-strict-transform`), currently awaiting the
strict-transform chart algebra.
(Blueprint: `lemma:nagata-scheme-image-strict-transform`; proof order item 31.) -/
theorem Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup
    {U : X.Opens} (B : AdmissibleBlowup X U)
    (h : V ⟶ pullback x y) [QuasiCompact h] [QuasiSeparated h]
    (hfac : Set.range (h ≫ pullback.fst x y) ⊆ (U : Set X))
    (h' : V ⟶ pullback (B.π ≫ x) y) [QuasiCompact h']
    (hlift : h' ≫ Nagata.partialSectionOpenι x y B.π = h) :
    h'.ker =
      (AlgebraicGeometry.strictTransformι h.imageι
          (Nagata.partialSectionOpenι x y B.π)
          (pullback.fst x y ⁻¹ᵁ B.preservedOpen) ≫
        pullback.snd h.imageι (Nagata.partialSectionOpenι x y B.π)).ker := by
  sorry

end ImageTransport

section CommonModification

variable {S U X₁ X₂ : Scheme.{u}}

/-- The data of a **common modification** of two separated finite-type models `X₁`,
`X₂` of a common open `U` over `S` (Stacks Project Tag 0F3X): admissible blow-ups
`X'ᵢ ⟶ Xᵢ`, open immersions of both `X'ᵢ` into a glued scheme `W`, agreeing lifted
copies of `U`, such that the two opens cover `W` and `W` is separated and of finite
type over `S`.
(Blueprint: `def:nagata-common-modification`.) -/
structure CommonModification (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] where
  /-- The `U`-admissible blow-up of the first model. -/
  B₁ : AdmissibleBlowup X₁ j₁.opensRange
  /-- The `U`-admissible blow-up of the second model. -/
  B₂ : AdmissibleBlowup X₂ j₂.opensRange
  /-- The glued common modification. -/
  W : Scheme.{u}
  /-- The structure morphism of the common modification. -/
  w : W ⟶ S
  /-- The open immersion of the first modified model into the glued scheme. -/
  k₁ : B₁.X' ⟶ W
  /-- The open immersion of the second modified model into the glued scheme. -/
  k₂ : B₂.X' ⟶ W
  isOpenImmersion_k₁ : IsOpenImmersion k₁
  isOpenImmersion_k₂ : IsOpenImmersion k₂
  k₁_w : k₁ ≫ w = B₁.π ≫ s₁
  k₂_w : k₂ ≫ w = B₂.π ≫ s₂
  /-- The lift of `U` into the first modified model. -/
  u₁ : U ⟶ B₁.X'
  /-- The lift of `U` into the second modified model. -/
  u₂ : U ⟶ B₂.X'
  u₁_π : u₁ ≫ B₁.π = j₁
  u₂_π : u₂ ≫ B₂.π = j₂
  /-- The two copies of `U` in the glued scheme agree. -/
  u_glue : u₁ ≫ k₁ = u₂ ≫ k₂
  /-- The two modified models cover the glued scheme. -/
  cover : Set.range k₁ ∪ Set.range k₂ = Set.univ
  isSeparated_w : IsSeparated w
  locallyOfFiniteType_w : LocallyOfFiniteType w
  quasiCompact_w : QuasiCompact w

attribute [instance] CommonModification.isOpenImmersion_k₁
  CommonModification.isOpenImmersion_k₂ CommonModification.isSeparated_w
  CommonModification.locallyOfFiniteType_w CommonModification.quasiCompact_w

/-- **Existence of a common modification** (Stacks Project Tag 0F3X): two separated
finite-type models `X₁`, `X₂` over a qcqs base `S` of a common quasi-compact open `U`
admit a common modification: `U`-admissible blow-ups `X'ᵢ ⟶ Xᵢ` which glue along a
common open copy of the blown-up `U`-locus to a separated finite-type scheme over `S`.

The construction is the one of the blueprint: form the scheme-theoretic image
`X₁₂ ⊆ X₁ ×_S X₂` of `U`, eliminate the indeterminacy of both projections
(`exists_admissibleBlowup_strictTransform_open`), dominate the two center ideals by
their product (`Scheme.IdealSheafData.exists_blowup_mul_iso`) and extend the resulting
common blow-up of `X₁₂` across the open strict transforms.
(Blueprint: `lemma:nagata-common-modification`; proof order item 32.) -/
theorem exists_commonModification [CompactSpace S] [QuasiSeparatedSpace S]
    (sU : U ⟶ S) (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (hj₁ : j₁ ≫ s₁ = sU) (hj₂ : j₂ ≫ s₂ = sU)
    [IsSeparated s₁] [LocallyOfFiniteType s₁] [QuasiCompact s₁]
    [IsSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂] :
    Nonempty (CommonModification s₁ s₂ j₁ j₂) := by
  sorry

end CommonModification

section GraphExtension

variable {S U : Scheme.{u}}

/-- **Graph extension** (Stacks Project Tag 0F3Z): let `u : U ⟶ S` be separated and of
finite type over the qcqs scheme `S`, let `V ⊆ U` be a quasi-compact open and let
`c` be a compactification of `V ⟶ S`. Then there are a `V`-admissible blow-up
`B : Y^gr ⟶ c.Z` of the compactification, an open subscheme `V^gr ⊆ Y^gr` and a
morphism `ψ : V^gr ⟶ U` such that:

- `ψ` is proper;
- `V` embeds as an open subscheme of `V^gr` lifting `c.i` along `B.π`;
- `ψ` extends the inclusion `V ⟶ U`;
- the inverse image of `V` under `ψ` is exactly the embedded copy of `V`, and `ψ` is
  an isomorphism over `V`.

The construction is the graph construction of the blueprint: `V^gr` is the open
strict transform of the scheme-theoretic image of the graph `V ⟶ c.Z ×_S U`, supplied
by the partial-section lemma (`Nagata.partialSectionRestrictIso`), the image transport
lemma (`Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup`) and elimination of
indeterminacy (`exists_admissibleBlowup_strictTransform_open`); `ψ` is the second
projection, proper because `c.Z ×_S U ⟶ U` is proper
(`Nagata.isProper_imageι_fst`).
(Blueprint: `def:nagata-graph-extension`, `lemma:nagata-graph-extension`;
proof order item 33.) -/
theorem Compactification.exists_properExtension
    [CompactSpace S] [QuasiSeparatedSpace S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (V : U.Opens) (hV : IsCompact (V : Set U)) (c : Compactification (V.ι ≫ u)) :
    ∃ (B : AdmissibleBlowup c.Z c.i.opensRange) (Vgr : B.X'.Opens)
      (ψ : Vgr.toScheme ⟶ U) (v : V.toScheme ⟶ Vgr.toScheme),
      IsProper ψ ∧ IsOpenImmersion v ∧
      v ≫ Vgr.ι ≫ B.π = c.i ∧
      v ≫ ψ = V.ι ∧
      ((ψ ⁻¹ᵁ V : Vgr.toScheme.Opens) : Set Vgr.toScheme) = Set.range v ∧
      IsIso (ψ ∣_ V) ∧
      ψ ≫ u = Vgr.ι ≫ B.π ≫ c.g := by
  sorry

end GraphExtension

section IsomorphismNearClosure

/-- **Isomorphism near the closure of a boundary piece** (Stacks Project Tag 0F3W): let
`X` be qcqs, `U ⊆ X` a quasi-compact open, `q : Z ⟶ X` proper and `T ⊆ U` a subset
closed in `U` such that `q` is an isomorphism over an open neighbourhood `N` of `T`.
Then there is a `U`-admissible blow-up `B` of `X` such that the strict transform of `q`
is an isomorphism over an open neighbourhood of the closure of `T` in the blown-up
scheme.

The construction of the blueprint separates `T` from the complement of the maximal
isomorphism open of `q` (`Scheme.Hom.maximalIsomorphismOpen`) by the boundary
separation blow-up (`exists_admissibleBlowup_disjoint_closures`) and then eliminates
the indeterminacy of `q` (`exists_admissibleBlowup_strictTransform_open`) away from
the separated bad locus; a proper open immersion onto a scheme-theoretically dense
open is an isomorphism.
(Blueprint: `def:nagata-isomorphism-near-closure`,
`lemma:nagata-isomorphism-near-closure`; used for the improved comparison projection
of the two-open compactification theorem.) -/
theorem exists_admissibleBlowup_strictTransform_isIso_near_closure
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hT : IsClosed (U.ι ⁻¹' T))
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) :
    ∃ (B : AdmissibleBlowup X U) (N' : B.X'.Opens),
      closure (B.π ⁻¹' T) ⊆ (N' : Set B.X') ∧
      IsIso (B.strictTransformMap q ∣_ N') := by
  sorry

end IsomorphismNearClosure

end AlgebraicGeometry
