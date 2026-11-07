/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.TensorPullback

/-!
# Base change, fibres and induced sections

Source: Stacks Project, Tags 01JX, 01K0, 0095; blueprint
`sec-abelian-varieties/def-sc-jacobian/def-pc-base-change.md`
(blueprint: def-pc-base-change).

`(Over.pullback T.hom).obj (Over.mk f)` is `X_T` over `T`: its underlying scheme is
`pullback f T.hom`, its structure map `pr_T` is `pullback.snd`, and its map `f_T` to `X`
is `pullback.fst`. The functor's map is `h_T` for an `S`-morphism `h`.
`baseChangeMap f g` is the existing map `g_X`, and `sectionBaseChange` is the existing
induced section. Geometric points use the recorded unbundled description
`Spec (.of Ω) ⟶ T.left` with `Ω` algebraically closed, and `Scheme.SpecToEquivOfField`.

## Main definitions

- `Scheme.Modules.moduleBaseChange`: module pullback along `g_X`.
- `Scheme.Hom.geometricFiberAt`: the fibre over a chosen algebraic closure of `κ(t)`.
- The remaining statements record the comparison and section clauses of the node.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}}

/-- Module base change along `g : T' ⟶ T` over `S` is `g_X^*`.
Source: Stacks, Tag 0095 (blueprint: def-pc-base-change). -/
def Scheme.Modules.moduleBaseChange (f : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    (Limits.pullback f T.hom).Modules ⥤ (Limits.pullback f T'.hom).Modules :=
  Scheme.Modules.tensorPullback (baseChangeMap f g)


/-- The geometric fibre `X ×_S Spec Ω` at `t`, for a chosen algebraic closure `Ω` of `κ(t)`.
The map from `Spec Ω` is induced by the residue-field embedding and the canonical point map.
Source: blueprint Definition def-pc-base-change; Stacks, Tags 01K0, 03PO
(blueprint: def-pc-base-change). -/
def Scheme.Hom.geometricFiberAt (f : X ⟶ S) (T : Over S) (t : T.left)
    (Ω : Type u) [Field Ω] [Algebra (T.left.residueField t) Ω]
    [IsAlgClosure (T.left.residueField t) Ω] : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫
    T.left.fromSpecResidueField t ≫ T.hom)


end
end AlgebraicGeometry
