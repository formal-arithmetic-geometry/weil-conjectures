/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker F1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Invariants
public import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
public import Sheaf.RepresentationTheory.DiscreteContinuousRep

/-!
# Etale modules on a field and discrete Galois modules

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-exc-field-discrete-modules.md`,
node `lem-exc-field-discrete-modules` (blueprint: lem-exc-field-discrete-modules).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] IsSepClosure.sep_closed in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- (blueprint: lem-exc-field-discrete-modules)
Let `K` be a field with separable closure `Ks`, `G = Gal(Ks/K)` with its Krull topology, and
`A` a finite commutative ring. The geometric fibre functor at the geometric point
`Spec Ks → Spec K` is an equivalence `E` from etale `A`-module sheaves on `Spec K` to discrete
continuous `A[G]`-modules: `i` identifies the underlying `A`-module of `E F` naturally with
the geometric stalk of `F`, and the `G`-action of `E F` is the Galois action on the stalk
(a germ represented at a lift `x` is sent by `g` to the same section at `x ∘ Spec g`).
The section functor at `Spec K` corresponds to the invariants functor (`σ`). An equivalence
of abelian categories is exact.

Proof:
1. By `lem-exc-abelian-sheaves-gmodules`, the geometric stalk at `Spec Ks`
(`def-weil-pbc-geometric-stalks`) is an equivalence from abelian sheaves on the small etale
site to discrete `G`-modules, compatible with the sheaf-of-sets/`G`-set equivalence.
2. An `A`-module sheaf is an abelian sheaf with a ring map `A → End(F)`; the additive fully
faithful equivalence transports it to `A → End_G(M)`, a discrete continuous `A[G]`-module
(`def-exc-continuous-cohomology`), and back.
3. For finite separable `L/K` with `H = Gal(Ks/L)`, Yoneda gives
`F(Spec L) = Hom(h_{Spec L}, F)`; by `lem-exc-etale-sheaves-gsets-point` the stalk of
`h_{Spec L}` is the `G`-set of `K`-embeddings `L → Ks`, i.e. `G/H`, so full faithfulness gives
`F(Spec L) = Hom_G(G/H, M) = M^H`, naturally in `L`; at `L = K` this is `M^G`.
4. The equivalence is one of abelian categories (`lem-exc-discrete-modules-abelian`), hence
exact; the stalk functor is exact by `prop-weil-pbc-geometric-stalks-exact`. -/
theorem etaleModuleSheaves_equiv_discreteGModules
    (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
    (A : Type v) [CommRing A] [Finite A] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ks))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let D := Rep.DiscreteContinuousRep.{v, u, max (u + 1) v} A G
    let U : D ⥤ Rep.{max (u + 1) v} A G := ObjectProperty.ι _
    ∃ (E : Sheaf J (ModuleCat.{max (u + 1) v} A) ≌ D)
      (i : E.functor ⋙ U ⋙ Rep.RepToAction A G ⋙
          Action.forget (ModuleCat.{max (u + 1) v} A) G ≅ p.sheafFiber)
      (_σ : (sheafSections J (ModuleCat.{max (u + 1) v} A)).obj (op (Etale.mk (𝟙 S))) ≅
          E.functor ⋙ U ⋙ Rep.invariantsFunctor A G),
      ∀ (F : Sheaf J (ModuleCat.{max (u + 1) v} A)) (g : G)
          (X : S.Etale) (x x' : p.fiber.obj X)
          (_hx : x'.left = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (i.hom.app F) ((E.functor.obj F).obj.ρ g
          ((i.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z := by
  sorry

end AlgebraicGeometry.Scheme
