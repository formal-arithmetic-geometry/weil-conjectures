/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # A generic stalk detects kernels in a locally constant sheaf

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-lisse-generic-kernel`
(blueprint: lem-weil-pbc-lisse-generic-kernel).
-/

@[expose] public section

universe u₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A morphism from a locally constant abelian étale sheaf is mono when its
geometric generic stalk map is mono. Local constancy is that of
`def-weil-pbc-etale-sheaves`, applied to the underlying sheaf of sets.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-lisse-generic-kernel`,
node `lem-weil-pbc-lisse-generic-kernel` (blueprint: lem-weil-pbc-lisse-generic-kernel).
Proof:
1. Set `N = ker φ`. Exactness of geometric stalks
   (`prop-weil-pbc-geometric-stalks-exact`) gives injective maps from stalks of `N`
   to stalks of `F` and a zero generic stalk of `N`. If `N` were nonzero,
   `lemma-weil-pbc-geometric-stalk-conservative` would give a nonzero geometric germ.
   Choose an étale cover member `V` on which the underlying sheaf of sets of `F` is
   isomorphic to the constant sheaf of a set `M` (`def-weil-pbc-etale-sheaves`,
   `def-weil-pbc-constant-sheaf`).
   Lift the geometric point to `V`: the nonempty étale fibre over its algebraically
   closed field has a rational point. Pointed neighbourhoods over `V` are cofinal
   among those on `X`, by fibre products (`def-weil-pbc-geometric-stalks`), so both
   stalks are unchanged. Represent the nonzero germ by a section `s` of `N` on a
   pointed neighbourhood. The constant-sheaf stalk formula
   (`lem-weil-pbc-constant-sheaf-geometric-stalk`) identifies the germs of the image
   of `s` in `F` and of the zero section of `F` with elements `m ≠ z` of `M`.
   Equality in a filtered colimit holds after refinement: shrink to a nonempty pointed
   étale neighbourhood `W` where the image of `s` is constantly `m` and the zero
   section is constantly `z`.
2. The image of `W → X` is open by `lem-weil-pbc-flat-lfp-open`, since étale maps
   are flat and locally of finite presentation. It is nonempty and hence contains
   the generic point. The fibre over the chosen geometric generic point is
   nonempty and étale over an algebraically closed field, so has a rational point.
   At this pointed neighbourhood the section `s` of `N` has zero germ, since its
   generic stalk is zero. Its image in `F` nevertheless has nonzero germ: cofinality
   identifies this with the stalk of the constant sheaf on `V`, and
   `lem-weil-pbc-constant-sheaf-geometric-stalk` sends `m ≠ z` to distinct germs.
   This contradiction gives `N = 0`, and therefore `φ` is a monomorphism.
-/
theorem mono_of_mono_generic_stalk
    (X : Scheme.{u₂}) (hX : IsIrreducible (Set.univ : Set X))
    (hne : Nonempty X) (η : X)
    (hη : IsGenericPoint η (Set.univ : Set X))
    (Ω : Type u₂) [Field Ω] [IsAlgClosed Ω]
    (barη : Spec (.of Ω) ⟶ X) (hbarη : barη default = η)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u₂ + 1})
    (hF : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u₂ + 1})).obj F))
    (φ : F ⟶ G)
    (hφ : Mono ((pointSmallEtale barη).sheafFiber.map φ)) : Mono φ := by
  sorry


end AlgebraicGeometry.Scheme
