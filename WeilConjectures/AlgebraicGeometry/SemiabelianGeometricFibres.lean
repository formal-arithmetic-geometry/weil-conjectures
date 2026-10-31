/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Semiabelian geometric fibres

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.3.3, semiabelian setting.
(blueprint: def-sfb-semiabelian-geometric-fibres)

A short exact fppf sequence is expressed by its actual kernel square and local
surjectivity of its quotient arrow. All group laws are the given group laws.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Every geometric fibre is an extension of an abelian variety by a split torus.
The kernel square identifies the entire scheme-theoretic kernel, while fppf local
surjectivity expresses epimorphy as fppf sheaves. Over the algebraically closed
field, a smooth connected group scheme is geometrically connected.

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.3.3, semiabelian setting.
(blueprint: def-sfb-semiabelian-geometric-fibres) -/
def HasSemiabelianGeometricFibres {S : Scheme.{u}} (G : Grp (Over S))
    [IsCommMonObj G.X] : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
    ∃ (r : ℕ) (A : Grp (Over (Spec (.of k))))
      (i : MultiplicativeType.splitTorus k r ⟶ (Over.pullback s).mapGrp.obj G)
      (q : (Over.pullback s).mapGrp.obj G ⟶ A),
      IsAbelianVariety A.X ∧
      IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus k r).X)
        q.hom.hom η[A.X] ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
        (yoneda.map q.hom.hom)

end AlgebraicGeometry
