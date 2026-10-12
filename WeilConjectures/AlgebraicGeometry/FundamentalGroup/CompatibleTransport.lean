/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Yoneda

/-!
# Section-compatible transport for finite étale local models

Let `E` be a sheaf of sets on the small étale site of a scheme `T`, let `U` be étale over `T`,
let `Q` be finite étale over `U`, and let `e` represent the restriction of `E` to `U` by `Q`:
for every `V` étale over `U`, `e` identifies `E(V → U → T)` with the `U`-morphisms `V ⟶ Q`.
A *compatible natural transport* sends, for scheme maps `a b : S ⟶ U` with the same
composite to `T`, the `Q`-points above `a` to `Q`-points above `b`, compatibly with
precomposition and with the identification `e` on étale sources.

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteLocalModelCompatibleTransport`
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}}

/-- A *natural section-compatible transport* for a sheaf of sets `E` on the small étale site of
`T`, an object `U` of that site, a finite étale `Q ⟶ U` and a representation
`e : E|_U ≅ Hom_U(-, Q)` of the restriction of `E` along `U ⟶ T`. It consists of maps sending
the `Q`-points above `a : S ⟶ U` to `Q`-points above `b : S ⟶ U` whenever `a` and `b` have the
same composite to `T`; these commute with precomposition, and on étale sources they send the
point corresponding to a section `s` under `e` at `a` to the point corresponding to `s` at `b`.
(blueprint: `def-weil-pbc-finite-local-model-compatible-transport`) -/
structure FiniteLocalModelCompatibleTransport (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : Over U.left) [IsFinite Q.hom] [Etale Q.hom]
    (e : (MorphismProperty.Over.map ⊤ U.prop).op ⋙ E.obj ≅
      (MorphismProperty.Over.forget @Etale ⊤ U.left).op ⋙ uliftYoneda.{u + 1}.obj Q) where
  /-- The transport of `Q`-points above `a` to `Q`-points above `b`. -/
  transport {S : Scheme.{u}} (a b : S ⟶ U.left) (hab : a ≫ U.hom = b ≫ U.hom) :
    {x : S ⟶ Q.left // x ≫ Q.hom = a} → {y : S ⟶ Q.left // y ≫ Q.hom = b}
  /-- The transport commutes with precomposition. -/
  transport_comp {S S' : Scheme.{u}} (g : S' ⟶ S) (a b : S ⟶ U.left)
    (hab : a ≫ U.hom = b ≫ U.hom) (x : {x : S ⟶ Q.left // x ≫ Q.hom = a}) :
    (transport (g ≫ a) (g ≫ b) (by simp only [assoc, hab])
      ⟨g ≫ x.1, by rw [assoc, x.2]⟩).1 = g ≫ (transport a b hab x).1
  /-- On étale sources, the transport sends the point corresponding to a section `s` under `e`
  at `a` to the point corresponding to `s` at `b`. -/
  transport_section {S : Scheme.{u}} (a b : S ⟶ U.left) (hab : a ≫ U.hom = b ≫ U.hom)
    (ha : Etale a) (hb : Etale b)
    (s : E.obj.obj (op ((MorphismProperty.Over.map ⊤ U.prop).obj
      (MorphismProperty.Over.mk ⊤ a ha)))) :
    transport a b hab ⟨(e.hom.app (op (MorphismProperty.Over.mk ⊤ a ha)) s).down.left,
        Over.w _⟩ =
      ⟨(e.hom.app (op (MorphismProperty.Over.mk ⊤ b hb))
        (E.obj.map (MorphismProperty.Over.homMk (𝟙 S) (by simpa using hab.symm)).op s)).down.left,
        Over.w _⟩

end AlgebraicGeometry.Scheme
