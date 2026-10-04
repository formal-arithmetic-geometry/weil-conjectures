/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Geometrically connected schemes

## Main statements

- `AlgebraicGeometry.GeometricallyConnected.of_geometricallyIrreducible`: a geometrically
  irreducible morphism is geometrically connected.
- `AlgebraicGeometry.GeometricallyConnected.of_isSepClosed`: a connected scheme over a
  separably closed field is geometrically connected.
- `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_section`: a connected scheme
  over a field with a rational point is geometrically connected.
- `AlgebraicGeometry.GeometricallyConnected.of_isOpenImmersion`: an irreducible scheme over a
  field with a nonempty geometrically connected open subscheme is geometrically connected.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A geometrically irreducible morphism is geometrically connected, since an irreducible space
is connected. -/
instance (priority := low) GeometricallyConnected.of_geometricallyIrreducible
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] : GeometricallyConnected f where
  geometrically_connectedSpace _ _ y _ fst snd h :=
    have := GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd h
    inferInstance

/-- A connected scheme over a separably closed field `k` is geometrically connected over `k`. -/
theorem GeometricallyConnected.of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [ConnectedSpace X] :
    GeometricallyConnected (X ↘ Spec (.of k)) :=
  sorry

/-- A connected scheme `X` over a field `k` with a `k`-rational point, that is, a section `s` of
its structure morphism `f`, is geometrically connected over `k`. -/
@[stacks 04KV]
theorem GeometricallyConnected.of_connectedSpace_of_section {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [ConnectedSpace X] (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) : GeometricallyConnected f :=
  sorry

/-- An irreducible scheme `Y` over a field `K` containing a nonempty open subscheme `X` which is
geometrically connected over `K` is geometrically connected over `K`. After a base change to a
field `L`, the open `X_L` is connected, and it is dense in `Y_L`: the projection `Y_L ⟶ Y` is
flat, hence generalizing, so every point of `Y_L` specializes from a point over the generic point
of `Y`, which lies in `X`. A space with a dense connected subset is connected. -/
theorem GeometricallyConnected.of_isOpenImmersion {K : Type u} [Field K] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] [Nonempty X] [IrreducibleSpace Y] (f : Y ⟶ Spec (.of K))
    [GeometricallyConnected (j ≫ f)] : GeometricallyConnected f where
  geometrically_connectedSpace L _ y Z fst snd h := by
    have hW : IsPullback (pullback.fst j fst) (pullback.snd j fst ≫ snd) (j ≫ f) y :=
      (IsPullback.of_hasPullback j fst).paste_vert h
    have : ConnectedSpace ↥(pullback j fst) :=
      GeometricallyConnected.geometrically_connectedSpace (f := j ≫ f) y _ _ hW
    have : Flat y := by
      rw [← Spec.map_preimage y, Flat.SpecMap_iff]
      algebraize [(Spec.preimage y).hom]
      exact (inferInstance : Module.Flat K L)
    have : Flat fst := MorphismProperty.of_isPullback h.flip ‹_›
    have hgen := Flat.generalizingMap fst
    have hη : genericPoint Y ∈ Set.range j.base := by
      obtain ⟨x⟩ := ‹Nonempty X›
      exact ((genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
        ⟨j.base x, trivial, x, rfl⟩
    have hdense : Dense (Set.range (pullback.snd j fst).base) := by
      refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun z ↦ ?_)
      obtain ⟨z', hz', hz'η⟩ := hgen (genericPoint_specializes (fst.base z))
      obtain ⟨x, hx⟩ := hη
      obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback x z' (hx.trans hz'η.symm)
      exact hz'.mem_closed (isClosed_closure) (subset_closure ⟨w, hw⟩)
    have hconn : _root_.IsConnected (Set.range (pullback.snd j fst).base) :=
      isConnected_range (pullback.snd j fst).base.hom.continuous
    have := hconn.closure
    rw [hdense.closure_eq] at this
    exact connectedSpace_iff_univ.mpr this

end AlgebraicGeometry
