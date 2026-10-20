# AlgebraicGeometry.exists_invertible_of_cech_transition

## Reason

The assigned retire item in coord/retire-items.tsv identifies this Sheaf theorem as a duplicate of the proved upstream theorem. No module currently imports the Sheaf copy. The source theorem has exactly the same conclusion and omits only the redundant hid and hinv hypotheses, which the old proof explicitly clears. Withdraw the Sheaf copy and repoint the existing node, preserving the source library verbatim.

## Old

In Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle:

```lean
theorem exists_invertible_of_cech_transition
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hcover : ⨆ a, U a = ⊤)
    (g : ∀ a b, Γ(X, U a ⊓ U b)ˣ)
    (hid : ∀ a, g a a = 1)
    (hinv : ∀ a b (W : X.Opens) (ha : W ≤ U a) (hb : W ≤ U b),
      Units.map (X.presheaf.map (homOfLE (le_inf hb ha)).op).hom.toMonoidHom (g b a) =
        (Units.map (X.presheaf.map (homOfLE (le_inf ha hb)).op).hom.toMonoidHom (g a b))⁻¹)
    (hcoc : ∀ a b c (W : X.Opens)
      (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c),
      Units.map (X.presheaf.map (homOfLE (le_inf ha hc)).op).hom.toMonoidHom (g a c) =
        Units.map (X.presheaf.map (homOfLE (le_inf ha hb)).op).hom.toMonoidHom (g a b) *
          Units.map (X.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom (g b c)) :
    ∃ (L : X.Modules) (e : ∀ a, Γ(L, U a)),
      L.IsInvertible ∧ (∀ a, IsFreeGenerator (e a)) ∧
      (∀ a b, L.presheaf.map (homOfLE inf_le_left).op (e a) =
        (g a b).val • L.presheaf.map (homOfLE inf_le_right).op (e b)) ∧
      ∀ (L' : X.Modules) (e' : ∀ a, Γ(L', U a)),
        (∀ a, IsFreeGenerator (e' a)) →
        (∀ a b, L'.presheaf.map (homOfLE inf_le_left).op (e' a) =
          (g a b).val • L'.presheaf.map (homOfLE inf_le_right).op (e' b)) →
        ∃! f : L' ≅ L, ∀ a, f.hom.app (U a) (e' a) = e a
```

## New

The Sheaf module is withdrawn. The node now names the existing declaration in WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle:

```lean
theorem exists_invertible_of_cech_transition
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hcover : ⨆ a, U a = ⊤)
    (g : ∀ a b, Γ(X, U a ⊓ U b)ˣ)
    (hcoc : ∀ a b c (W : X.Opens)
      (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c),
      Units.map (X.presheaf.map (homOfLE (le_inf ha hc)).op).hom.toMonoidHom (g a c) =
        Units.map (X.presheaf.map (homOfLE (le_inf ha hb)).op).hom.toMonoidHom (g a b) *
          Units.map (X.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom (g b c)) :
    ∃ (L : X.Modules) (e : ∀ a, Γ(L, U a)),
      L.IsInvertible ∧ (∀ a, IsFreeGenerator (e a)) ∧
      (∀ a b, L.presheaf.map (homOfLE inf_le_left).op (e a) =
        (g a b).val • L.presheaf.map (homOfLE inf_le_right).op (e b)) ∧
      ∀ (L' : X.Modules) (e' : ∀ a, Γ(L', U a)),
        (∀ a, IsFreeGenerator (e' a)) →
        (∀ a b, L'.presheaf.map (homOfLE inf_le_left).op (e' a) =
          (g a b).val • L'.presheaf.map (homOfLE inf_le_right).op (e' b)) →
        ∃! f : L' ≅ L, ∀ a, f.hom.app (U a) (e' a) = e a
```

The upstream declaration and all upstream consumers are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle | E7 | Withdraw unused duplicate; repoint its node to upstream. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle --uses AlgebraicGeometry.exists_invertible_of_cech_transition` reports zero downstream modules, and only the retiring module itself as a textual declaration user. The historical consumers listed in the retirement inventory already use the upstream module; their Sheaf copies are absent. No consumer adaptation is required. No target signature or definition changes.

## Status

landed 20261020T141308-L-2032954 2026-10-20 (merge of deliver/E7/Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle)
