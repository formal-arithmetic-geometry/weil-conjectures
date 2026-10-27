# internal_scalar_mate_projection proof commands

## Reason

Preflight requests a change record because new local reducibility attributes and
proof elaboration options are commands outside declaration proof bodies. They are
used only after the original definitions, to keep the large derived tensor and
section functor constructions abstract during the category calculations. Existing
public signatures, public imports and definition bodies are unchanged. The new
normalization statements have their own new modules and nodes.

## Old

Existing signature, verbatim:

```lean
theorem internal_scalar_mate_projection (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hY : TensorNormalized a Y tY)
    (hlam : PullNormalized a f lam) :
    IsIso (scalarRestrictionPush a f) ∧
    ScalarMatePullEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      (V a Y).map ((rho a f lam).app K) ≫
          (scalarRestrictionPush a f).app ((D a X).obj K) ≫
          (F Λ f).map (tX.derived.hom.app K) =
        tY.derived.hom.app ((F Λ f).obj K) ≫ scalarProjection a f K) ∧
    ScalarMateSectionEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      IsIso ((rho a f lam).app K) ↔ IsIso (scalarProjection a f K)) ∧
    (∀ (K K' : DerivedCategory (Modules Λ X)) (q : K ⟶ K'),
      ((CondensedRing.derivedTensor Λ Y).map ((F Λ f).map q)).app (B a Y) ≫
        scalarProjection a f K' =
        scalarProjection a f K ≫
          (F Λ f).map (((CondensedRing.derivedTensor Λ X).map q).app (B a X)))
```

The item ended its original definitions and proceeded directly to the docstring
and theorem `internal_scalar_mate_projection`, with its unchanged signature and
one sorry. There were no intervening private proof helpers or local proof options.

## New

Preserved signature, verbatim:

```lean
theorem internal_scalar_mate_projection (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hY : TensorNormalized a Y tY)
    (hlam : PullNormalized a f lam) :
    IsIso (scalarRestrictionPush a f) ∧
    ScalarMatePullEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      (V a Y).map ((rho a f lam).app K) ≫
          (scalarRestrictionPush a f).app ((D a X).obj K) ≫
          (F Λ f).map (tX.derived.hom.app K) =
        tY.derived.hom.app ((F Λ f).obj K) ≫ scalarProjection a f K) ∧
    ScalarMateSectionEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      IsIso ((rho a f lam).app K) ↔ IsIso (scalarProjection a f K)) ∧
    (∀ (K K' : DerivedCategory (Modules Λ X)) (q : K ⟶ K'),
      ((CondensedRing.derivedTensor Λ Y).map ((F Λ f).map q)).app (B a Y) ≫
        scalarProjection a f K' =
        scalarProjection a f K ≫
          (F Λ f).map (((CondensedRing.derivedTensor Λ X).map q).app (B a X)))
```

The original theorem has the same signature, now with a complete proof from the
two new normalization lemmas. Before it, proved private helpers formalize mate
calculus, coefficient transport, conservativity and naturality. Local irreducibility
attributes prevent elaboration from unfolding the large derived constructions;
local reducibility attributes expose only the scalar and section interface wrappers.
`backward.isDefEq.respectTransparency.types` is false and
`backward.defeqAttrib.useBackward` is true in this proof section. There is no
change to the data, statement, instance or visibility of any existing declaration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalScalarMateProjection | J3 | Proof commands and private proved helpers only; original public declarations unchanged. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | R9 | Only downstream importer found by tools/downstream.py. No adaptation: local attributes do not escape this module and the theorem signature is unchanged. |

## Status

landed 20261024T190112-L-3934369 2026-10-24 (merge of deliver/J3/Sheaf.Paper.InternalScalarMateProjection)
