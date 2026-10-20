# AlgebraicGeometry.Etale exceptional-pullback extraction repair

## Reason

Restore the current quarantined module after the 2026-10-20 upstream sync and repair the
stale-base return of delivery 33f05d00f2 (base e0d550965). The extraction retained a declaration-local
binder without its declaration and duplicated notation already supplied by upstream.
Reapply their removal against the current quarantine source. Also use the upstream
proper-pushforward theorem now supplying the private helper's exact conclusion, eliminating
its duplicate geometric proof and its obsolete Sheaf import. Public declarations,
signatures, attributes and proofs remain unchanged. Source-library files are untouched.

## Old

The quarantined Sheaf module imports:

```lean
public import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
```

Its Unbounded section ends:

```lean
@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

variable (Λ : Type*) [Ring Λ] [Linear Λ A] in
end Unbounded
```

The private helper's unchanged signature is:

```lean
private theorem exists_uniform_proper_dimension_bound
    {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] [CompactSpace T]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ d : ℕ, ∀ (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj G)
```

Its old proof constructs a fibre-dimension bound using `exists_fibre_dimension_bound`,
extends it to geometric fibres, and transports vanishing through proper base change.

## New

Remove that Sheaf import. The upstream public import supplies identical notation, so
Unbounded ends directly after its existing left-adjoint variable:

```lean
variable [(R(f)_![A]).IsLeftAdjoint]

end Unbounded
```

With the private helper signature unchanged, its new complete proof is:

```lean
by
  exact exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite p
```

The upstream theorem takes the same proper morphism and quasi-compact target and assumes
additive torsion, supplied by finiteness of Λ. It returns exactly the helper's existential
vanishing statement; no data is chosen from mere existence. The extraction comment is
wrapped at 100 characters.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | W8 | Compilation restored; unchanged public proofs and private helper signature; direct upstream helper proof. |

Exact import and declaration-use searches in lean/ and quarantine/ find no consumers of
the extracted module or its public amplitude theorems. No adaptations are required.
The removed import affects no public signature: all categories and functors are provided
by retained upstream imports. No target statement or definition changes. Public theorem
DAG proof routes stay identical; no node records need changing.

## Status

landed 20261020T151239-L-2654381 2026-10-20 (merge of deliver/W8/Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.Derived.UpperShriek)
