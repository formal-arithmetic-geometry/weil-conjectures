# AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsRestriction_smul

## Reason

The old pointwise specialization exceeds the 60-second single-file kernel checking limit.
The same semilinearity statement as an equality of additive maps compiles within that limit.
The second reader independently tried to recover the verbatim original pointwise signature
by evaluating the proved map equality at a section; this also timed out after 60 seconds.
For modules M and N and an additive map rho, the proved private lemma `smulHom_eq_iff`
states precisely that `M.smul a ≫ rho = rho ≫ N.smul b` is equivalent to
`∀ s, rho (a • s) = b • rho s`. Thus this is an equivalent interface, with no added
hypothesis or weakened conclusion. The blueprint statement stays unchanged.

The coefficient map is still `g.left.appTop`; the source module is still U tensor-pullback
and the target module is still V tensor-pullback. All definitions keep their original bodies.
The existing tensor irreducibility controls are moved before the section-map definitions,
and the existing scheme-module instance gets local priority 2000 to control elaboration.
No such setting is exported.

## Old

```lean
theorem etaleTensorSectionsRestriction_smul {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (g : V ⟶ U) (a : Γ(U.left, ⊤))
    (s : Γ((tensorPullback U.hom).obj F, ⊤)) :
    etaleTensorSectionsRestriction F g (a • s) =
      g.left.appTop a • etaleTensorSectionsRestriction F g s
```

## New

```lean
theorem etaleTensorSectionsRestriction_smul {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (g : V ⟶ U) (a : Γ(U.left, ⊤)) :
    ((tensorPullback U.hom).obj F).smul a ≫ etaleTensorSectionsRestriction F g =
      etaleTensorSectionsRestriction F g ≫
        ((tensorPullback V.hom).obj F).smul (g.left.appTop a)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleTensorSections --uses
etaleTensorSectionsRestriction_smul` lists only its declaring module as a name occurrence.
A search of both library roots finds no callers. The 197 downstream importers therefore
need no adaptation: every definition, the identity/composition interfaces and the presheaf
are unchanged. No target statement or target-used definition changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleTensorSections | E3 | Equivalent map form of semilinearity; no internal callers |

## Status

landed 20261013T072345-L-1117686 2026-10-13 (merge of deliver/E3/Sheaf.AlgebraicGeometry.EtaleTensorSections)
