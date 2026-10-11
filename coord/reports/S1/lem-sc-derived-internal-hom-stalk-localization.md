## Worker report

(Restated by reviewer R-dsl for the merged statement.)

The module states `AlgebraicGeometry.derivedInternalHom_stalk_localization` in
`Sheaf.Paper.DerivedInternalHomStalkLocalization` for the sheaf-dag statement of the node
(the delivered statement correction was reverted: it named an error of an earlier Lean
draft, `Abelian.Ext (Int.toNat i)`, not of the node, whose statement already asks for
`H^i` of the derived internal Hom on the one-point ringed site for every `i : ℤ`).

## Second reading by S1

(Restated by reviewer R-dsl.) Binders: `X : Scheme` with `[CompactSpace X]` and `[IsLocallyNoetherian X]`; the derived
category instances of `SheafOfModules (moduleRings X.toRingedSpace)` and of the one-point
site `CochainComplex.onePointRingSheaf (O_{X,x})`; `F G` sheaves of modules with `F`
coherent (`RingedSpace.IsCoherent`); `x : X`; `i : ℤ`.

Conclusion: `Nonempty (… ≃ₗ[X.presheaf.stalk x] …)` between the module stalk
(`RingedSpace.moduleStalkFunctor`) of `H^i(derivedInternalHom (F[0], G[0]))` and the value at
the unique object of `H^i(derivedInternalHom_{O_{X,x}} (F_x[0], G_x[0]))` on the one-point
site, where `F_x`, `G_x` are the module stalks placed on the one-point site through
`PresheafOfModules.constFunctor` along the identity cocone (the bottom topology makes every
presheaf a sheaf, `Presheaf.isSheaf_bot`).

Reviewer change: the delivered left side was the raw `Ab`-stalk and the conclusion an
additive equivalence `≃+`; it now uses `moduleStalkFunctor` (STATE.md: module stalks via
`moduleStalkFunctor`) and an `O_{X,x}`-linear equivalence, as the canonical isomorphism of
the node is one of `O_{X,x}`-modules.
