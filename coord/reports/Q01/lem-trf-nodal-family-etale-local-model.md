## Worker report

The module `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel` defines the
canonical universal chart `Spec ℤ[u,v,a]/(uv-a)` in each scheme universe, its map to
`Spec ℤ[a]`, the map induced by a global function `a ↦ h`, and the completed local
ring and power-series quotient used in the fibre hypothesis.  It states
`AlgebraicGeometry.exists_etale_nodal_local_model` with proof `sorry`.

The assumptions are rendered as follows.  The morphism is `f : X ⟶ S` with the
Mathlib classes `[Flat f]` and `[LocallyOfFinitePresentation f]`.  For every
`(Ω : Type u)` with `[Field Ω] [IsAlgClosed Ω]` and geometric point
`g : Spec (.of Ω) ⟶ S`, `IsEmpty (pullback (C := Scheme) f g)` gives the empty-fibre
clause.  The other branch is
`Scheme.IsPureDimension (pullback (C := Scheme) f g) 1`; its nonsmooth-point clause
uses the exact stalk criterion
`¬ ((geometricFiberProjection f Ω g).stalkMap z).hom.FormallySmooth` and a ring
isomorphism from the maximal-ideal completion
`AdicCompletion (IsLocalRing.maximalIdeal A) A` to
`MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`.  The distinguished point is
`x : X` with `x ∉ f.smoothLocus`, the Mathlib pointwise nonsmooth locus.

The conclusion existentially supplies `V U`, a global function `h : Γ(V, ⊤)`, maps
`v : V ⟶ S`, `uMap : U ⟶ X`, `w : U ⟶ V`, and
`m : U ⟶ pullback nodalModelBaseMap (nodalBaseMap h)`.  The conjunction renders,
clause by clause, `Etale v`, `Etale uMap`, `Etale m`, the triangle
`w ≫ v = uMap ≫ f`, the V-map condition
`m ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h) = w`, and a point
`z : U` with `uMap z = x`.

Dependency declarations used are Mathlib's `AlgebraicGeometry.Flat`,
`AlgebraicGeometry.LocallyOfFinitePresentation`, `IsAlgClosed`,
`AlgebraicGeometry.Scheme.SpecToEquivOfField`, `CategoryTheory.Limits.pullback`,
`AlgebraicGeometry.Scheme.IsPureDimension` from
`Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Smooth`,
`AlgebraicGeometry.Etale`, `AdicCompletion`, and `MvPowerSeries`.

Edge cases checked: empty geometric fibres are accepted by the disjunction; the
pure-dimension predicate is true on the empty scheme by its recorded definition;
`n = 0` is represented by the `Fin 2` nodal variables (the separate power-series
node supports zero variables); and the integer base is universe-lifted so the model
works for every scheme universe.  The relation specializes to `uv = 0` when `h = 0`.

Searches made: `msearch.py leanfinder` for an etale local model of a nodal family
returned only standard-etale and smooth-presentation declarations; `msearch.py
loogle` for `nodal uv h Etale` returned no hits; `msearch.py grep` for
`nodal|ordinary.double|uv.*h` found no matching Mathlib definition; `msearch.py
leansearch` for the Stacks statement returned only generic etale-locus results.
Direct `rg` searches of Mathlib, `WeilConjectures/`, and `lean/Sheaf` found no
existing declaration of this theorem or its universal nodal model.  The dependency
records were read and their declarations used directly.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q01

A fresh pass over the node and module matched each hypothesis and conclusion clause.
The fibre is the pullback along the explicitly quantified geometric point; the
nonsmooth condition is the stalk formal-smoothness complement, exactly the
Mathlib definition of `smoothLocus`.  The completed ring uses the maximal ideal of
that stalk, and the target quotient has the single relation `uv`.  The universal
model and its base map are canonical quotient constructions, and the final
conjunction contains both etale maps, the V-compatibility, the triangle over S,
and the required point over x.  No mismatch was found.
