## Worker report

The single new module is `Sheaf.AlgebraicGeometry.NodalPointBlowupProjectiveFibres`.
Its only declaration is `AlgebraicGeometry.nodal_point_blowup_projective_fibres`, whose entire
proof is `sorry`. There is one new definition node recording existing definitions, no new Lean definitions,
dependency repairs, or statement corrections. The module docstring identifies Stacks models.tex Tags 0CDC and 0CDE and
divisors.tex Tag 02NS. The theorem docstring carries all six original proof steps verbatim,
including their dependency citations, wrapped to the required line width.

Two definition owners are added to `stmt_deps`: `def-sfb-arithmetic-nodal-model-origin` supplies
`DvrNodal.model`, `projection` and `IsOrigin`; `def-sfb-surface-point-blowup-data` supplies
`SurfacePointBlowup.pointIdeal`. Neither has a dependency path back to this item. The original
statement and all other original node fields are preserved. No private copies of these
constructions are introduced.

Hypothesis-by-hypothesis correspondence (all names below are in namespace AlgebraicGeometry
unless stated otherwise):

| Node hypothesis/object | Lean rendering |
| --- | --- |
| DVR R, uniformizer pi, S = Spec R | `R : CommRingCat.{u}`, `[IsDomain R]`, `[IsDiscreteValuationRing R]`, `π : R`, `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`; `Spec R` throughout |
| Noetherian X, meaning quasi-compact and locally Noetherian | `X : Scheme.{u}`, `[IsNoetherian X]`; Mathlib's class extends `IsLocallyNoetherian X` and `CompactSpace X` |
| H-projective f : X -> S | `f : X ⟶ Spec R`, `[IsHProjective f]`, the recorded finite-projective-space convention |
| Closed point of the special fibre | `x : X`, `hx : IsClosed ({x} : Set X)`, `hxs : f x = IsLocalRing.closedPoint R`; the special fibre is closed, so closedness here equals closedness in that fibre |
| Local injective etale extension of DVRs R -> R' | `R' : CommRingCat.{u}`, its domain/DVR instances, `ι : R ⟶ R'`, `[IsLocalHom ι.hom]`, `hι : Function.Injective ι.hom`, `[Etale (Spec.map ι)]` |
| pi remains a uniformizer | `hπ' : IsLocalRing.maximalIdeal R' = Ideal.span {ι π}` |
| Integer n >= 2 | `n : ℕ`, `hn : 2 ≤ n`; precisely the nonnegative integers satisfying the stated bound |
| Arithmetic model M_n, origin o | `DvrNodal.model R' (ι π) n` is the existing `Spec R'[a,b]/(ab-(ι π)^n)`; `ho : DvrNodal.IsOrigin R' (ι π) n (q z)` identifies the prime `(ι π,a,b)` |
| Pointed etale S-maps (X,x) <- (U,u) -> (M_n,o) | `U : Scheme.{u}`, `p`, `q`, `[Etale p]`, `[Etale q]`, `hover : p ≫ f = q ≫ DvrNodal.projection R' (ι π) n ≫ Spec.map ι`, `z : U`, `hz : p z = x`, and `ho` |
| Ordinary blowup of the reduced point | `(pointIdeal x hx).blowup`, `(pointIdeal x hx).blowupMap`; the ideal is the published vanishing ideal of the closed singleton, with reduced induced scheme structure |
| Composite g = f o b | `(pointIdeal x hx).blowupMap ≫ f`, always the actual composite |
| Assumed flat and locally of finite presentation g | `[Flat ((pointIdeal x hx).blowupMap ≫ f)]` and `[LocallyOfFinitePresentation ((pointIdeal x hx).blowupMap ≫ f)]` |

The witnesses `R'`, `n`, `U`, `p`, `q`, `z` are explicit parameters: this unpacks the node's
existential hypothesis without imposing a chosen residue-field isomorphism or restricting
which witnessing chart is allowed.

Conclusion-by-conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| b and g H-projective and proper | First four conjuncts: `IsHProjective b`, `IsProper b`, `IsHProjective (b ≫ f)`, `IsProper (b ≫ f)`, with b written as its actual term |
| g flat and finitely presented | `Flat (b ≫ f)` and `LocallyOfFinitePresentation (b ≫ f) ∧ QuasiCompact (b ≫ f) ∧ QuasiSeparated (b ≫ f)`; this is the recorded finite-presentation convention |
| B Noetherian | `IsNoetherian (pointIdeal x hx).blowup` |
| Every fibre over y nonempty and geometrically connected over kappa(y) | `∀ y : X, Nonempty (b.fiber y) ∧ GeometricallyConnected (b.fiberToSpecResidueField y)` |
| Every geometric fibre nonempty and connected | Quantification over every `Ω : Type u` with `[Field Ω] [IsAlgClosed Ω]` and `t : Spec (.of Ω) ⟶ X`, with `Nonempty` and `ConnectedSpace` for `pullback b t` |
| Away from x the fibre remains a single point after any residue-field extension | `∀ y, y ≠ x → ∀ K [Field K] [Algebra (X.residueField y) K], IsIso (pullback.snd (b.fiberToSpecResidueField y) (Spec.map ...))`; the projection being an isomorphism says the entire extended fibre is `Spec K`, including scheme structure |
| Over an algebraic closure of kappa(x), n=2 gives P^1 | For every `Ω [Field Ω] [Algebra (X.residueField x) Ω] [IsAlgClosure (X.residueField x) Ω]`, `n = 2` implies an isomorphism from the base-changed exceptional fibre to `ProjectiveLine (Spec (.of Ω))`, with the equation making it an isomorphism over Ω |
| n>2 gives two copies of P^1 meeting in one reduced point | Two closed immersions `i j` from that same projective line, both over Ω; rational sections `a b` of their projections; `IsPullback a b i j` says their scheme-theoretic intersection is `Spec Ω`; `i.ker ⊓ j.ker = ⊥` says their scheme-theoretic union is the full exceptional fibre; the ranges cover |
| b surjective | `Surjective (pointIdeal x hx).blowupMap` |
| Nonempty geometric fibres of f imply nonempty geometric fibres of g | For every algebraically closed Ω and `s : Spec (.of Ω) ⟶ Spec R`, `Nonempty (pullback f s : Scheme.{u}) → Nonempty (pullback (b ≫ f) s : Scheme.{u})` |
| No connectedness of f/g, split node, excellence, or characteristic restriction | None occurs among the hypotheses. Connectedness is asserted for the blowup fibres only |

The two-line configuration is a description of the whole scheme, not just its point set:
the kernel-ideal condition excludes nilpotent thickenings supported on its intersection.
Together with the closed immersions of reduced projective lines it also implies reducedness
of the whole fibre. The cartesian square with domain `Spec Ω` records reducedness and
rationality of the intersection itself.

Recorded statement-dependency declarations read and reused:

| Node | Module and declaration |
| --- | --- |
| def-sc-discrete-valuation-ring | `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`; uniformizer via maximal ideal span (equivalently `irreducible_iff_uniformizer`) |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map` |
| pqf-def-locnoeth | `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`, with `IsNoetherian` for the full hypothesis |
| def-kun-projective | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `AlgebraicGeometry.IsHProjective` |
| def-weil-etale-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` |
| def-weil-polynomial-ring | `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; the existing strict nodal model uses `MvPolynomial (Fin 2)` and the explicit quotient, not a new polynomial construction |
| def-nagata-global-blowup | `WeilConjectures.Blowup.Gluing`: `AlgebraicGeometry.Scheme.IdealSheafData.blowup`, `blowupMap` |
| def-weil-flat-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` |
| def-sbc-locally-finite-presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`; finite presentation is lfp + qc + qs |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper` |
| def-weil-geometric-fibre | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`, `pullback.snd`; fibre via `Mathlib.AlgebraicGeometry.Fiber` |
| def-pc-geometrically-irreducible | Recorded `Mathlib.AlgebraicGeometry.Geometrically.Integral` imported; its node's connectedness clause uses `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `AlgebraicGeometry.GeometricallyConnected` |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField` |
| def-sc-p1-standard | Recorded `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits` imported; the projective line in its `ProjectiveLine.TwistData` is the canonical `AlgebraicGeometry.ProjectiveLine` from `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`; `IsAlgClosure` from its imported Basic module quantifies over any choice of algebraic closure |
| def-sfb-arithmetic-nodal-model-origin | `Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus`: `AlgebraicGeometry.DvrNodal.model`, `projection`, `IsOrigin` (their full definitions read) |
| def-sfb-surface-point-blowup-data | `Sheaf.AlgebraicGeometry.SurfacePointBlowupData`: `AlgebraicGeometry.SurfacePointBlowup.pointIdeal` (full definition read) |

All stated proof-dependency modules are imported with plain `import`, except those already
needed publicly for the statement. These include ProjectiveAffineBaseBlowup,
ProjectiveImpliesProper, EtaleFibreDiscreteSeparablePoints, Blowup.FlatBaseChange,
BinomialBlowupChartAlgebras, GeometricallyConnectedCheckAfterExtension, Blowup.Complement,
and Mathlib's PullbackCarrier. Mathlib Noetherian/Proper/FinitePresentation and the field
closure import supply the other recorded proof dependencies. The proof plan does not use
the DvrNodal theorem as an extra axiom; only its actual model/origin definitions are reused.

Edge cases checked before drafting and on rereading:

- `n = 0,1` are excluded exactly by `2 ≤ n`; `n = 2` and `2 < n` cover all allowed exponents.
  At `n = 2`, the model's middle equation is `rs = 1`; for larger exponents its exceptional
  middle chart is `rs = 0`, giving the stated reduced one-point intersection.
- No perfectness, separability of kappa(x) over the trait residue field, or split-node
  assumption is imposed. The common etale chart can have larger residue field, and only
  the algebraic-closure configuration is asserted to split.
- Equal/mixed characteristic and characteristic two are allowed. No conic discriminant
  or division by two enters the statement.
- The empty scheme cannot satisfy the hypothesis supplying `x`; this is the node's own
  exclusion. No unrelated components of X or fibres of f/g are assumed connected.
- `y ≠ x` is required only for the single-point clause. The exceptional fibre is retained
  at x, and arbitrary field extensions (including the identity) are allowed elsewhere.
- One universe `u` accommodates the rings, schemes and test fields, following Mathlib's
  geometric connectedness convention; there is no independent smaller test universe.
- The chosen centre is `vanishingIdeal` of the actual closed singleton, not a thickening
  or a merely topological exceptional configuration.

Searches (2026-10-24):

- `msearch.py Q44 <item> leanfinder "Blowing up an arithmetic nodal closed point has projective geometrically connected fibres"`: eight hits for generic Proj properness and fibre declarations, no match to this theorem.
- `msearch.py ... loogle "AlgebraicGeometry.GeometricallyConnected, AlgebraicGeometry.IsHProjective"`: zero hits, IsHProjective unknown to the Mathlib-only service.
- `msearch.py ... grep "nodal.*blowup|blowup.*[Ff]ib" AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "The blowup of an arithmetic nodal closed point has geometrically connected fibres and is projective"`: eight generic fibre/properness hits, no such theorem.
- `rg -n` over `lean/Sheaf` and `lean/WeilConjectures` for nodal blowup, pointIdeal, exceptional fibres, and projective lines: found the existing DvrNodal calculus, SurfacePointBlowup data and BinomialBlowupChartAlgebras, reused here; no theorem with all these hypotheses and conclusions. `rg` for the item's id in `lean/WeilConjectures` and for the new full declaration name in both libraries and `dag/lean_names_upstream.json` found no prior declaration.
- DAG search found the two existing owners above, which are cited rather than duplicated.

No `STATEMENT-DISPUTED` issue or statement correction was found. The initial compile found
ambiguous coercions from scheme pullbacks to types; explicit `: Scheme.{u}` annotations
resolved them. A docstring/declaration blank-line style warning was removed. Only server
compilation through the prescribed `scompile.py` wrapper is used.

## Second reading by Q44

A separate reread of the final node copy and full module checked each row of the hypothesis
and conclusion tables above. The dispatcher forbids starting another agent; this is the
worker's own second pass, with the independent maintainer review still to follow. No claim
of an independent worker review is made.

The extension is local, injective and etale, preserves the same pi, and the two pointed maps
commute over Spec R. The point is closed and special. The blowup is the actual ordinary blowup
of the reduced point. The projectivity convention is the recorded H-projective class.
The conclusion contains the exact flatness/finite-presentation/Noetherian assertions and
separates fibres of b from fibres of f/g. All residue-field extensions, both exceptional
exponent cases, the scheme-theoretic cover and reduced intersection, surjectivity, and the
final nonemptiness implication are present. No extra connectedness or splitting hypothesis
was found. No mathematical change was needed in this reread.


## New nodes

`def-sfb-arithmetic-nodal-model-origin` owns the existing definitions
`AlgebraicGeometry.DvrNodal.constant`, `coordinate`, `originIdeal`, `model`, `projection`,
and `IsOrigin` in `Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus` with `existing: true`.
Its source is Stacks models.tex Tag 0CDC's coefficient map and origin ideal, with Tag 0CDE's
pointed chart comparison. For every commutative ring R and a in R, `constant` and `coordinate`
are the quotient classes of coefficients and variables in `strictNodalRing R a`;
`originIdeal` is the sum of their generated ideals. `model R π n` is the existing nodal
scheme with parameter π^n, `projection` is the coefficient-induced spectrum morphism,
and `IsOrigin` is equality of the point's prime ideal with the displayed generated ideal.
These bodies are actual quotient/spectrum constructions and use no theorem conclusion.
The node cites the existing strict nodal chart, polynomial ring and spectrum definition
nodes. The new node quantifies over all n >= 0 as do the definitions; at n=0 the origin
predicate may have no witness, and the node asserts no primality or existence. No DVR,
nonzero-element or characteristic condition is silently added to these general definitions.

The new node contains the fresh LeanSearch, LeanFinder, Mathlib grep, upstream/Sheaf grep
and DAG/blueprint-search records with results. Mathlib search hits were generic affine-space
or Weierstrass declarations. The six exact definitions already exist in the landed module,
but no definition node owns them. The new node therefore records the exact existing
interface instead of adding a duplicate module or attaching plain definitions to a theorem
statement dependency. Its blueprint ancestor and via list follow the item.

## Returned delivery repair

H2 (immutable head 3a8563c2b22f): removed
`lem-sfb-dvr-nodal-chart-blowup-calculus` from this item's added statement dependencies and
replaced it with `def-sfb-arithmetic-nodal-model-origin`, the new owner described above.
The new node's six-declaration binding includes all transitively used helper definitions
listed in the return. The theorem module and `lean.statement` are byte-identical to the
returned version. Current shared main still has no Lean record for this item; its unchanged
node fields were refreshed from main, preserving only the authorized `lean` and `stmt_deps`
delta. No dependency records or existing source modules were edited. The delivery wrapper
will construct the repair commit on current main.

The worker's second pass for this repair compared all six source definitions with the new
node and verified that no theorem conclusion is used to define them. It checked the new
node's general-ring and n=0 cases and the item's unchanged correspondence tables. The
original independent maintainer review explicitly accepted every hypothesis, conclusion,
edge case, and source match, returning only the ownership issue repaired here. As instructed,
no other agent was started. Compile and delivery preflight are rerun for this repaired set.
