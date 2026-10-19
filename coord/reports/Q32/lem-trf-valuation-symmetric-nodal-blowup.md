## Worker report

The module `Sheaf.TraceFormula.ValuationSymmetricNodalBlowup` states
`AlgebraicGeometry.exists_valuation_symmetric_nodal_blowup`, with one `sorry` and no other
postponed theorem. Every auxiliary definition has real data. The structure
`SymmetricNodalLocalChart` and predicate `SymmetricNodalChartRings` package the specific
local data asserted by this node; they do not introduce an independent notion or replace
any recorded dependency.

Hypotheses and conclusions, in the order of the node:

| Node clause | Lean rendering |
| --- | --- |
| Separably closed field K | `(K : Type u) [Field K] [IsSepClosed K]` |
| Valuation subring V of K with fraction field K | `(V : ValuationSubring K)`; the inclusion is `V.subtype`, and this standard bundled notion includes the either-z-or-inverse condition and has fraction field K |
| Finite chain of primes | `[Finite (PrimeSpectrum V)]`; valuation-ring prime ideals are already totally ordered, so finiteness is precisely the additional hypothesis |
| S and eta | `Spec (.of V)`, `Spec (.of K)`, and `Spec.map (CommRingCat.ofHom V.subtype)` |
| S-curve is flat and finitely presented | `[Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]` |
| Pure one-dimensional fibres | `hpure : ∀ s, (f.fiber s).IsPureDimension 1` |
| Geometric fibres have only ordinary double points as singularities | `hnodal` tests every algebraically closed Ω and every geometric point g, and says each point has a smooth open neighbourhood or satisfies `Orgogozo.IsOrdinaryDoublePoint (pullback.snd f g) x`; this existing predicate uses the maximal-ideal completion and an isomorphism to Ω[[u,v]]/(uv) commuting with Ω scalars |
| Smooth generic fibre | `hgeneric : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom V.subtype)))` |
| J and N | `Scheme.firstFittingIdealSheaf f` and `Scheme.firstFittingSingularSubscheme f` |
| Finite underlying set of N | `hfinite : (Set.range (Scheme.firstFittingSingularSubscheme f)).Finite` |
| Arbitrary chosen z in N | `(z : X) (hz : z ∈ Set.range ...)` |
| s0 and whole closure C | `f z` and `closure ({z} : Set X)` |
| C is contained in N | The first conjunct of the conclusion is exactly that subset statement |
| Nonzero pi, open W containing all C, finite affine cover | Existentials π, W, n, `U : Fin n → X.Opens`; `π ≠ 0`, `closure {z} ⊆ W`, `⨆ i, U i = W`; each `SymmetricNodalLocalChart` has `affine : IsAffineOpen (U i)` |
| V(pi) is closure of s0 | `PrimeSpectrum.zeroLocus ({π} : Set V) = closure ({f z} : Set (Spec (.of V)))` |
| Singular locus intersection in W over V(pi) is C | The next intersection equality includes all three factors, including W and the inverse image by f |
| Each base is an affine open of S and a localization of V | In each local chart: `R`, `scalar`, `denominators`, `localization : @IsLocalization ... scalar.toAlgebra`, `baseOpen`, `baseAffine`, `baseIso`, and `baseMap` |
| Walpha maps into that affine base open | `toBase`, `overBase`, and `baseMap` |
| Nonzero smoothing parameter aalpha | `a` and `a_ne_zero` |
| Etale cover Talpha of Walpha | `T`, `cover`, `cover_etale`, `cover_surjective` |
| Etale morphism to Spec R[u,v]/(uv-a), over R | `modelMap`, `model_etale`, `model_over`, using the existing `StrictSemistableModel.nodal` and its canonical `baseMap` |
| Pullback of J equals (u,v) | `fitting` is equality of ideal sheaves after `comap`; `symmetricNodalAffineIdeal` transfers the actual ideal via the canonical `ΓSpecIso`, and `symmetricNodalSingularIdeal` is the span of the two quotient coordinates |
| b = a/pi squared belongs to R | `b : R` and `division : a = scalar π ^ 2 * b`; since V is a domain, π is nonzero, the localization is nonzero (a is nonzero), this equation is exactly the stated fraction-field division condition |
| Gluing J restricted to W plus (pi) with the unit ideal outside C | `I.comap W.ι = (J ⊔ (piIdeal.comap f)).comap W.ι` and `I.comap (symmetricNodalComplement X z).ι = ⊤`; these two restriction equalities include equality on the overlap and identify the glued ideal |
| Finite-type quasi-coherent ideal | `I : X.IdealSheafData` with `∀ A : X.affineOpens, (I.ideal A).FG` |
| q is the blowup, and proper | Canonical `I.blowup`, `I.blowupMap`, and `IsProper I.blowupMap` |
| Isomorphism outside C | `IsIso (pullback.snd I.blowupMap (symmetricNodalComplement X z).ι)` |
| Isomorphism on the entire generic fibre | `IsIso (pullback.snd I.blowupMap (pullback.fst f eta))`; its target is the entire original generic fibre |
| Reduced semistable S-curve | `IsReduced I.blowup`, flatness, local finite presentation, quasi-compactness, quasi-separatedness, pure dimension of all scheme fibres, and the same geometric nodal condition as in the hypothesis |
| Local cover by actual A[I/g] subalgebras | For every affine A and every finite generating family g for `I.ideal A`, open immersions c from `Spec (.of (AffineBlowup.chartRing ... (g j)))` to `I.blowup`, with canonical maps to A and union of images equal to the inverse image of A |
| Pullback to Talpha is etale pullback of the model blowup | `comparison` is a nonempty isomorphism in `Over T` between the two actual pullback projections; `model_etale` is retained |
| Three standard chart rings | `charts : SymmetricNodalChartRings R a (scalar π) b`: isomorphisms from `strictNodalRing R π`, `strictNodalRing R b`, `strictNodalRing R π` to the actual u, pi, v chart subalgebras of `(u,v,pi)` |
| Chart morphisms v=pi b p, u=pi r, v=pi t, u=pi b h | The last six equalities of `SymmetricNodalChartRings`; its scalar equalities make every isomorphism R-linear. Coordinates in the right-hand model are ordered `(v,h)` |
| Each reduced irreducible fibre component smooth at every point above C | Quantify every base point s, closed subset Z which is an irreducible component, and every point x of its canonical reduced induced closed subscheme `vanishingIdeal Z`. If its composite image lies in `closure {z}`, require a smooth open neighbourhood for the component's structure map to Spec κ(s) |
| Every closed subscheme E disjoint from C is preserved | For arbitrary E and arbitrary `[IsClosedImmersion i]`, disjointness implies `IsIso (pullback.snd I.blowupMap i)`; this is the canonical isomorphism of its full scheme-theoretic inverse image with E |

The local fields and map equalities use the same I, π and f as the global conclusion.
No separatedness, properness, connectedness, geometric nonemptiness, Noetherianity,
discreteness, or characteristic restriction is assumed for the input curve.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (and the recorded companion `IsSepClosure` read).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, through `Scheme.IsPureDimension`.
- `WeilConjectures.Blowup.Affine.Defs`: `AffineBlowup` and `AffineBlowup.toSpec`.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`: `AffineBlowup.chartRing`; the current published source was read using `scompile.py --source`, since it is absent from the older local source checkout.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`: `Scheme.firstFittingIdealSheaf` and `Scheme.firstFittingSingularSubscheme`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its projections.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.RingTheory.AdicCompletion.Algebra`/`Basic`: `AdicCompletion` and `AdicCompletion.of`, through the existing scalar-compatible ordinary-double-point predicate.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, through that same predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.

Already recorded nodes added to stmt_deps: `def-weil-pure-dimension` for
`Sheaf.AlgebraicGeometry.PureDimension` / `Scheme.IsPureDimension`;
`def-trf-orgogozo-induction-data` for `Sheaf.Paper.OrgogozoInductionData` /
`Orgogozo.IsOrdinaryDoublePoint`; `def-trf-strict-semistable-curve` for
`Sheaf.TraceFormula.StrictSemistableCurve` / `strictNodalRing`,
`StrictSemistableModel.scheme`, `StrictSemistableModel.baseMap`;
`def-nagata-global-blowup` for `WeilConjectures.Blowup.Gluing` /
`Scheme.IdealSheafData.blowup` and its canonical `blowupMap`;
`def-pc-reduced-scheme` for `Mathlib.AlgebraicGeometry.Properties` / `IsReduced`.
These declarations were read, not duplicated. No new node or dependency repair was needed.

All recorded, available proof-dependency modules are imported without `public`; Mathlib
matches for openness, the affine etale criterion, formally etale differentials, and qcqs
permanence are also imported. Currently unrecorded proof prerequisites (flat blowup
comparison map/theorem, nodal source locality, sepclosed valuation geometric components,
and etale source smoothness) are not imported and are not needed to type this statement.
The complete fifteen-step node proof, including its named inputs, is in the docstring.

Edge cases checked: the trivial valuation V=K and the smooth/empty curve have no possible
chosen z, so the implication has no instance in those cases; no artificial nonemptiness
assumption was added. The definition of pure dimension allows empty fibres. Disconnected
curves are retained (the connected/nonempty `HasNodalGeometricFibres` predicate was
explicitly rejected). Finite positive height need not be discrete or Noetherian. The
localization R cannot be zero because it contains a nonzero a. Characteristic two and
positive characteristic are retained. The centre is the full closure of z, so the
component condition is tested over every s, not just a closed fibre or over z alone.
A global self-node is allowed; smoothness is required of each reduced component locally
above C, not of the entire nodal fibre. The empty generating family is permitted when the
ideal is zero; its chart cover has empty image, consistent with that blowup. E may be
empty or nonreduced: its full pullback projection is required to be an isomorphism.

Searches (all through the prescribed wrapper unless described as rg):

- LeanFinder: `Blowup of a semistable curve over a valuation ring along the singular ideal plus a parameter, with three hyperbola charts and smooth components above the centre`. Eight hits, all Weierstrass minimality/good reduction; no match.
- Loogle: `AlgebraicGeometry.AffineBlowup.chartRing, AlgebraicGeometry.IsProper`. No hits; external Loogle does not index the upstream chartRing name.
- LeanSearch: `The symmetric blowup of a nodal curve along the ideal (u,v,pi) has charts up=pi, rt=a/pi^2, vh=pi`. Eight hits about manifold charts or Weierstrass variable changes; no match.
- Mathlib grep: `nodal|semistable|blowup` in AlgebraicGeometry. No hits in the wrapper's result.
- rg in the upstream `WeilConjectures` and side `lean/Sheaf`: `semistable|Nodal|Blowup|firstFittingSingularSubscheme`, then `symmetric_nodal_blowup|valuation_symmetric|Symmetric blowup|nodal blowup`. Found the reused interfaces, no theorem matching this node.
- `grep -rn 'lem-trf-valuation-symmetric-nodal-blowup'` in upstream: no hit.
- Collision search for `symmetricNodal|SymmetricNodal|exists_valuation_symmetric_nodal_blowup` in Mathlib, upstream, side Lean, and `dag/lean_names_upstream.json`: no hit.

Source reading: local `literature/stacks-project/curves.tex`,
`lemma-etale-local-structure-nodal-family` (0CBY), including the etale neighbourhood
statement and its formal-local discussion. The Temkin archival PDF is absent locally;
read https://arxiv.org/pdf/0707.3953v3 online at §1.2, §4.3 (pp. 27--28), and Remark 4.5.2
(p. 33). The latter supplies the strictification motivation; the symmetric operation and
its component argument remain explicitly the DAG's reconstruction, not a verbatim
assertion of Temkin. The current blueprint unit `_section.md` was also read. No statement
correction was made; no definite mathematical counterexample was found.

Validation: the module compiled with `scompile.py`, first without and then with the
available proof imports, with no errors or warnings. The initial elaboration issue was a
pullback point binder choosing the category of types; it was fixed by explicitly writing
`↥(pullback (C := Scheme) ... ...)`. The final recorded signature has that explicit choice.

## Second reading by Q32

This is the author's separate second pass; the maintainer supplies the independent
review, as the dispatcher brief requires. I reopened the node and the final Lean file.
I checked every row above against the actual binders, conjunctions, helper definitions,
and structure fields. I specifically checked the following potential mismatches:

- The nodal condition must respect Ω scalars; the existing
  `Orgogozo.IsOrdinaryDoublePoint` does, unlike a bare ring-isomorphism-only interface.
- Pure dimension is tested on every scheme fibre and is not replaced by total Krull
  dimension one of a connected geometric fibre. The geometric nodal condition has no
  connectedness or nonemptiness requirement.
- `comparison` is over the same T, with the actual blowup projections, not an unrelated
  isomorphism of underlying schemes. Both cover and model map remain etale.
- The three isomorphisms target the actual `AffineBlowup.chartRing` subalgebras. Constants
  and both original coordinates are specified, so the stated maps to the original model
  are retained, including the right chart order `(v,h)`.
- The glued I is the ideal used for the comparison, chart cover, reducedness, generic
  isomorphism, component conclusion, and arbitrary closed-subscheme preservation.
- The component conclusion is local smoothness on the reduced induced component at every
  point mapping into C; it does not mistakenly require the whole fibre to be smooth or
  replace the reduced scheme structure with the underlying closed subset.

No mathematical clause was dropped or silently corrected in this pass. I added the
already recorded dependency nodes for the canonical notions used and retained the
available proof imports. All auxiliary declarations are listed in lean.declarations;
there are no private definitions, local notation, local instances, axioms, or additional
postponed proofs.
