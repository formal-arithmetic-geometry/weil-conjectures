## Worker report

The delivery states `AlgebraicGeometry.Temkin.valuation_semistable_stable_contraction` in
`Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction`. Its single postponed proof
is `sorry`. It also supplies the missing multipointed-curve interface in
`Sheaf.AlgebraicGeometry.MultipointedCurveModification`, owned by the new definition node
`def-trf-multipointed-curve-modification`. Every definition has concrete data; the canonical
base-change maps are `pullback.map`, using the compatibility equations of the given pair.
No dependency node was repaired, and the item's natural-language statement is unchanged.

Source read: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, §1.2 (printed p. 2),
§4 preamble and Remark 4.1 (pp. 24--25), Lemmas 4.4.4--4.4.5 and Proposition 4.4.6
(pp. 31--33). The argument really starts from the given semistable modification and
successively blows it down; the conclusion retains that factorization. The source's
reducedness convention follows here from flatness over the valuation domain and the
smooth/étale generic fibres, so it imposes no additional hypothesis.

Hypothesis and clause correspondence:

- Field and separable closedness: `(K : Type u) [Field K] [IsSepClosed K]`.
- Embedded valuation ring, with fraction field K: `(V : ValuationSubring K)`.
  Its defining field `mem_or_inv_mem'` is precisely the valuation alternative;
  its existing `IsFractionRing V K` instance shows the fraction-field clause.
  `V.toSubring.subtype` is the actual inclusion, not an independently chosen map.
- Finite chain of prime ideals: `[Finite (PrimeSpectrum V)]`. Primes in a valuation
  ring are already linearly ordered, so this says exactly that the chain is finite.
  No discrete, Noetherian, rank-one, or nonfield hypothesis was added.
- T and eta: every pair is over `Spec (.of V)`, and every generic base change uses
  `Spec.map (CommRingCat.ofHom V.toSubring.subtype)` from `Spec K`.
- Multipointed pairs `(X,D)` and `(Y,E)`: `X Y : MultipointedCurve (Spec (.of V))`.
  The bundle has schemes `curve` and `marking`, structure maps `toBase` and
  `markingToBase`, and `inclusion` with `inclusion_over`. Its fields `curve_flat`
  and `marking_flat` give flatness. The `*_lfp`, `*_qc`, `*_qs` fields together
  give finite presentation, including quasi-separatedness. The `*_dimension`
  fields use the already recorded `Scheme.IsPureDimension` on each ordinary
  fibre. The field `closed` says the marking inclusion is a closed immersion.
- Smooth generic X: `hX : Smooth (pullback.snd X.toBase eta)`.
- Étale generic D: `hD : Etale (pullback.snd X.markingToBase eta)`.
- Given compatible pair: `f : Y.Hom X`. The `curve_over`, `marking_over`, and
  `comm` equations express compatibility over T and with the closed markings.
- Given eta-modification: `hf : f.IsEtaModification eta`. This includes properness
  of BOTH maps; for each map an open U, injectivity on sections over every open
  for both U and its inverse image, and `IsIso (pullback.snd f U.ι)`; and `IsIso`
  for both canonical generic base-change maps. This realizes isomorphisms between
  schematically dense opens on both sides, with no topological-density substitute.
- Semistability of the given source: `hY : Y.IsSemistable`. For every base point t
  and every point of the chosen algebraic-closure fibre, either membership in
  Mathlib's `smoothLocus` or the existing `Orgogozo.IsOrdinaryDoublePoint` holds.
  That predicate explicitly identifies the maximal-ideal completion with
  `MvPowerSeries (Fin 2) Ω / (X₀ * X₁)`, respecting the scalar map Ω. The other
  conjuncts give étaleness of the marking and membership in the relative smooth
  locus at every marked point. Geometric fibres use `Orgogozo.geometricPoint`,
  the recorded residue-field algebraic-closure composite, and `pullback`.
- Stable intermediate pair and its map: `∃ Z g q` with `g : Z.Hom X` and
  `q : Y.Hom Z`. The conjunct `g.IsStable eta` includes `g.IsEtaModification eta`
  and `Z.IsSemistable`. Its final universal condition excludes exactly closed
  projective-line embeddings over Ω with irreducible-component image, at most two
  special points, and singleton image under the geometric fibre map.
- The existing projective line is `ProjectiveLine (Spec (.of Ω))`; the embedding
  must commute with structure maps to `Spec Ω`. Its image is required to belong
  to `irreducibleComponents` of the geometric fibre, so no arbitrary rational
  subcurve or normalization is substituted for the component itself.
- `specialPoints` is the union of the base-changed marking and the complement of
  the fibre's smooth locus. `encard ≤ 2` counts points and correctly rejects
  infinite sets. The negation of `Subsingleton` of the fibre-map image says that
  such a component is not contracted. The projective line is nonempty, so a
  subsingleton image is exactly a singleton. Contraction is tested in the
  geometric target fibre, not after forgetting its scalar field.
- The factor is an eta-modification: `q.IsEtaModification eta` independently
  requires all curve and marking clauses just listed.
- Factorization of the original pair: `q.curve ≫ g.curve = f.curve` AND
  `q.marking ≫ g.marking = f.marking`. Thus the original morphism, including its
  marking map, is retained.

Dependency declarations read and reused (module, declaration):

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (also read the dependency's
  `IsSepClosure` signature; the node uses its field clause, not an extension).
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.RingTheory.Valuation.ValuationSubring`: `ValuationSubring`, its subtype
  inclusion, and its `IsFractionRing` instance.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.Scheme.Hom.smoothLocus`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.map`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `AdicCompletion.of`, as used in the existing ordinary-double-point predicate.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `C`, `X`, used by
  that same recorded predicate; no duplicate node-ring construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.Paper.OrgogozoInductionData`: `Orgogozo.IsOrdinaryDoublePoint`,
  `Orgogozo.geometricPoint` (and the `nodeRing`, `localScalar` definitions they use).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveLine`, the
  two-homogeneous-coordinate specialization of the recorded `ProjectiveSpace`.
- Proof imports include `Mathlib.RingTheory.RingHom.Flat` for the recorded
  `RingHom.Flat`/`Module.Flat` and `Mathlib.AlgebraicGeometry.Morphisms.Proper`
  for proper-composition permanence. The two exceptional-component proof nodes
  have no recorded Lean declaration, so there is no proof module to import yet.

Edge cases checked at the statement level: V a field (height zero, the generic map
is an isomorphism); an empty marking; empty curves and their vacuous dimension and
component conditions; disconnected curves; nonproper and nonseparated pairs; arbitrary
finite valuation height; positive characteristic and imperfect separably closed K;
contracted tails and bridges with respectively one or two special points; noncontracted
rational components, which do not obstruct stability; components with three special
points, which do not obstruct stability. A self-nodal rational component is not silently
replaced by its projective-line normalization. All universes and variables are explicit,
with `set_option autoImplicit false`. The geometric fields use algebraic closures in the
scheme universe and do not impose any new equality of site universes.

Searches (the exact machine records are in the new node's `mathlib_searches`):

- msearch leanfinder: “Every given semistable marked curve modification over a finite
  height valuation ring factors through a stable modification”. Eight results are
  valuative criteria and minimal Weierstrass models, not this theorem.
- msearch leansearch: “multipointed curve semistable eta modification stable exceptional
  projective line component”. Eight results concern nonsingular Weierstrass points;
  none supplies this curve-pair interface or theorem.
- msearch loogle: `"semistable"`: zero hits.
- msearch grep: `Multipointed|Semistable|StableModification|EtaModification|semistable`:
  zero Mathlib hits.
- msearch grep in AlgebraicGeometry:
  `IsOrdinaryDoublePoint|MultipointedCurve|IsSemistable|IsStable.*Modification|smoothLocus`:
  smooth-locus results only; that Mathlib API is used directly.
- Direct rg over the prescribed upstream `WeilConjectures/` and project `lean/Sheaf/`:
  no multipointed-curve or stable-modification interface. The Orgogozo file supplies
  the reused nodal predicate and geometric point. Its `IsSemistableGeometricCurve`
  additionally requires connectedness, so it would wrongly restrict these fibres.
- Direct grep for the item id in upstream: no hits. Upstream name-index and
  projective-space searches locate the existing projective line used here.
- DAG grep: several statement nodes contain inline multipointed-curve definitions,
  but none is a definition node giving this notion. `blueprint_refs.py search
  multipointed` and `search 'stable modification'`: no blueprint definition matches.

No statement dispute or correction is needed. A dependency-closure read confirmed no
path from the reused Orgogozo definition node back to this item, so the new definition
node does not introduce a cycle.

## New nodes

`def-trf-multipointed-curve-modification` collects the multipointed-curve notion and its
morphisms, canonical base-change maps, semistability, eta-modification and stability,
exactly as introduced together in Temkin §1.2 and used in §4. It is self-contained and
cites the existing definitions for all its component notions. The searches above found
no existing definition of this interface. All nine declarations, with source and blueprint
docstrings, are listed in its `lean.declarations`; there are no postponed theorems in the
new module. Its finite-presentation and density clauses include the nonseparated and
non-quasi-compact-open cases rather than adding convenient restrictions.

## Second reading by Q102

I reread the node and the two delivered files as a separate check after drafting. This is
a worker self-review; the maintainer performs the independent delivery review specified
by the dispatch brief, and no other agent was started.

The clause-by-clause reading above checks every binder, both morphism components and
every stability and density condition. It caught two draft interface issues: a temporary
smooth-point predicate duplicated Mathlib's smooth-locus API, and using the quasi-coherent
zero-kernel predicate would not directly express the requested sectionwise density for
arbitrary opens. Both were replaced by the exact existing smooth locus and by explicit
sectionwise injectivity. I also checked that the geometric contraction map is the
canonical base change into the target geometric fibre, not its composite into the total
space. The closed projective-line test respects the Ω-structure map and the reduced
component structure. Neither X nor Y is forced proper, separated or connected over T.
The new node and its declarations were reread against the same source definitions.

Validation: `scompile.py Q102 lem-trf-valuation-semistable-stable-contraction` compiled
both delivered modules separately in dependency order, with no errors or warnings.
`deliver2.py Q102 lem-trf-valuation-semistable-stable-contraction --no-push` then printed
`OK (dry run)` after server preflight and compilation of both files (temporary checked
commit `8916cc8376`). The main theorem's recorded signature is verbatim; only `lean` and
the new definition dependency were added to the original item. All Lean lines are within
100 characters.

## Maintainer review fix (NT-cc reviewer, 2026-10-18)

The delivery's base already contains the landed definition node `def-trf-multipointed-curve`
(`AlgebraicGeometry.MultipointedCurve`, `Sheaf.TraceFormula.MultipointedCurve`, N5), with the
same clauses as the delivered `AlgebraicGeometry.Temkin.MultipointedCurve`. To keep one
definition per notion (H4), the structure is dropped from
`Sheaf.AlgebraicGeometry.MultipointedCurveModification`: its morphisms, base changes,
semistability, eta-modification, special points and stability are now declared in namespace
`AlgebraicGeometry.MultipointedCurve` on the landed structure (fields `X, D, x, d, i`), with
`lfp_X` made an instance for the smooth locus. The new node cites
`def-trf-multipointed-curve` instead of restating the curve clauses, and the item's signature
reads `X.x`, `X.d` for `X.toBase`, `X.markingToBase`. The mathematics is otherwise unchanged;
both modules compile with no error or warning beyond `sorry`.
