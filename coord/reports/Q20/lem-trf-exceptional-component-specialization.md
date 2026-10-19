## Worker report

The module `Sheaf.TraceFormula.ExceptionalComponentSpecialization` states
`AlgebraicGeometry.Temkin.exceptional_component_specialization`, with a single `sorry`.
There are no new definitions and no dependency repairs. The item's mathematical statement
is unchanged. Its `stmt_deps` gains the two already landed nodes
`def-trf-multipointed-curve` and `def-trf-multipointed-curve-modification`, whose shared
interfaces replace the repeated prose definitions in this item. Every other node field,
except `lean`, is unchanged.

Source checked: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
§1.2 and Lemmas 4.4.2 and 4.4.4, especially the specialization claim after replacing
the target by its normalization. Read the primary source at
https://arxiv.org/html/0707.3953v3#S4.SS4 . The local archival PDF named by the node
is absent (WANTED); the online primary text supplies the source. The node asks only
for an exceptional component in the prescribed nonempty closure fibre. The theorem
states exactly this existence assertion, without requiring the image point to be
closed in the original target.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Separably closed field K | `(K : Type u) [Field K] [IsSepClosed K]` |
| Valuation ring V inside K with fraction field K | `(V : ValuationSubring K)`. Its `mem_or_inv_mem'` field is the stated valuation criterion; every element of K is a quotient from V by that criterion, so K is its fraction field. |
| Prime ideals form a finite chain | `[Finite (PrimeSpectrum V)]`. Primes of a valuation ring are already totally ordered, so this says exactly that the chain is finite. |
| T = Spec V and eta = Spec K | Every base is `Spec (.of V)`; the generic morphism is `Spec.map (CommRingCat.ofHom V.toSubring.subtype)`. |
| Multipointed target and source | `(X Y : MultipointedCurve (Spec (.of V)))`. The structure includes flatness, local finite presentation, quasi-compactness and quasi-separatedness for both structure maps, pure fibre dimensions 1 and 0, and the marking closed immersion. It permits empty markings and does not require a separated or proper structure map. |
| Smooth generic X and etale generic D | `hX : Smooth (pullback.snd X.x ...)` and `hD : Etale (pullback.snd X.d ...)`, for the generic morphism above. |
| Every local ring of X is an integrally closed domain | `hnormal : ∀ x : X.X, IsDomain (X.X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.X.presheaf.stalk x)`. |
| Compatible pair f | `(f : Y.Hom X)`: `curve`, `marking`, their base equations and the marking square. |
| eta-modification | `hf : f.IsEtaModification ...`: properness on both maps, isomorphisms over schematically dense opens on source and target, and isomorphisms on both generic fibres. |
| Semistable source | `hY : Y.IsSemistable`: smooth or nodal geometric-fibre points, etale marking, and marking in the relative smooth locus. The imported ordinary-double-point definition uses the maximal-ideal completion and the two-variable formal-power-series nodal quotient, with scalar compatibility. |
| Point s and irreducible component C of Y_s | `(s : Spec (.of V)) (C : Scheme.{u}) (i : C ⟶ Y.x.fiber s)`, `[IsReduced C]`, `[IsClosedImmersion i]`, and `hC : Set.range i ∈ irreducibleComponents (Y.x.fiber s)`. |
| Its generic point z | `(z : Y.x.fiber s)` with `hz : IsGenericPoint z (Set.range i)`; its image in Y is `Y.x.fiberι s z`. |
| Reduced closure W of that point in Y | `(W : Scheme.{u}) (w : W ⟶ Y.X)`, `[IsReduced W]`, `[IsClosedImmersion w]`, and `hW : Set.range w = closure ({Y.x.fiberι s z} : Set Y.X)`. The reduced-induced-closed-subscheme uniqueness theorem identifies precisely this representation with the specified canonical closed subscheme. |
| f contracts C to a point | `hcontract : (Set.range (i ≫ Y.x.fiberι s ≫ f.curve)).Subsingleton`. The component is nonempty, so its image is a singleton, not an empty set. |
| C over the algebraic closure is P1 | `hline` gives an isomorphism from `ProjectiveLine (Spec (.of (AlgebraicClosure ...)))` to the actual pullback of `i ≫ Y.x.fiberToSpecResidueField s` along the residue-field algebra map. The equation on `e.hom ≫ pullback.snd` makes it an isomorphism over that algebraically closed field. |
| At most two geometric marking or singular points on C | `hpoints` takes the inverse image of `Set.range (i ≫ Y.x.fiberι s)` under the geometric-fibre projection to Y, intersects it with `Y.specialPoints s`, and bounds its `encard` by 2. |
| Every specialization t of s | `(t : Spec (.of V)) (ht : t ∈ closure ({s} : Set (Spec (.of V))))`. Equality t = s is included. |
| The prescribed W_t is nonempty | `hne : Nonempty ((w ≫ Y.x).fiber t)`, the scheme-theoretic fibre of W's structure map. |
| An irreducible component C_t of Y_t with reduced induced structure exists | The existential binds `Cₜ`, `iₜ : Cₜ ⟶ Y.x.fiber t`; its first three clauses are `IsReduced Cₜ`, `IsClosedImmersion iₜ`, and `Set.range iₜ ∈ irreducibleComponents (Y.x.fiber t)`. |
| It is contained in W_t | `Set.range iₜ ⊆ (Y.x.fiberι t) ⁻¹' Set.range w`. This is precisely the support of W_t inside Y_t; reducedness of both closed subschemes also gives the equivalent closed-subscheme containment. |
| It is contracted | `(Set.range (iₜ ≫ Y.x.fiberι t ≫ f.curve)).Subsingleton`. |
| Its algebraic-closure base change is P1 | The existential isomorphism `e` and its scalar compatibility equation repeat the `hline` construction at t, with `iₜ`. |
| It has at most two geometric special points | The last clause repeats `hpoints` at t with `iₜ`. |

The support formula for geometric components requires no arbitrary map: the ordinary
fibre embeds into Y, so the inverse image of a reduced component's support under the
geometric-fibre projection is exactly the support of its base change. The geometric
scheme itself is still the actual pullback in `hline` and in the conclusion. In particular,
no normalization or parametrization is substituted for a component.

Dependency declarations read and used:

- `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.Hom`, `Hom.IsEtaModification`, `MultipointedCurve.IsSemistable`,
  `MultipointedCurve.specialPoints`; the marking base-change map and
  `Orgogozo.geometricPoint` underlying these are the canonical pullback constructions.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`, including
  its uniqueness clause, justifies the representation by reduced closed immersions.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (and read the recorded `IsSepClosure`).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
  These are also used through the shared pair and modification definitions.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, through
  `AlgebraicGeometry.Scheme.IsPureDimension` in the shared curve definition.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` as required by the recorded inline normal-domain form.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` and
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, through the shared nodal
  predicate in `Sheaf.Paper.OrgogozoInductionData`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`, `snd`.
- `Field` is the existing Mathlib class, not a project copy.

Every currently recorded proof-dependency module is imported without `public`.
`lem-trf-nodal-generic-component-closure` has no recorded module yet and is therefore
only described in the proof docstring. `lem-weil-pbc-finite-type-over-noetherian` is a
Mathlib leaf supplied by `Mathlib.AlgebraicGeometry.Noetherian`. The second global-sections
module supplies the companion declaration recorded by `lem-pc-h0-proper-variety`.
No downstream theorem is imported to obtain a helper: in particular the existing
`geometricComponentInclusion` in `ValuationExceptionalClosedImageCriterion` is not needed,
avoiding a dependency cycle with its proof's use of this item.

Edge cases checked before writing:

- `t = s` satisfies the specialization condition; the given component witnesses the
  conclusion. No strict-specialization hypothesis was introduced.
- Empty markings are accepted by `MultipointedCurve`; `specialPoints` then only counts
  singular points. Zero, one and two special points are all allowed by `encard ≤ 2`.
- An empty W_t is deliberately excluded only by the stated `hne`. No chosen point of
  W_t or properness of Y over T is added.
- The empty curve cannot carry the initial irreducible component, as in the node.
- A valuation ring which is a field is allowed; there is no positive-height restriction.
- Residue characteristic is unrestricted; algebraic closures, not separable closures,
  appear in the projective-line condition. Scalar compatibility is explicit.
- No closedness of the contraction point in all of X is assumed; neither structure map
  is required to be proper or separated over T.
- The reduced scheme, closed immersion and support equation determine each component
  and W up to its unique ambient isomorphism. These are presentations of the specified
  objects, not additional mathematical hypotheses.

Searches for an existing statement (2026-10-19):

- `msearch.py ... leanfinder "An exceptional rational component with at most two marked
  or singular points has an exceptional component in a nonempty specialized closure
  fibre"`: eight hits, led by specializing-map and valuative-criterion lemmas and
  `genericPoints.component`; none give rationality or the geometric special-point bound.
- `msearch.py ... leanfinder "exceptional rational component specializes in a semistable
  marked curve"`: eight Weierstrass minimal-model/good-reduction hits; none state this claim.
- `msearch.py ... leansearch "specialization of exceptional components in semistable
  marked curves"`: eight specialization/topological and stalk-map hits; none match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.fiber, irreducibleComponents"`:
  zero hits.
- `msearch.py ... grep "Semistable|Multipointed|ExceptionalComponent" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` in `lean/Sheaf` and upstream `WeilConjectures` for
  `Multipointed|MultiPointed|Semistable|EtaModification|ExceptionalComponent|semistable|multipointed`
  found the landed pair definitions and related stable-modification statements.
  `rg` for `exceptional.*specializ|exceptional_component_specialization` found only the
  downstream criterion's proof reference and unrelated material, not a matching theorem.
- The item-id search in upstream `WeilConjectures` found no declaration. Searches in the
  DAG found the already landed multipointed-curve and modification definition nodes;
  their exact source signatures and docstrings were read, and these two ids were added
  to `stmt_deps`. No new notion/node is required.
- Exact declaration-name search in the upstream name index and both source trees found
  no existing `AlgebraicGeometry.Temkin.exceptional_component_specialization`.

No statement dispute or source-based correction is required.

Validation: `scompile.py Q20 lem-trf-exceptional-component-specialization` compiled the
sandbox and library forms separately in 4.3 and 6.4 seconds, with no diagnostic messages.
The complete theorem signature is copied verbatim into `lean.statement`; all universes
and variables are explicitly bound (`set_option autoImplicit false`).

## Second reading by Q20

Author's separate second pass, reopening the node and final file; the dispatched worker
has no second agent, and the maintainer supplies the independent review.

I rechecked each hypothesis and conclusion against the table above. The pair definition
has the required finite presentation (including quasi-compactness and quasi-separatedness),
not just local finite presentation. Normality uses both the domain and integrally closed
conditions at every stalk. The geometric projective-line isomorphisms commute with the
scalar projections, and the special-point bound counts points of the geometric ambient
fibre. The inverse-image support formula was checked against the base-change square,
so the bound is on the component itself, not on its normalization. The chosen t is
allowed to equal s and is required only to lie in the singleton closure. The nonemptiness
hypothesis is on the actual scheme fibre of W, and the conclusion's support inclusion is
in that same W_t. Contraction is a singleton because a component is nonempty. All three
exceptionality properties occur in both the hypothesis and the conclusion. The source
normalization assumption and the absence of a closed-image assumption agree with the node.
No mismatch was found and no mathematical statement changed in this pass.
