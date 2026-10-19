## Worker report

The delivery states `AlgebraicGeometry.normal_surface_exceptional_curves` in
`Sheaf.AlgebraicGeometry.NormalSurfaceExceptionalCurves`, with `sorry` as its only
postponed proof. The module also gives the real-data definition
`AlgebraicGeometry.Scheme.Hom.exceptionalCurves`, which is the set B(h) explicitly
introduced by this item. No statement correction, dependency replacement, new
independent notion, or new DAG node is needed. The node changes only in `lean`.

The source read is `literature/stacks-project/resolve.tex`, Tag 0BBT,
`lemma-dominate-by-normalized-blowing-up`, first two and fourth proof paragraphs.
The node expands precisely the normalization reduction, the finite BadCurves set
and empty base case, and the generic-stalk DVR/residue-field observations. Its
14-step proof is included step by step in the theorem docstring, with the
recorded proof dependencies as imports. The full tower of normalized blowups in
the source lemma is not this auxiliary node's statement.

Hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| X is a scheme | `{X : Scheme.{u}}` |
| X is integral | `[IsIntegral X]` |
| X is normal | `hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)`; integrality already supplies `IsDomain` for every stalk |
| X is Noetherian | `[IsNoetherian X]`, the scheme class extending locally Noetherian and compact |
| every affine coordinate ring of X is excellent | `hexcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U)` |
| X has topological dimension 2 | `hdim : topologicalKrullDim X = 2` |
| Y is integral | `[IsIntegral Y]` |
| f : Y → X is proper | `(f : Y ⟶ X) [IsProper f]` |
| the induced k(X) → k(Y) is an isomorphism | `hgeneric` identifies the image generic point with that of X, and `hbirational` is bijectivity of `X.presheaf.stalkCongr ... |>.inv` followed by the **actual** `f.stalkMap (genericPoint Y)` |
| ν : Z → Y is normalization in k(Y) | No arbitrary replacement is bound: Z is exactly `Y.normalization`, ν exactly `Y.fromNormalization`, and h exactly `Y.fromNormalization ≫ f` |

The generic-point equality is the data needed to type the stated induced field
map; it does not impose an additional mathematical hypothesis. A field-map
isomorphism induced by f is birationality and entails dominance, hence this
same equality. The transported stalk-map formula follows the recorded interface
of `lem-trf-finite-birational-normal-iso`, rather than introducing a second
birational predicate or an unrelated field isomorphism.

Clause correspondence (write h for the displayed composite only in this report):

1. ν finite and proper: `IsFinite Y.fromNormalization ∧ IsProper Y.fromNormalization`.
2. Z integral and Noetherian: `IsIntegral Y.normalization ∧ IsNoetherian Y.normalization`.
3. Z normal: all its stalks are `IsIntegrallyClosed`; their domain instances
   are supplied by the actual integral normalization (and integrality is also
   explicitly a conclusion).
4. Z excellent: `∀ U : Y.normalization.affineOpens, IsExcellent Γ(Y.normalization, U)`.
5. Z dimension two: `topologicalKrullDim Y.normalization = 2`.
6. h proper: `IsProper (Y.fromNormalization ≫ f)`.
7. h induces a function-field isomorphism: existential generic-point equality
   `hg`, followed by `Function.Bijective` of the transported actual generic stalk
   map `X.functionField ⟶ Y.normalization.functionField`.
8. Normal Y implies ν is an isomorphism: the implication from
   `∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)` to `IsIso Y.fromNormalization`.
9. Definition B(h): `h.exceptionalCurves : Set (IrreducibleCloseds Z)` consists
   exactly of supports C with `topologicalKrullDim (C : Set Z) = 1` and
   `∃ x : X, h '' (C : Set Z) = {x}`. `IrreducibleCloseds` includes nonemptiness,
   irreducibility and closedness. An integral closed subscheme of Z has radical
   ideal sheaf and is uniquely the reduced induced closed subscheme on its
   irreducible closed support. Conversely each such support has that integral
   reduced structure. Indexing by supports is therefore exactly the node's
   convention, not a restriction to a selected family or to isomorphism classes
   lacking an embedding. It also avoids counting isomorphic presentations of
   one embedded curve repeatedly. All requested local rings are on Z, so no
   extra scheme structure on a carrier C is used in the Lean formula.
10. B(h) finite: `h.exceptionalCurves.Finite`.
11. Every contraction point is closed: for each member C and every x with
    `h '' (C : Set Z) = {x}`, the assertion is `IsClosed ({x} : Set X)`.
12. h is an isomorphism iff B(h) is empty:
    `IsIso h ↔ h.exceptionalCurves = ∅`.
13. For every exceptional curve and its generic point: `∀ C ∈ h.exceptionalCurves,
    ∀ η : Z, IsGenericPoint η (C : Set Z) → ...`.
    This covers the unique generic point of every member; it does not assume
    an additional chosen section of a generic-point assignment.
14. The generic ambient local ring R_C is a DVR:
    `IsDiscreteValuationRing (Z.presheaf.stalk η)`; the domain instance is present.
15. The induced local-ring map is local:
    `IsLocalHom (h.stalkMap η).hom`.
16. That same map is injective: `Function.Injective (h.stalkMap η)`.
17. R_C is a subring of k(Z) with fraction field k(Z): the canonical Mathlib
    `stalkFunctionFieldAlgebra` is used in
    `IsFractionRing (Z.presheaf.stalk η) Z.functionField`.
18. The target local ring has the same fraction field **through the actual local
    map**: explicit `@IsFractionRing` with algebra
    `((algebraMap (Z.presheaf.stalk η) Z.functionField).comp
    (h.stalkMap η).hom).toAlgebra`. Thus the common field is k(Z), already
    identified canonically with k(X) by clause 7; no arbitrary algebra action or
    bare unrelated field equivalence replaces this compatibility.
19. The residue transcendence degree is one:
    `@Algebra.trdeg (X.residueField (h η)) (Z.residueField η) _ _
    ((h.residueFieldMap η).hom.toAlgebra) = 1`.
    It uses precisely the residue-field map induced by the local map, not an
    arbitrary extension structure. As the image is a singleton and η lies in C,
    h(η) is the contraction point x of the node.

Recorded dependency declarations used (full signatures and docstrings read in
the named source modules):

| Dependency | Module and declaration used |
| --- | --- |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral` |
| def-weil-pbc-normal-ring | `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed` together with stalk domain instances; a scheme is normal exactly when its local rings are normal domains |
| def-weil-pbc-noetherian-ring | `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`; scheme Noetherianity uses the existing `AlgebraicGeometry.IsNoetherian` class |
| def-exc-excellent-ring | `Sheaf.RingTheory.ExcellentRing`, `IsExcellent` (and its quasi-excellent/universally catenary definitions) |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`, `topologicalKrullDim` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper` |
| def-sc-function-field | `Sheaf.AlgebraicGeometry.FunctionField` publicly imports Mathlib's `AlgebraicGeometry.Scheme.functionField`, which the record explicitly specifies for arbitrary integral schemes; the component product is not needed on an integral scheme |
| def-sc-normalization | `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `AlgebraicGeometry.Scheme.normalization`, `AlgebraicGeometry.Scheme.fromNormalization` |
| def-sc-generic-point | `Mathlib.Topology.Sober`, `IsGenericPoint`, `genericPoint` |
| def-sc-discrete-valuation-ring | the dependency's mathlib_match: `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing` |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`, `AlgebraicGeometry.Scheme.residueField`, `AlgebraicGeometry.Scheme.Hom.residueFieldMap` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite` |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`; the support encoding uses the unique reduced induced structure rather than a private alternative definition of a closed immersion |
| def-kun-transcendence-degree | `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg` |

The normal-domain rendering on stalks is equivalent to the normal-ring
localization formulation: a local ring is a normal ring iff it is a normal
domain. Integral schemes already have domain stalks, so the normality hypotheses
and conclusions omit only redundant domain proof fields, not a condition.

Edge cases checked before writing: integral X and Y exclude the empty scheme
as the node requires; dimension two excludes fields and curves, not a surface
case. B(h) may be empty; its definition and both directions of the equivalence
explicitly retain that case. The identity of a normal excellent integral
Noetherian surface has no exceptional curves and normalization is an isomorphism.
A nonnormal Y is allowed and no normality assumption on Y was inserted; its
conditional clause remains an implication. Irreducible closed supports are
nonempty, so an empty support cannot count as a curve or provide a spurious
contraction point. No uniqueness assumption on a presentation of a curve is
imposed. All characteristics and arbitrary scheme universe u are permitted;
there are no independent test universes and no extra finite-type-over-a-field
assumption (the residue degree concerns the finite type fibre over κ(x)).

Searches performed (wrapper logs are in sandbox `searches.jsonl`):

* LeanFinder: `A proper birational modification of a normal excellent surface has
  finitely many exceptional curves, and their generic stalks are discrete
  valuation rings`. Eight results: relative normalization, valuative criterion,
  and minimal Weierstrass models; none has the exceptional-curve statement.
* Loogle: `AlgebraicGeometry.Scheme.normalization, IsDiscreteValuationRing`.
  No hits; Mathlib does not know the upstream absolute-normalization name.
* msearch grep, Mathlib/AlgebraicGeometry:
  `exceptionalCurve|BadCurves|badCurves|birational`. Eight hits concern the
  Birational/RationalMap modules; no exceptional-curve definition or theorem.
* LeanSearch: `A proper birational morphism of normal excellent surfaces has
  finitely many contracted curves, with DVR stalk at each curve generic point`.
  Eight proper-morphism class/projection/finite-proper results; no match.
* `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `lean/Sheaf` for `exceptionalCurve|BadCurves|badCurves|lem-per-normal-surface-exceptional-curves`:
  no existing definition or statement.
* `rg` of the chosen new declaration names over `dag/lean_names_upstream.json`,
  the upstream Lean tree and `lean/Sheaf`: no collision.
* Targeted source searches found the existing absolute normalization and generic
  stalk constructions and the recorded finite-birational normal-target theorem;
  these are reused rather than copied.

Validation: `scompile.py Q138 lem-per-normal-surface-exceptional-curves .../NormalSurfaceExceptionalCurves.lean`
passed both sandbox and library compilation (5.5 s and 4.9 s), without errors or
warnings. `set_option autoImplicit false` binds all variables and universe u.
The theorem has the expected sole sorry; both defining data and imports are real.
No STATEMENT-DISPUTED issue or source discrepancy was found.

## Second reading by Q138

This is a separate rereading pass by the same dispatched worker; the dispatch
forbids starting another agent, and the maintainer supplies independent review.
I reopened the node statement and the full module after compilation. The
hypotheses and clauses are matched individually above. In particular I checked
normality of X and of Z against their integral domain stalk instances, excellence
on every affine rather than only a convenient chart cover, and the original
normalization in k(Y) rather than an arbitrary finite cover. The helper indexes
supports with the reduced induced scheme convention, not all presentations of
closed immersions (which would incorrectly obstruct the finiteness claim).
The displayed field maps and local-ring actions are induced by f and h; the
residue algebra is induced by h.residueFieldMap. The quantification over generic
points includes every exceptional curve, and the equivalence includes the
empty-curve case. The full conclusion still includes finite/proper normalization,
normal/integral/excellent/Noetherian two-dimensional source, proper birational h,
the conditional normal-Y isomorphism, closed contraction points, the empty
criterion, DVR, local injectivity, common fraction field, and residue degree one.
This rereading found no missing hypothesis, omitted conclusion or statement
correction to make.
