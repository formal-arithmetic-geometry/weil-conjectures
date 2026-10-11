## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect`
states `AlgebraicGeometry.Scheme.isPerfect_schemeDerivedDirectImage_of_bounded_coherent_finiteTor`
with a `sorry` proof. It introduces no definitions. The declaration docstring carries
all four DAG proof steps and their dependencies.

Hypothesis and conclusion correspondence:

- Schemes X and S and the morphism f: `{X S : Scheme.{u}}` and `(f : X ⟶ S)`.
- S Noetherian: `[IsNoetherian S]`, with no Noetherian or quasi-compact hypothesis on X.
- f locally of finite type: `[LocallyOfFiniteType f]`; properness of f is not assumed.
- E in D(𝒪_X): `(E : schemeDerivedCategory X)` on the shared SheafOfModules carrier.
- Bounded E: `hbounded` asserts vanishing of every cohomology object outside an
  existential integer interval. It imposes no fixed bound or restriction on its signs.
- Coherent cohomology: `hcoherent` applies `RingedSpace.IsCoherent X.toRingedSpace`
  to every integer-indexed `DerivedCategory.homologyFunctor` object of E.
- Every cohomology sheaf has support proper over S: `hsupport` applies the dependency's
  `Scheme.Modules.HasSupportProperOver f` to precisely those same objects. The predicate
  includes closedness and properness of the reduced induced closed subscheme.
- Finite Tor dimension over f⁻¹𝒪_S: `hTor : HasFiniteTorDimensionOver f E`, which restricts
  scalars along the structure map and uses a K-flat resolution with a uniform finite
  tensor-cohomology interval for all inverse-image-ring module sheaves.
- Conclusion: `IsPerfect S ((schemeDerivedDirectImage f).obj E)`, the recorded locally
  strictly-perfect predicate on the recorded derived direct image, in D(𝒪_S).
- Explicit HasDerivedCategory binders provide the localization categories of X, S and
  all opens of S required by these recorded declarations. The source and target
  morphism universes wX and wS are independent; no new geometric hypothesis is imposed.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.DerivedCategory: AlgebraicGeometry.schemeDerivedCategory.
- Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage:
  AlgebraicGeometry.schemeDerivedDirectImage.
- Sheaf.AlgebraicGeometry.PerfectComplex: AlgebraicGeometry.Scheme.IsPerfect,
  which uses Scheme.IsStrictlyPerfect.
- Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase:
  AlgebraicGeometry.Scheme.Modules.HasSupportProperOver, using
  Scheme.IsClosedSubsetProperOver.
- Sheaf.AlgebraicGeometry.FiniteTorDimensionOver:
  AlgebraicGeometry.Scheme.HasFiniteTorDimensionOver (landed node
  def-pc-finite-tor-dimension-over, added to stmt_deps).
- Sheaf.AlgebraicGeometry.Coherent: AlgebraicGeometry.RingedSpace.IsCoherent
  (landed node pqf-def-coherent, added to stmt_deps).
- Mathlib.AlgebraicGeometry.Noetherian: IsNoetherian;
  Mathlib's LocallyOfFiniteType and DerivedCategory.homologyFunctor.

Edge cases checked before writing: zero E admits any nonempty bounding interval and
empty supports; the conclusion is perfect zero. Empty X or S is not excluded. Bounds
may be negative, zero or positive. The statement does not force E itself to be perfect
over 𝒪_X. For f = identity it gives the usual bounded-coherent finite-Tor criterion.
Nonproper f is permitted when all cohomological supports are proper, as in the source.
An unbounded E fails hbounded and does not enter the theorem. No characteristic or
nonempty-space assumption is introduced.

Searches for an existing statement:

- msearch LeanFinder, “proper pushforward of bounded coherent finite Tor complex is
  perfect”: eight Mathlib derived-category T-structure hits, no scheme direct-image
  perfectness theorem.
- msearch Loogle, “IsPerfect, HasFiniteTorDimensionOver”: zero hits; IsPerfect unknown.
- msearch LeanSearch, “proper pushforward bounded coherent finite Tor dimension perfect
  complex”: unavailable, Internal Server Error.
- msearch grep, `HasFiniteTorDimensionOver|schemeDerivedDirectImage` in Mathlib
  AlgebraicGeometry: zero hits.
- rg in the source WeilConjectures/AlgebraicGeometry for
  `IsPerfect|HasFiniteTorDimensionOver|bounded.*coherent`: zero hits; broader source
  searches find unrelated étale constructible finite-Tor and ring-perfectness theorems.
- grep of the exact item id throughout source WeilConjectures: zero hits.
- rg in lean/Sheaf for bounded coherence and finite Tor finds DirectImageBoundedCoherent,
  ProperDirectImageFiniteTor and the shared definitions, but no theorem with this exact
  conclusion and hypotheses. The proper-perfect-morphism theorem is a different statement.

Source verification: read https://stacks.math.columbia.edu/tag/08EV, hypotheses (1)-(3),
conclusion and proof. They match the node without correction. The node source.document
names more-morphisms.tex, although Tag 08EV belongs to perfect.tex; this pre-existing
bibliographic fault is reported here and left unchanged under the permitted field rule.
The local Stacks source checkout is absent. No statement dispute or correction is needed.

Validation: lcompile.py compiled the single module with exit code 0 and no warnings.
The final server compile and maintainer preflight are run by deliver2.py --no-push.
No delivery is pushed; independent second reading remains the second worker's task.


## Second reading by Q1

Independent source reading: Stacks Tag 08EV, and the actual TeX
`perfect.tex`, `lemma-perfect-direct-image`, including the preceding section
“Producing perfect complexes” and the entire proof. The section introduces no
standing extra assumptions. The source is
https://stacks.math.columbia.edu/tag/08EV and the TeX was read from
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex.
No statement correction is present or needed. The source.document bibliographic
mismatch already noted by the worker does not change the source tag's statement.

Object/hypothesis/conclusion checklist (node, source and Lean compared separately):

- X and S are schemes, with a scheme morphism f: `{X S : Scheme.{u}}`
  and `(f : X ⟶ S)`. PASS. Opened Mathlib's Scheme and Scheme.Hom definitions:
  the objects are locally ringed spaces locally isomorphic to affine spectra,
  and their maps are locally ringed-space morphisms.
- S is Noetherian: `[IsNoetherian S]`. PASS. Opened the class: locally
  Noetherian plus compact, the global Noetherian notion required here.
- f is locally of finite type: `[LocallyOfFiniteType f]`. PASS. Opened its
  affine-section ring-map definition. There is no properness, separatedness,
  quasi-compactness or global finite-type hypothesis on f.
- E lies in D(O_X): `(E : schemeDerivedCategory X)`. PASS. Read
  def-pc-derived-category and DerivedCategory.lean: this is the localization
  of complexes of all shared O_X-module sheaves, not only quasi-coherent ones.
- E is bounded: `hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
  IsZero ((DerivedCategory.homologyFunctor ... i).obj E)`. PASS. A single
  finite integer interval bounds all cohomology, not a pointwise local bound.
- E has coherent cohomology: `hcoherent : ∀ i : ℤ,
  RingedSpace.IsCoherent X.toRingedSpace (H^i(E))`. PASS. Read pqf-def-coherent
  and Coherent.lean: finite type and finite-type kernels of all finite-free
  maps on all opens. This is coherence, not finite presentation alone.
- Each H^i(E) has support proper over S: `hsupport : ∀ i : ℤ,
  Scheme.Modules.HasSupportProperOver f (H^i(E))`. PASS. Read
  def-weil-pbc-closed-subset-proper-over-base and ClosedSubsetProperOverBase.lean:
  the closed subset is exactly the nonzero-stalk locus, and its reduced induced
  closed subscheme maps properly to S. It does not assert properness of f.
- E has finite Tor dimension in D(f⁻¹O_S):
  `hTor : HasFiniteTorDimensionOver f E`. PASS. Read the dependency node
  def-pc-finite-tor-dimension-over and FiniteTorDimensionOver.lean in full:
  scalars are restricted along f⁻¹O_S → O_X, a K-flat resolution computes the
  derived tensor, and one finite interval works for every f⁻¹O_S-module sheaf.
  Neither finite Tor dimension over O_X nor a conclusion about Rf_*E is
  substituted for this hypothesis.
- Conclusion Rf_*E is perfect in D(O_S):
  `IsPerfect S ((schemeDerivedDirectImage f).obj E)`. PASS. Read
  def-pc-derived-direct-image and SchemeDerivedDirectImage.lean, then its
  RingedSpaceDerivedDirectImage dependency: this is the unbounded right derived
  module direct image computed by K-injective resolutions. Read
  def-pc-perfect-complex and PerfectComplex.lean: every point has an open where
  the restriction is represented by a bounded complex of finite-free summands.
  There are no additional conclusion clauses.
- The three HasDerivedCategory binders supply precisely the localization
  categories used by E, Rf_*E and restriction to opens of S. PASS. These are
  categorical infrastructure, not geometric or finiteness assumptions.
  All variables and universes are bound; wX and wS remain independent.
  The common scheme universe u is arbitrary, with no small-universe test
  quantifier, and is the universe of the recorded Scheme.Hom convention.

Edge cases: zero E and empty support are admitted; empty X and empty S are
not excluded; the perfectness predicate is vacuous on an empty S. Integer
bounds can have either sign; a = b = 0 permits degree-zero objects. Allowing
b < a in hbounded only admits zero-cohomology objects, already covered by a
nonempty interval, so it does not change boundedness. The finite free ranks in
the dependency include rank zero. There is no index family requiring a
nonempty index, no field assumption, and no characteristic restriction.
Nonproper f with proper cohomological supports remains included. For f = id
the statement specializes to bounded coherent finite-Tor perfectness.

Independent duplicate searches (different wording from the worker):

- msearch LeanFinder: “direct image complex coherent cohomology proper support
  perfect on noetherian scheme”. Eight hits, mainly derived T-structure bounds,
  affine transition limits and IsFiniteType; none states this theorem.
- msearch Loogle: “LocallyOfFiniteType, DerivedCategory”. No hits; the service
  does not recognize LocallyOfFiniteType.
- msearch LeanSearch: “derived pushforward finite tor amplitude proper support
  perfect”. Service unavailable (Internal Server Error), not a negative result.
- rg of Mathlib/AlgebraicGeometry, source WeilConjectures/AlgebraicGeometry and
  project lean/Sheaf/AlgebraicGeometry for perfect with direct/push, bounded
  with coherent, and finiteTor/FiniteTor: no Mathlib or source theorem matching
  this statement. Opened ProperSupportPerfectDirectImage.lean (a different
  finite-presentation/base-flat tensor and base-change theorem) and
  ProperPerfectDirectImagePerfect.lean (proper perfect morphisms and perfect
  input), confirming that neither replaces this node.
- rg of the exact node id and 08EV in the upstream name index and source tree:
  no matching declaration. The shared finite-Tor, coherent, perfect and support
  definitions above are used without making a private copy.

Delivery inspection: one statement module, no new definition nodes or dependency
modules. No definitions or auxiliary proofs are introduced. The sole theorem
proof is `by sorry`. The source and blueprint marker occur in both docstrings;
all four proof steps, including the essential passage from relative Tor dimension
of E to Tor dimension of Rf_*E, are present with their DAG dependencies. Imports,
namespace, line lengths and explicit binders follow the project conventions.
The node's lean.statement is the unchanged signature in the module.

Mismatches and repairs: no mathematical or Lean mismatch found. Preserved the
module and node signature; appended this independent reading to the report.
Validation: local single-file compilation and deliver2 server compilation and
preflight, with the dry run before the actual delivery.
