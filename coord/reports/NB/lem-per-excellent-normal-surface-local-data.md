## Worker report

The module `Sheaf.AlgebraicGeometry.ExcellentNormalSurfaceLocalData` states
`AlgebraicGeometry.excellent_normal_surface_local_data`, with one postponed proof and no
new definitions. The node's statement and dependencies are unchanged. No statement dispute
or mathematical correction was needed.

Hypothesis and conclusion correspondence:

- `X : Scheme.{u}` is the arbitrary scheme; `[IsIntegral X]` expresses integral, including
  nonemptiness, using the recorded declaration of def-pc-integral-scheme.
- `[IsNoetherian X]` expresses the stated finite affine Noetherian cover. Mathlib's
  `AlgebraicGeometry.isNoetherian_iff_of_finite_iSup_eq_top` and
  `isNoetherian_iff_of_finite_affine_openCover` identify this with that precise condition;
  local Noetherianity alone would omit finiteness and is deliberately insufficient.
- `hNormal : ∀ x, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed ...` expresses normality
  by the normal local domains at all points, with the recorded normal-domain conjunction
  of def-weil-pbc-normal-ring. This is the existing inline stalk convention, not a new
  normality definition. The side library's `IsNormalScheme` additionally packages
  integrality, already supplied here by `[IsIntegral X]`.
- `hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U)` is excellence on every affine
  open, including the empty one, not just on a selected chart or on the stalks.
- `hDim : topologicalKrullDim X = 2` is dimension of the entire scheme, not the dimension
  of each closed point or an equidimensionality assumption.
- `IsOpen {x | IsRegularLocalRing (X.presheaf.stalk x)}` renders precisely openness of the
  regular locus defined in the statement, using the ring clause of def-weil-regular-scheme.
- `{x | ¬ IsRegularLocalRing ...}.Finite` renders finiteness of its complement.
- The final universal quantifier is over exactly the nonregular points. `IsClosed ({x} :
  Set X)` says each is a closed point. The following six stalk clauses respectively say
  excellent, Noetherian, domain, integrally closed, local, and dimension two.
- The ring appearing in all completion clauses is exactly
  `AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)`.
  No arbitrary complete extension or unspecified comparison ring is substituted.
- Its clauses respectively give Noetherianity, domain, integral closure, locality,
  completeness for its OWN maximal ideal (`IsAdicComplete`), and dimension two. Thus
  completeness is stated for the local-ring topology, not merely for an unnamed ideal
  of the original stalk. Mathlib's canonical completion-locality instance makes that
  maximal ideal well typed using Noetherianity of the original stalk.

Dependency declarations read and used:

- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: `IsIntegrallyClosed`; normal domains
  are its recorded conjunction with `IsDomain`.
- Mathlib.RingTheory.KrullDimension.Basic: `ringKrullDim`.
- Sheaf.AlgebraicGeometry.IsRegularScheme: `AlgebraicGeometry.IsRegularScheme`, whose
  source and ring clauses use Mathlib's `IsRegularLocalRing`. The theorem needs the ring
  clause pointwise, rather than asserting the entire surface is regular.
- Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsIntegral`.
- Sheaf.RingTheory.ExcellentRing: `IsExcellent`, including `IsQuasiExcellent`, J-2 and
  `IsUniversallyCatenary`.
- Mathlib.RingTheory.AdicCompletion.Basic (through LocalRing): `AdicCompletion` and
  `IsAdicComplete`; LocalRing supplies the maximal-ideal completion's local structure.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`.

All recorded proof modules available for this node are imported without `public` when
used only by the proof plan: affine/closed-point finiteness, localization of excellence,
Noetherian completion, dimension of completion, flat ascent of normality, regularity of
G-ring completions, regular implies normal, and Serre's criterion. Mathlib localization
and spectrum modules supply the proof's prime-localization and closed-subset dictionary.
The theorem docstring records all ten steps of the DAG proof, including the localization
identification, the attained length-two chain argument, and normal ascent to completion.

Sources read locally: more-algebra.tex definition-excellent and
lemma-finite-type-over-excellent (07QT/07QU), lemma-completion-normal-local-ring (0C23),
lemma-completion-dimension (07NV), and resolve.tex theorem-resolve (0BGP). The finite
singular-set use is in 0BGP, as already explained in the node's stage-1 review; the old
source.place pointer to 0BGN is not used as a replacement for that argument.

Edge cases checked mathematically:

- A regular surface has empty singular locus: openness and finiteness hold and all local
  conclusions are vacuous; the theorem does not require any singular point to exist.
- The empty scheme is excluded by integrality and dimension two, exactly as in the node.
- Fields and DVRs have dimension zero and one and are excluded by the surface hypothesis.
- A non-Jacobson surface can have closed height-one points, but normality makes their
  stalks regular; the theorem does not assert that every closed point has dimension two.
- No separatedness, Jacobson condition, finite type over a field, chosen ample module,
  characteristic restriction, or equidimensionality hypothesis is imposed.
- The singular quadric cone supplies the familiar nonempty case: its singular maximal
  stalk has dimension two and normal completion; the predicate selects that stalk.
- The zero ring is allowed on the empty affine open. It is not a singular stalk of this
  integral nonempty scheme. Universes are bound explicitly; no test universe is restricted.

Searches for an existing statement (all through the authorized tools or named sources):

- msearch.py leanfinder, query "An excellent normal Noetherian surface has finitely many
  closed singular points and normal completed local rings of dimension two": eight hits,
  including IsIntegral, IsLocallyNoetherian, finite_irreducibleComponents_of_isNoetherian,
  the Noetherian stalk instance and DVR TFAE; none states this theorem.
- msearch.py loogle, query `IsRegularLocalRing, AdicCompletion`: zero hits.
- msearch.py leansearch, query "excellent normal surface regular locus finite singular
  points complete local normal domain": eight hits concerning smooth/unramified loci,
  normal topological spaces and normalization; none is the assertion.
- msearch.py grep, query `singular[Ll]ocus|[Nn]ormal.*[Cc]ompletion|[Cc]ompletion.*[Nn]ormal`:
  zero Mathlib hits.
- rg of the same concepts plus `excellent_normal_surface_local_data`, `regularLocus` and
  `singularLocus` in lean/Sheaf and the upstream WeilConjectures tree found related
  desingularization consumers, regular-locus algebra criteria and normality predicates,
  but no declaration stating this result. The exact node-id search upstream gave no hit.
- Read the located NormalScheme and Regular modules; no private predicate was introduced.

Validation: the module is compiled through scompile.py and the delivery is checked through
both the dry-run preflight and its normal delivery gate. Their final results are recorded
below after those commands complete.

## Second reading by NB

A separate second pass by this same dispatcher-started worker compared the full node and
module; no sub-agent was started, as the brief forbids that. Independent maintainer review
remains part of the delivery process. This pass checked each conjunct against the list
above, especially finite affine Noetherianity versus merely local Noetherianity, all affine
opens in hExcellent, actual stalks in hNormal, dimension of X, the negative regularity
predicate in the singular set, closedness in X, and the maximal ideal of the completion
itself in the completeness clause. No extra geometric assumptions or missing clauses were
found. No new node, dependency repair or statement correction was necessary.

Validation results: scompile.py passed both the sandbox and library-name compilation with
no errors or warnings (2.1 s and 2.8 s). The dry-run delivery printed
`OK (dry run): commit e14577a89b passes the preflight and compiles; nothing pushed`.
All Lean lines are at most 100 characters. Only the permitted `lean` field differs in the
node copy; the source statement, proof and dependency lists are preserved.
