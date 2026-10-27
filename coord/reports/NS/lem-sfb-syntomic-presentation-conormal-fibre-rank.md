## Worker report

Prepared `lean/Sheaf/RingTheory/SyntomicPresentationConormalFibreRank.lean`, declaring
`Algebra.syntomic_presentation_conormal_fibre_rank` with one `sorry`. No definitions,
new nodes, dependency repairs or statement corrections were needed. Only the item's
`lean` field is changed in the sandbox copy.

Validation is incomplete: two prescribed scompile.py attempts both failed on the
server with `resource exhausted (error code: 28, no space left on device)` after
approximately 10.3 seconds. Neither returned Lean elaboration diagnostics. No claim
of a clean compile or completed delivery is made. The launcher scripts, shared
repository, and published build were not modified. No direct git command was run.

Hypothesis and conclusion correspondence:

- The commutative ring map R to S is `[CommRing R] [CommRing S] [Algebra R S]`,
  with independent universes u and v.
- Syntomic flatness is `[Module.Flat R S]`, equivalent to the recorded
  `RingHom.Flat (algebraMap R S)` by `RingHom.flat_algebraMap_iff`.
- Syntomic finite presentation is `[FinitePresentation R S]`.
- Every residue-field fibre is a local complete intersection: `hci` quantifies
  over all `p : PrimeSpectrum R` and uses the existing
  `IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S)`.
  The finite-type instance on each fibre follows from finite presentation and
  Mathlib's finite-type base-change instance, as in the landed sibling
  SyntomicPolynomialKernelKoszulRegular.lean.
- The chosen polynomial presentation has `n : ℕ`,
  `α : MvPolynomial (Fin n) R →ₐ[R] S`, and `hα : Function.Surjective α`.
- Its finitely generated kernel is `hJ : (RingHom.ker α.toRingHom).FG`.
- The conormal is Mathlib's `(Extension.ofSurjective α hα).Cotangent`, a type
  synonym for the kernel modulo its square with its canonical S-module action.
- Finite projectivity is rendered in the node's explicit direct-summand sense:
  there are a natural m and S-linear maps i to S^m and r back with
  `r.comp i = LinearMap.id`. This includes the finite-generation assertion.
- The fibre ring is `p.asIdeal.Fiber S`, canonically k tensor_R S; tensor symmetry
  identifies it with the node's S tensor_R k. Its residue field is
  `p.asIdeal.ResidueField`, the residue field of the prime localization.
- The coefficient-reduced polynomial presentation is the existing
  `((Generators.ofAlgHom α hα).baseChange p.asIdeal.ResidueField).toExtension`.
  Its ring is literally `MvPolynomial (Fin n) p.asIdeal.ResidueField`, and its
  variables map to `1 tensor α(X_i)`. Its kernel therefore is the node's Jbar.
- The comparison uses the canonical tensor-associativity and symmetry identification
  N tensor_S F = k tensor_R N. It asserts existence of a k-linear equivalence e
  from this tensor to the reduced presentation's conormal, with its value on every
  pure tensor of a kernel class prescribed by coefficient reduction. For every a,
  j and j', `j'.val = MvPolynomial.map (algebraMap R k) j.val` implies
  `e (a tensor Cotangent.mk j) = a • Cotangent.mk j'`.
  Reduction of each kernel element does belong to Jbar, so the formula is not
  vacuous. Surjectivity of Cotangent.mk and spanning by pure tensors make e unique.
  Multiplying j by a polynomial lift of any s in S shows this same formula is
  S-equivariant; together with k-linearity it is F-linear under the canonical
  tensor identification. Thus the assertion identifies the canonical map rather
  than asserting an arbitrary abstract isomorphism.
- For every `q : PrimeSpectrum (p.asIdeal.Fiber S)`, the last clause gives a
  natural d with `topologicalKrullDimAt q = (d : WithBot ℕ∞)` and `d ≤ n`,
  and a basis indexed by `Fin (n - d)` over `Localization.AtPrime q.asIdeal`
  of the localization of the reduced conormal. This spells out that the point
  dimension is finite, n-d is the integer difference, and the localized conormal
  is free of exactly that rank. No local-ring Krull dimension is substituted.

Dependency declarations read and used:

- Mathlib.RingTheory.RingHom.Flat: RingHom.Flat and flat_algebraMap_iff; Module.Flat.
- Mathlib.RingTheory.FinitePresentation: Algebra.FinitePresentation.
- WeilConjectures.RingTheory.CompleteIntersectionOverField:
  Algebra.IsLocalCompleteIntersection and IsGlobalCompleteIntersection.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField and
  Scheme.Hom.residueFieldMap. For the ring-prime specialization the file uses
  Mathlib's Ideal.ResidueField (the residue field of Localization.AtPrime), and
  Mathlib.RingTheory.LocalRing.ResidueField.Fiber: Ideal.Fiber. The scheme-level
  record is not redefined; the ring-prime presentation is the standard existing
  Mathlib specialization also used by the recorded syntomic-at-prime dependency.
- Mathlib.Algebra.MvPolynomial.Basic/Eval: MvPolynomial, aeval, algHom_ext, map.
- WeilConjectures.Mathlib.Topology.KrullDimension: topologicalKrullDimAt, whose
  definition is the infimum over open neighbourhoods, exactly the node's notion.
- Mathlib.RingTheory.Extension.Basic: Extension.ofSurjective, Cotangent,
  Cotangent.mk; Extension.Generators: Generators.ofAlgHom and baseChange.

Proof-dependency modules are imported without `public`: syntomic-at-prime-relative-
global-complete-intersection; conormal-module-principal-localization; relative-global-
complete-intersection-conormal-free; finite-projective-prime-local-free;
affine-standard-cover-finite-projective; flat-quotient-tensor-injective;
polynomial-scalar-extension; tensor-right-exact; lci-conormal-free-rank-codimension;
projective-module. Basic-open cover facts and flat-local-ring-maps are supplied by
Mathlib imports already present. The declaration docstring follows all seven proof
steps of the DAG, including the finite-free splitting and the flat quotient argument.

Edge cases checked mathematically: S = 0 (zero conormal and empty spectrum); a zero
fibre (zero comparison and no q); J = 0 (polynomial fibre, d = n and rank zero);
k[x]/(x^2) (d = 0 and rank one); n = 0 (zero conormal for a flat finitely presented
quotient of R). No characteristic, Noetherian, nontriviality, connectedness, or common
rank hypothesis is imposed. The rank is allowed to vary with p and q.

Searches performed using the prescribed msearch.py wrapper:

- leanfinder: "The conormal of a syntomic polynomial presentation is finite projective
  and commutes with residue field base change with rank equal to codimension".
  Eight hits: finite H1Cotangent, standard smoothness, free-conormal presentation,
  formal smoothness, and finite conormal; none states the conjunction.
- loogle: "Algebra.Extension.Cotangent, Module.Projective": zero hits.
- grep, RingTheory: "[Ss]yntomic|[Cc]otangent.*[Pp]rojective|[Pp]rojective.*[Cc]otangent":
  zero hits.
- leansearch: "The conormal module of a syntomic algebra is finite projective and
  has fibre rank equal to codimension": eight hits on formally smooth differentials,
  standard smooth rank, finite conormal, and related smoothness criteria; none matches.
- rg of both lean/WeilConjectures and lean/Sheaf for syntomic/conormal names and
  the proposed declaration name found no existing statement. grep of the exact node
  id in lean/WeilConjectures found no match. The Sheaf syntomic lifting consumer
  mentions this node only in its proof docstring.
- Read Mathlib Extension/Generators, Extension/Basic, Cotangent/BaseChange and the
  existing conormal principal-localization and lci-rank modules. The flat base-change
  conormal equivalence in Mathlib assumes the tensor factor is flat; it does not
  apply here, since k need not be R-flat.

Source checks: read algebra.tex's lemma-syntomic-presentation-ideal-mod-squares
(Tag 07BT, g = 1) and lemma-lci (Tag 00SC, (1) implies (4)), including the relevant
proofs. Read the current latest blueprint direct-images proof (3); this auxiliary
ring input supports the inherited route described in the DAG. No change to a unit
or target statement is proposed. No STATEMENT-DISPUTED finding.

## Second reading by NS

Self rereading only: the dispatcher expressly prohibits starting another agent,
and the maintainer's independent review has not occurred. Reread the DAG statement
against the sandbox signature. Checked all three syntomic hypotheses, the arbitrary
chosen presentation and its FG kernel, the explicit finite-free splitting, every
base prime, the coefficient-reduction formula, every fibre prime, and the use of
local topological dimension. The tensor-associativity encoding of the comparison
must be read with the formula as explained above, not as an arbitrary k-vector-space
isomorphism. No discrepancy was found in this rereading. Compilation and independent
review remain outstanding because the server's filesystem is full.

## Resumed validation (2026-10-24)

Retained the saved packet and first ran the required
`deliver2.py NS lem-sfb-syntomic-presentation-conormal-fibre-rank --no-push`.
It exited 1 with `COMPILE FAILED on the server, nothing pushed`, followed by
`sandbox Sheaf.Stage2.Sandbox0` and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A fresh direct prescribed `scompile.py` call on the saved module also exited 1
with the same sandbox name and identical resource-exhaustion error (10.3 s).
Neither returned Lean elaboration diagnostics. This is an actual server tool
failure, not a missing declaration or a Lean diagnostic that can be repaired
in this packet. No launcher script, live source, or server artifact was changed.

Reopened the current item and all six statement-dependency records; there is no
released repair note for this item. The saved node differs from the current
shared node only in `lean`. Reread its syntomic assumptions, chosen surjective
polynomial presentation, FG kernel, finite-free splitting, coefficient-reduction
comparison, and pointwise dimension/rank clause against the saved signature.
The recorded signature matches the module verbatim, every line is within
100 columns, autoImplicit is disabled, both universes are explicitly declared,
and the only postponed declaration is the named theorem with its proof docstring.
The statement and module were retained. Compilation, dry-run success, and push
remain incomplete because both authorized validation entry points fail on the
server's full filesystem.

## Retry validation (2026-10-24 10:29 UTC)

Retained the saved packet and again ran the prescribed dry run first.
`deliver2.py NS lem-sfb-syntomic-presentation-conormal-fibre-rank --no-push`
exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A direct prescribed `scompile.py` retry on the saved module also exited 1
with the identical resource-exhaustion error and duration. Neither produced
a Lean elaboration diagnostic. The tool failure persists before statement
validation, and cannot be repaired by changing the delivery. No push occurred.

Checked the current node and all six statement-dependency records again.
No repair note exists; only the lean field differs from the current node.
The module, recorded signature, and earlier mathematical self-check are
retained. No direct Git command, live-source edit, launcher-script edit,
or server cleanup was performed. Compilation and delivery remain incomplete.

## Retry validation (2026-10-24 10:31 UTC)

Retained the saved packet and ran the required dry run first:
`deliver2.py NS lem-sfb-syntomic-presentation-conormal-fibre-rank --no-push`.
It exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A direct prescribed `scompile.py` retry of the saved module also exited 1
with the same sandbox and resource-exhaustion error (10.3 s).
Neither returned Lean elaboration diagnostics. The server tool failure persists;
there is no packet diagnostic to repair. The saved Lean module and node were
retained, and no delivery was pushed. No launcher script, shared source, server
artifact, or Git state was directly modified.

## Retry validation (2026-10-24 10:34 UTC)

Inspected the retained report and ran the required dry run first.
`deliver2.py NS lem-sfb-syntomic-presentation-conormal-fibre-rank --no-push`
exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A direct prescribed `scompile.py` retry on the saved module also exited 1
with the identical resource-exhaustion error (10.3 s). Neither returned
Lean elaboration diagnostics. This remains an actual server tool failure;
there is no packet diagnostic to repair. No push occurred.

Reread the saved module and node. Verified against the current shared node
that only `lean` differs, the recorded signature is verbatim, no line exceeds
100 columns, and no item repair note exists. Retained the existing statement,
module, and mathematical correspondence report. No launcher script, shared
source, server artifact, or Git state was directly modified. The packet remains
uncompiled and undelivered because both authorized validation entry points fail
on the server's full filesystem.

## Retry validation (2026-10-24 10:37 UTC)

Inspected the saved report and first ran the required deliver2.py dry run.
It exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A direct prescribed scompile.py retry on the retained module exited 1
with the identical sandbox and resource-exhaustion error (10.3 s).
Neither returned Lean elaboration diagnostics. No push occurred.

Reread the retained module and current node: only `lean` differs, the
recorded signature matches verbatim, no line exceeds 100 columns, and
there is no item repair note. Retained all statement work. The server
filesystem failure prevents validation; no packet diagnostic is available
to repair. No shared source, launcher script, server artifact, or Git state
was directly modified.

## Retry validation (2026-10-24 10:41 UTC)

Inspected the saved report and first ran the prescribed deliver2.py dry run.
It exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A direct prescribed scompile.py retry on the retained module also exited 1
with the same sandbox and resource-exhaustion error (10.3 s). Neither
returned a Lean elaboration diagnostic. No push occurred.

Reread the retained module, current item and six statement-dependency records.
Only `lean` differs from the current shared item; its recorded signature
matches the module verbatim and all lines satisfy the 100-column limit.
No item repair note exists. Retained the statement and earlier mathematical
self-check. This server filesystem failure prevents validation and supplies
no packet diagnostic to repair. No shared source, launcher script, server
artifact, or Git state was directly modified.

## Retry validation (2026-10-24 10:44 UTC)

Inspected the retained report and first ran the prescribed deliver2.py dry run.
It exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A direct prescribed scompile.py retry on the retained module also exited 1
with the identical sandbox and resource-exhaustion error (10.3 s). Neither
returned Lean elaboration diagnostics. No push occurred.

Reread the retained module, current item and all six statement-dependency records.
Only `lean` differs from the current shared node; the recorded signature matches
the module verbatim and all lines satisfy the 100-column limit. No item repair
note exists. Retained the statement and earlier mathematical correspondence.
Both authorized validation entry points fail on the server filesystem before
packet validation; there is no Lean diagnostic to repair. No shared source,
launcher script, server artifact, or Git state was directly modified.

## Retry validation (2026-10-24 10:47 UTC)

Inspected the saved report and first ran the prescribed deliver2.py dry run.
It exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
The initial SSH multiplexing refusal was followed by this server response.
A direct prescribed scompile.py retry on the retained module also exited 1
with the identical sandbox and resource-exhaustion error (10.3 s). Neither
returned Lean elaboration diagnostics. No push occurred.

Reread the saved module, current item and all six statement-dependency records.
Only `lean` differs from the current shared node; the recorded signature matches
the module verbatim and all lines satisfy the 100-column limit. No item repair
note exists. Retained the packet and its earlier mathematical correspondence.
Both authorized validation entry points fail on the server filesystem; there
is no Lean diagnostic to repair. No shared source, launcher script, server
artifact, or Git state was directly modified.

## Retry validation (2026-10-24 10:51 UTC)

Inspected the saved report and first ran the prescribed deliver2.py dry run.
It exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A direct prescribed scompile.py retry on the retained module also exited 1
with the same sandbox and resource-exhaustion error (10.3 s). Neither
returned Lean elaboration diagnostics. No push occurred.

Reread the saved module, current item and all six statement-dependency records.
Only `lean` differs from the current shared node; the recorded signature matches
the module verbatim up to `:=`, and no line exceeds 100 columns. There is no
item repair note. Retained the statement and earlier mathematical correspondence.
Both authorized validation entry points fail on the server filesystem before
Lean validation; there is no packet diagnostic to repair. No shared source,
launcher script, server artifact, or Git state was directly modified.

## Retry validation (2026-10-24 10:54 UTC)

Inspected the retained report and first ran the prescribed deliver2.py dry run.
It exited 1 with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)` (10.3 s).
A direct prescribed scompile.py retry on the retained module also exited 1
with the identical sandbox and resource-exhaustion error (10.3 s). Neither
returned Lean elaboration diagnostics. No push occurred.

Reread the retained module, current item and all six statement-dependency records.
Only `lean` differs from the current shared node; its recorded signature matches
verbatim and all module lines satisfy the 100-column limit. No item repair note
exists. Retained the packet and its earlier mathematical correspondence. Both
authorized validation entry points fail on the server filesystem; there is no
packet diagnostic to repair. No shared source, launcher script, server artifact,
or Git state was directly modified.

## Successful resumed validation (2026-10-24 11:00 UTC)

Retained the saved packet and ran the prescribed dry run first. It initially
failed with the same server filesystem exhaustion recorded above. The direct
prescribed scompile.py retry then passed with exit code 0: sandbox module
Sheaf.Stage2.Sandbox0 compiled in 2.5 seconds and library module
Sheaf.RingTheory.SyntomicPresentationConormalFibreRank compiled in 2.8 seconds,
with no diagnostics. The filesystem failure no longer prevents compilation.

Repeated deliver2.py with --no-push; it passed preflight and compilation,
printing `OK (dry run): commit f2e60fd63e4 passes the preflight and compiles;
nothing pushed`. This supersedes the earlier incomplete-validation status.

Self-check: reread the current node, all six statement-dependency records,
and the saved module; reopened the dependency definitions and docstrings.
Only the item's lean field differs from the current shared node. Its recorded
signature is verbatim, all lines are within 100 columns, autoImplicit is false,
and both universes are explicit. Rechecked the finite-free splitting, all base
primes, the coefficient-reduction characterization of the canonical comparison,
and all fibre primes with the topological dimension and rank n-d. No change to
the statement or module was needed. The earlier edge-case checks and mathematical
correspondence remain valid. No independent reviewer is claimed; the dispatcher
prohibits starting another agent. No direct Git command, shared-source edit,
launcher-script edit, or server cleanup was performed.
