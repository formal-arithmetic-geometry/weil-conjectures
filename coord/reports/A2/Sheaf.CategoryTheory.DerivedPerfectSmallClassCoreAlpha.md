## What changed

Repaired the source interface in `Sheaf.CategoryTheory.DerivedPerfectSmallClassCoreAlpha`:
Krause's alpha-compact objects are the maximal class of alpha-small objects satisfying
coproduct factorization (G4), rather than ordinary `IsCardinalPresentable` objects in
D(A). `AlphaCompactObject` defines that notion as an actual proposition with an
explicit witnessing class; no data or definition contains a hole.

The core now constructs a common regular bound using a small representative set of P,
objectwise ranks, monotonicity and isomorphism transport. It combines the bounded class
smallness theorem with proved zero, shift and coproduct closure to supply all clauses.
The rank theorem is also proved: the union of the regular alpha-compact classes is
localizing, contains the well-generators, and consequently contains every object.
The eventual-class theorem is proved by choosing well-generators and applying the
generic maximal-class identification at every larger regular cardinal.

`AlphaCompactObjectProperties` proves the support/factorization API, G4 implies G2,
monotonicity, repletion, retracts, equivalences, shifts, zero, regular bounded coproducts,
and extension closure of alpha-small objects. It proves the converse G2-to-G4
for an essentially small bounded-coproduct-closed class, and perfectness of
coproduct representative classes. It also proves the size of bounded
coproduct, extension and integer-shift classes and detection of zero by localizing generators.
These are concrete parts of the two remaining source arguments, not additional holes.
Every API theorem passes a kernel axiom check using only propext, Classical.choice
and Quot.sound. Rank-zero and arbitrary-zero-object edge checks also compile.
The two source obligations remain visible as sorryAx in the assembled core and ranks.

Adapted the unclaimed `DerivedPerfectSmallClassCore` and
`DerivedPerfectSmallClassProperties` together. The Core now returns equality with the
canonical alpha-compact class. Properties transports G4 across that equality and lifts
components; alpha-smallness gives its support-factorization clause directly.
Kept `DerivedPerfectSmallClassFactorization` as a forced interface adaptation for
holder C1. The returned head had replaced it by an empty module; this repair restores
the exact public imports and declaration so C1's existing interface remains available.
The declaration is still unused by the corrected Properties route and remains a
separate existing sorry.
The final `derived_exists_perfectSmallClass` statement and proof remain verbatim, and
its original file compiles against the new interfaces. All Challenge statements and
all definitions they use remain verbatim. The unit's localizing/Brown-representability
route is preserved.

All delivered modules have been compiled individually through lcompile, including
the unchanged final consumer and DerivedLocalizingPerfectFamily. Verification-only
copies were removed from the delivery after they compiled. Consumer and holder checks are recorded in four change
records. This is an interface correction requiring independent CODEX review.

## Proved and sorry left

The original item had one sorry, `CategoryTheory.derived_exists_alphaCompactClass_core`.
Its old ordinary-presentability signature is corrected, not proved as originally
written. The corrected theorem has a complete Lean proof and zero local sorries.
Do not count the source repair itself as a proof of the old statement.
The corrected argument is a decomposition into two genuinely different source facts.

Fully proved, with no local holes:

- `CategoryTheory.derived_exists_alphaCompact_rank`: localizing union of ranks.
- `CategoryTheory.derived_alphaCompact_classes_eventually_small`: simultaneous class
  bound from well-generators and the generic maximal-class lemma.
- The corrected `CategoryTheory.derived_exists_alphaCompactClass_core`: common-rank
  selection and assembly of repletion, smallness, triangulated and sum closure.
- The corrected `CategoryTheory.derived_exists_perfectSmallClass_core` and
  `CategoryTheory.derived_perfectSmallClass_properties`: consumer glue and perfectness.
- Every declaration of `AlphaCompactObjectProperties`, including the small-support
  extension argument, bounded coproduct/extension size bounds and double-orthogonal
  proof that localizing generators detect zero.

The two holes added, each a sole public theorem with an exact `by sorry`, source,
complete proof in words and matching node, are:

- `CategoryTheory.derived_exists_perfect_well_generators`
  (`new-sfb-derived-perfect-well-generators`). Still needs the set-generated-kernel /
  compact quotient well-generation argument. The conversions from perfectness to
  G4, perfectness of coproduct classes, and size of bounded coproduct classes have
  now been proved in this session. It uses the already declared Gabriel--Popescu presentation
  and exact derived localization. It does not mention a prescribed P or the canonical
  alpha-compact classes at all cardinals.
- `CategoryTheory.alphaCompactObjects_small_closed`
  (`new-sfb-alpha-compact-class-small-closed`). Still needs the transfinite alpha-hull
  construction and weak-kernel/G4 argument identifying that hull with the maximal
  class. Bounded coproduct, extension and shift-closure smallness, alpha-small closure, retraction
  and shift transport, and generator detection of zero have been proved in this
  session. This generic theorem assumes an actual small perfect generating family;
  it does not assert existence of one or choose a cardinal for a family P.

The finite-support theorem remains an existing sorry in the restored C1 interface;
it is not used by the corrected route and is still marked `STATEMENT-DISPUTED` below.
Actual local hole count: zero in the item and the proved APIs/consumers, two in the
new source modules. No axiom declaration, private sorry, partial-proof sorry or
holed definition is added. Existing holes in imported project modules are not
claimed as proved by this delivery.

## No longer needed

Removed `Mathlib.CategoryTheory.Presentable.Basic` from CoreAlpha, Core and Properties:
its ordinary categorical notion is not Krause's triangulated alpha-compactness.

Removed both proof imports from Properties:

- The finite-support theorem in `Sheaf.CategoryTheory.DerivedPerfectSmallClassFactorization`,
  node `new-sfb-derived-perfect-small-class-factorization`, is no longer used by the
  corrected Properties route. The module is retained only to preserve C1's public
  interface; its existing node and declaration remain unchanged.
- `Sheaf.CategoryTheory.DerivedPerfectSmallClassFiniteLifting`, node
  `new-sfb-derived-perfect-small-class-finite-lifting`: a true finite lifting lemma
  rendered unnecessary by direct G4 lifting. No remaining module imports it after
  this delivery. Leave its existing theorem intact, and prune it from this route.

Removed Properties' statement dependency on
`new-sfb-derived-perfect-small-class-core`: its universal hypothesis now explicitly
identifies S with the canonical class from the definition node, so it does not use
an existence theorem in its statement. Core itself remains used by the final theorem.

The original CoreAlpha proof dependency `lem-grothendieck-derived-has-coproducts`
remains necessary. No dependency realizing a blueprint unit statement or proof step
is bypassed. The exploratory ordinary-presentability attempt is not delivered.


## Forced adaptations

`Sheaf.CategoryTheory.DerivedPerfectSmallClassFactorization` (holder C1) was
adapted because the returned head had an empty replacement module. Compiling the
unchanged downstream interface against that returned head produced the original
error `unknown constant CategoryTheory.derived_factor_through_small_subcoproduct`
when the pre-existing Properties interface referenced the declaration. The repair
restores the exact C1 module text: its public imports and the existing theorem
`CategoryTheory.derived_factor_through_small_subcoproduct` are restored verbatim.
No theorem signature, visibility, or proof content was changed, and no helper was
added. These lines are forced solely to preserve C1's existing interface; the
corrected Properties proof does not use the theorem.

## Where the brief, the DAG or earlier work was wrong

The previous core silently translated alpha-compactness to ordinary
`IsCardinalPresentable`. Krause (2001), page 122, defines the maximal class by (G3)--(G4).
Localization theory 6.10.2 discusses presentability in an abelianization/functor
category, not this identification inside the original triangulated category.
The corrected interface restores the cited source argument; the final perfect-class
conclusion is unchanged. The previous core proof plan cited only existence of derived
coproducts, which does not supply either well-generation or the maximal-class theorem.

STATEMENT-DISPUTED: `CategoryTheory.derived_factor_through_small_subcoproduct`
asserted finite support for every regular alpha. In D(k), equivalently graded vector
spaces, the countable sum U of k[0] is aleph1-presentable, but its identity cannot factor
through any finite subcoproduct. The finite-subset indexing poset is not aleph1-filtered:
the countable family of singleton subsets has no finite upper bound. The false declaration remains only as the restored C1 interface; no weakened replacement is claimed as its proof.

The old created.item chain stores module names rather than node ids, so the mechanical
blueprint ancestor for this item is broken. The new nodes record the actual ancestor,
`lem-sfb-dc-proper-pushforward-left-adjoint-e`, through the perfect-class,
solution-set and localizing representability chain. Existing blueprint/created fields
are maintainer-owned and are not altered here.

Sources read directly and wanted in the tracked literature catalogue (their PDFs are
currently only in the sandbox scratchpad): Neeman, On the derived category of sheaves
on a manifold, Theorem 0.2 and Section 2; Krause, On Neeman's Well Generated
Triangulated Categories (2001), pages 121--125, especially Lemmas 4--5;
Krause, Localization theory for triangulated categories, 6.2--6.3 and 6.10.2;
Alonso--Jeremias--Souto, Localization in categories of complexes and unbounded
resolutions, Proposition 5.1. Node sources point to the actual blueprint proof place,
with these exact external references in their source.place and Lean docstrings.

## New nodes

`def-sfb-alpha-compact-object` records the actual support and G4 definitions and the
maximal witnessing-class proposition. Module `AlphaCompactObject` has no holes.

`lem-sfb-alpha-compact-object-api` records all proved support, factorization, transport,
closure, smallness and generator-detection APIs, both directions between G4 and
perfectness for a small bounded-coproduct-closed class, and perfectness of coproduct
representative classes in `AlphaCompactObjectProperties`.

`new-sfb-derived-perfect-well-generators` supplies a small shift-closed G4 family with
a common smallness rank and localizing generation. This is the derived-existence part
of the argument; its two off-unit generic presentation/localization tools are declared
in split_report.tool_uses.

`new-sfb-alpha-compact-class-small-closed` supplies the generic smallness/extension
closure of the maximal alpha-compact class given a small perfect generating family.
This is the hull-identification part, with the concrete elementary APIs already proved.

`new-sfb-derived-alpha-compact-classes` is proved from the preceding two source facts
and monotonicity, and yields one bound valid for every larger regular cardinal.

`new-sfb-derived-alpha-compact-ranks` is proved by the localizing union argument,
including a regular bound for an arbitrary family of summands. It is not handed on
as another sorry.

Change records:
`coord/changes/a2-alpha-compact-core.md`,
`coord/changes/a2-alpha-compact-core-consumer.md`,
`coord/changes/a2-alpha-compact-properties.md`,
`coord/changes/a2-withdraw-false-finite-factorization.md`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
