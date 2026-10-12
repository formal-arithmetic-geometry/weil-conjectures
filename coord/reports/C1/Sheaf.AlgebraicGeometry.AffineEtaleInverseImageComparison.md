## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.exists_affineEtale_inverseImage_comparison` with a complete
compiling proof assembling four smaller inputs. The theorem's signature and existing
public imports are unchanged.

The proof fixes `U` to `affineEtaleBaseChange` and `t` to the definitional identity
isomorphism. From `AlgebraicGeometry.affineEtaleSiteBaseChange` it obtains covering
preservation, continuity, and finite-limit preservation of the canonical affine
`sheafPullback`. It chooses the canonical `sheafAdjunctionContinuous` as `a`.
It extracts the full-site composition isomorphism and unit formula from
`AlgebraicGeometry.etaleSetInverseImageCompositionUnits` and specializes to affine
morphisms. Two new, strictly smaller statements supply (1) restriction comparison
with its unit equation, and (2) composition coherence given such comparisons and
full-site composition data. The main proof constructs every existential witness
and conjunction from these inputs; no statement is merely renamed.

Added proof-only imports of `AffineEtaleRestrictionUnit` and
`AffineEtaleRestrictionComposition`. Updated the original node's proof,
proof dependencies, and proof origin to match the Lean reduction. Added one module
and one node for each intermediate theorem. No definition or statement was changed.

Local compilation of all three modules in import order succeeds without warnings.
The required delivery dry run is the final validation. The proof closes the local
hole, but remains dependent on the named theorems left unproved below it; this is a
stage-3 reduction, not a claim of a sorry-free target closure.

## Proved and sorry left

Proved, with no direct `sorry`:
`AlgebraicGeometry.Scheme.exists_affineEtale_inverseImage_comparison`
(node `lem-weil-pbc-sets-affine-etale-inverse-image-comparison`).

Every direct `sorry` in the delivery:

- `AlgebraicGeometry.Scheme.affineEtale_inverseImage_restriction_unit`, in
  `Sheaf.AlgebraicGeometry.AffineEtaleRestrictionUnit`, node
  `lem-weil-pbc-affine-etale-restriction-unit`.
- `AlgebraicGeometry.Scheme.affineEtale_inverseImage_restriction_composition`, in
  `Sheaf.AlgebraicGeometry.AffineEtaleRestrictionComposition`, node
  `lem-weil-pbc-affine-etale-restriction-composition`.

The first intermediate proves only existence of the restriction comparisons and
single-morphism unit equations for given adjunctions. The second assumes those
comparisons and the full-site composition data, then constructs affine composition
and proves its square. Neither includes covering preservation, continuity,
finite-limit preservation, or existence of the full-site composition comparison.
Neither is the original proposition with a hypothesis repackaged.

Edge cases checked mathematically: identity morphisms reduce to comparison of
adjunctions with an identity base-change functor; empty schemes admit the same
adjunction argument; non-affine base schemes cause no use of a terminal affine-site
object. Arbitrary choices of `t` are conjugated into `gamma`, so the statement does
not silently require canonical `t`. Arbitrary choices of `a` and `e` are allowed:
unit compatibility determines their mates, and the composite proof uses their
specified units. The two new statements impose no finite-limit or covering
hypothesis beyond the continuity needed to type their right adjoints.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.SiteMorphismComposition`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already publicly available
  through the statement imports).

The original node no longer directly uses
`lem-weil-pbc-affine-etale-site-topos`,
`lem-weil-pbc-etale-base-change-continuous`,
`def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-conjugate-iso-unit-equation`,
`lem-weil-pbc-site-morphism-composition`, or `def-pc-fibre-product`.
The topos equivalence and conjugate-unit uniqueness remain necessary for the new
restriction-unit intermediate. Fibre products, composite adjunctions and
conjugate-unit uniqueness remain necessary for the new composition intermediate.
The base-change-continuity and sites/cohomology nodes are not separately needed by
these new proofs: precomposition is explicit in the right adjoints and continuity
is a supplied hypothesis. This does not assert that these nodes are absent from
other branches or from the existing base-change theorem's own proof.

`Sheaf.CategoryTheory.SiteMorphismComposition` is not needed in this reduction or
in the new composition argument: the latter composes the given adjunctions and
uses the mate of the induced right-adjoint isomorphism. It does not need a theorem
that simultaneously reproves site continuity, covering preservation and exactness.
The main module's public imports were retained because they describe its existing
interface; none was converted to a private proof import.

## Where the brief, the DAG or earlier work was wrong

The existing `siteMorphism_composition` interface requires
`Precoverage.IsStableUnderComposition` and `SmallCategory` inputs and ties the
coefficient universe to the site universe. In particular, the finite-covering
precoverage does not furnish the strict indexed-composition instance: its own
`IsSpecialCocontinuousForCoverings` documentation explicitly explains this.
Applying this theorem directly is therefore not the planned few-line glue.
Composition of the already supplied adjunctions and the right-adjoint comparison
is sufficient for the needed unit formula, without these unrelated requirements.

`fullAffineEtaleInclusion_special_equivalences` states its sets equivalence for
`Type u` for a scheme in universe `u`, while the target is about `Type (u + 1)`.
The first new intermediate is true for that universe by the same special
cocontinuity / 04HR argument, but its future proof must use that argument or the
generic coefficient-valued comparison API; simply applying the existing
coefficient-specific conjunct does not typecheck. No existing statement was
changed in this delivery.

The clone does not contain the Stacks source files named by the node. Read the
available source pages and obtained the current `topologies.tex` and `sites.tex`
in this item's scratchpad. Tag 04HR supplies affine restriction equivalence;
03CB supplies composition via uniqueness of left adjoints. Current 09YQ's proof
only invokes 04HR and a colimit lemma; it does not spell out this unit/coherence
calculation. The new nodes mark the detailed argument as written by C1 from these
sources and the original node's plan, rather than attributing those details to
an explicit passage of 09YQ.

LeanSearch was attempted twice and returned an Internal Server Error. Recorded
it as unavailable without drawing an absence verdict. LeanFinder, Loogle, source
grep, and library grep were also performed. The successful search found generic
`Adjunction.restrictFullyFaithful`, unit equations, `conjugateIsoEquiv`, and
sheaf pushforward comparison APIs; no existing theorem supplies the full affine
restriction-unit comparison or its composite square.

## New nodes

`lem-weil-pbc-affine-etale-restriction-unit`, module
`Sheaf.AlgebraicGeometry.AffineEtaleRestrictionUnit`: the part of the original
plan that transports a given inverse-image adjunction through affine restriction
and evaluates its unit. Its docstring and node give the right-adjoint comparison,
conjugation by equivalences, and evaluated mate equation. This excludes all
base-change construction and composition assertions of the original theorem.

`lem-weil-pbc-affine-etale-restriction-composition`, module
`Sheaf.AlgebraicGeometry.AffineEtaleRestrictionComposition`: the remaining
coherence part for already given unit-compatible `e` and `c`. Its node gives the
full-faithfulness construction of `gamma`, the mate construction of `d`, and the
comparison of transposes after cancelling the iterated restriction isomorphism.
The unit route `sk-thm-iff` and its realized nodes are unchanged.

No change record is required: no existing statement, definition, or public import
was changed.

## Second reading by C1

1. **Visible interface: pass.** Compared the original module with the repository using
   `diff`, then compared the substring from the theorem name to `:= by` byte for byte.
   The existing signature, definitions, docstring and public imports are unchanged.
   The existing node differs only in `proof`, `proof_deps`, and `proof_origin`.
   There is no target or existing statement change and no change record is needed.

2. **Lean proof and trust: pass as a reduction.** Compiled all three modules with
   `lcompile.py --all`, without errors or warnings. The original module has no
   `sorry`; the new modules have exactly the two named theorem holes listed above.
   No definitions or forbidden declarations were introduced. A scratch copy with
   `#print axioms` for all three declarations reports only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is expected from the
   stated open dependencies; this delivery does not certify final target closure.

3. **New statements: pass.** Read both full signatures, docstrings and nodes.
   Restriction-unit comparison is the mate of the right-adjoint comparison after
   transport by restriction equivalences. Composition first lifts the conjugated
   base-change isomorphism through the fully faithful inclusion, then takes its
   mate for the composed affine adjunction. Cancelling the iterated restriction
   comparison puts the final square under that adjunction's injective hom-set
   equivalence, where the assumed unit equations prove it. The orientation of
   every section restriction agrees with the displayed contravariant maps.
   Identity morphisms, empty schemes, non-affine bases, and noncanonical `t` and
   adjunction choices impose no additional hypotheses: `t` is conjugated into
   `gamma`, and units determine the relevant mates. The 04HR refinement argument
   works for `Type (u + 1)` although the existing coefficient-specific equivalence
   conjunct only states `Type u`. Neither split theorem restates the original:
   covering preservation and finite-limit preservation are obtained independently,
   and coherence assumes the separately supplied single-morphism comparisons.
   These categorical calculations cannot be closed by a few-minute tactic proof.

   Repeated searches using different terminology: LeanFinder's Beck–Chevalley /
   equivalence-of-sites query gave generic sheaf equivalence tools; Loogle's
   `CategoryTheory.conjugateIsoEquiv` gave the generic mate API and component
   formulas. Read the corresponding Mathlib Mates, Restrict and Continuous APIs
   and searched the project with restriction/pullback/comparison terminology.
   No existing affine comparison or its coherence square was found. Checked the
   available Stacks source: 04HR's affine refinement argument and the adjoint
   uniqueness argument in Sites' composition lemma support the reductions.

4. **Route and pruning: pass.** The main proof explicitly constructs canonical
   `U`, `t`, `L` and `a`, extracts base-change preservation and full-site
   composition units, and assembles the two smaller statements. The old
   `proof_deps` minus the new ones is exactly the six-node list already reported
   under `No longer needed`. Those still used below the new intermediates remain
   named there. Read `dag/units/sk-thm-iff.json`: its statement and realized step
   are unchanged and no unit step is bypassed. Existing public imports supply
   the statement's data and instances; both added imports are proof-only.

5. **DAG agreement: pass after repairs.** The main node's three steps and four
   dependencies match the Lean proof. Both new nodes have the required source,
   searches, proof steps, matching declaration/signature, creation, blueprint,
   chapter, unit and split records. Their proof dependencies equal the unions
   of their steps' `uses`. The restriction-unit node had described the
   right-adjoint composites in the wrong verbal order; corrected it explicitly
   to `R_h` followed by `rho_X`, versus `rho_Y` followed by `A_h`.

Second-reading changes: narrowed each new module's public import of
`EtaleInverseImageAlgebraicStructures` to `EtaleSheaves`, which defines the
`etaleSetPullback` appearing in the statements; the algebraic-structures theorem
is not needed by either intermediate. Updated their new-node `stmt_deps` to
`def-weil-pbc-etale-sheaves`. This prunes that direct import from the new modules,
not from the original module's existing full-site composition dependency.
Added the second reader's successful search records, corrected the right-adjoint
ordering in the new restriction-unit node, clarified the coefficient universe
in its docstring, and explained cancellation before affine adjoint transposition
in the new composition docstring. No Lean statement or proof body was changed.
