## What changed

Proved `AlgebraicGeometry.Scheme.Hom.pic_restriction_divisor_correction` without changing its
signature. The proof constructs E = D - div(b), uses the divisor-class equivalence twice to
extract the principal representative and to kill its ambient Picard class, and proves every
retained coefficient vanishes. Added proof-only imports of DivisorRestrictionPicard and
PrincipalDivisorOpenExtension. Updated the target node to this decomposition.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Hom.pic_restriction_divisor_correction`
(lem-sc-pic-restriction-divisor-correction).

Added two strictly intermediate holes, so this is a decomposition (net holes: -1):
- `AlgebraicGeometry.Scheme.Hom.exists_divisor_restriction_picard`
  (lem-sc-divisor-restriction-picard): restrict any divisor and compute its Picard pullback.
- `AlgebraicGeometry.Scheme.Hom.exists_principal_divisor_open_extension`
  (lem-sc-principal-divisor-open-extension): extend any principal divisor with equal open orders.

All three modules compile together using lcompile.py. No data definitions or arbitrary
witness choices from holed existence statements are added. Witnesses are used only within
proofs of propositions. Both remaining assertions include complete proofs in words. Edge
cases checked: zero divisor, constant unit, and empty boundary; none requires a boundary point.

## No longer needed

No original imports removed; both public imports are required by the original signature.
In the new PrincipalDivisorOpenExtension module, replaced Picard by the narrower Divisor import: its
statement uses divisors and function fields, not Picard groups.
No original proof-dependency branches pruned: point-lift and boundary-triviality are needed
by the new restriction node; function-field and divisor definitions are needed by the new
principal-extension node. The divisor-class equivalence remains used directly.

## Where the brief, the DAG or earlier work was wrong

The planned restriction and transport steps had no Lean declarations expressing their
conclusions. The original class equivalence alone does not identify Picard pullback or
orders under an open immersion; these steps are now separate nodes. A proof of the
restriction step from the existing point-lift and boundary-triviality declarations was
attempted, but lcompile reports PicRestrictionPointLift.olean missing from the available
compiled library. That unverified attempt is not part of the delivery. The source blueprint
file named by the node is absent in this clone; the supplied node proof and existing theorem
docstrings give the source argument used here. The unit route is unchanged.

## New nodes

lem-sc-divisor-restriction-picard: DivisorRestrictionPicard.lean; Picard-compatible restriction
for arbitrary divisors, independent of the triviality hypothesis of the target.

lem-sc-principal-divisor-open-extension: PrincipalDivisorOpenExtension.lean; transport of
arbitrary principal divisors, independent of the given divisor and its Picard class.

No change records: no existing signature or definition changed.

## Second reading by D2

1. Compared the delivered target module with the repository using diff. Its entire existing
   theorem signature is now byte-for-byte unchanged, as is its docstring. Only the proof and
   two plain proof imports were added. The two sibling modules and nodes are new; there are
   no definitions or statement changes requiring change records.
2. All three modules compile locally with lcompile.py in import order. The only textual
   holes are the two public helper theorems listed above, each with a matching node and
   full proof docstring. There is no axiom, unsafe, opaque, extern, implemented_by, hollow
   definition, or arbitrary data choice. The witnesses R, a, b and the equivalences are
   eliminated inside a proposition proof; the final witness is explicitly D - div(b).
   The axiom probes and delivery preflight provide the final mechanical check.
3. Checked both new statements hypothesis by hypothesis: smooth connected curves give
   integral regular dimension-one schemes; finite type gives Noetherianity; the dense open
   immersion identifies generic and retained closed stalks. Restriction retains coefficients
   and sends point-ideal classes to their pullbacks; extension only asserts agreement of
   principal orders on the open. Neither helper assumes triviality of D's Picard pullback
   or concludes the target normal form, so neither restates the target. For D=0 use R=0;
   for a constant unit choose its constant ambient extension; for empty boundary the same
   constructions work and the final E is zero. Repeated LeanFinder, Loogle and grep searches
   with different queries, and read Curve.Picard, Curve.Divisor, FunctionField,
   OrderOfVanishing, PicRestrictionPointLift and PicRestrictionBoundaryTrivial. No existing
   arbitrary-divisor restriction or principal-extension statement was found. The two
   single-point modules are present as source but still absent from the compiled library,
   so the restriction helper could not be closed against the permitted build.
4. Read the proof top down: hR plus hD kills toPic(R); injectivity of the divisor-class
   equivalence yields R=div(a); extension supplies b; the ambient equivalence kills
   toPic(div(b)); subtraction gives both clauses. Both new imports are proof-only. The
   original point-lift and boundary-triviality nodes remain dependencies of the restriction
   helper, and function-field and divisor nodes remain dependencies of extension: none of
   the old proof branches is pruned. Read dag/units/sk-prop-ext-invariance.json, whose
   realized statement and three step lists are empty on the base. This delivery does not
   alter them or bypass the affine compactification/Picard restriction route. The referenced
   blueprint source is absent locally, as the first report already notes; this reading uses
   the supplied source-derived node proof and existing docstrings, not a claim of having
   opened the missing paper file.
5. Checked the item's proof/proof_deps against each Lean step, and the two new nodes'
   signatures, chapter, unit, origin, source, searches, and created/lean records. The
   dependency lists equal the unions of step uses. The target statement and stmt_deps
   are unchanged. New node natural-language statements match both quantified conclusions.

Changed only the accidental extra space before the target's proof delimiter, narrowed the
new principal-extension module's public Picard import to Divisor, added independent search
records, and recorded this reading. No proof or helper statement needed mathematical repair.
This remains one upper hole closed and two lower holes added, a decomposition with net -1.
