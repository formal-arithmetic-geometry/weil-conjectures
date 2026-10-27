## What changed

Completed `AlgebraicGeometry.exists_stage_isAmple_of_limit_isAmple` in
`Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent`. The proof chooses the existing
finite affine section cover, descends its sections as maps of finitely presented
modules, and proves that their nonvanishing opens become affine and cover a stage.
All auxiliary constructions and lemmas are private and proved. The node proof now
records this argument. All original public imports remain unchanged; new imports
are private proof imports.

The index type now lies in the schemes' universe (`I : Type u`), implementing the
smallness convention used by all the declared affine-limit dependencies and
required by `coord/STATE.md`, “INDEX UNIVERSES FOR LIMITS AND FILTERED COLIMITS”. This is
an explicit restriction of the previous arbitrary-universe Lean interface, rather
than a proof of that former interface. See
`coord/changes/Z5-ample-affine-limit-index-smallness.md` for both signatures, the
22-module downstream audit, holders, and the two DAG citer checks. No downstream
statement or target is changed and no adaptation is necessary.

Validation: the assembled module compiles without warnings or local `sorry`.
The proof handles the empty limit and empty finite section cover: the common
upper bound includes the initial index, and eventual-cover descent then gives an
empty stage. Powers remain positive individually; no common tensor power or
nonempty cover is assumed. Pullback identifications are isomorphisms, and
nonvanishing opens are invariant under arbitrary isomorphisms of arrows.

## Proved and sorry left

Closed the sole body hole in
`AlgebraicGeometry.exists_stage_isAmple_of_limit_isAmple`, subject to the explicit
index-universe interface correction above. Item holes: 1 before, 0 after.
Added holes: 0. Split-off statements: 0. No `sorry` remains in the item or is added
elsewhere by this delivery.

The proof uses the existing statement
`AlgebraicGeometry.Scheme.Modules.finitePresentation_descent_affineLimit`
(node `lem-trf-fp-modules-affine-limit-descent`), whose existing hole is unchanged.
This is a complete proof from declared dependencies, not an axiom-free completion
of the transitive library. The finite affine cover and all glue lemmas used here
are proved.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent`: replace section-colimit
  descent by the morphism clause of finite-presentation descent, applied to the
  structure module and the relevant tensor powers.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`: use Mathlib's
  `opensDiagram`, `opensCone` and `isLimitOpensCone` directly.

The proof therefore does not use nodes
`lem-sc-valuation-limit-qcoh-section-descent` or
`lem-weil-pbc-limit-affine-transition`; removed these from this node's proof
route and its obsolete top-level tool approvals. No module is withdrawn and no
claim is made that these modules have no other users. The eventual-affine-stage
and quasi-compact-open-descent nodes remain, realized by their Mathlib APIs.
A temporary exploratory import of
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` was also removed;
none of its results is used.

## Where the brief, the DAG or earlier work was wrong

The previous Lean signature allowed an unconstrained separate index universe,
whereas its declared dependencies and Mathlib limit lemmas require a small index
in the schemes' universe. The interface correction is recorded explicitly in the
node's `statement_change` and the change record; no claim of a counterexample to
the larger-universe mathematical statement is made.

The planned section-descent interface is unnecessary for this proof. Sections
are maps from the structure module, so finite-presentation morphism descent
supplies the needed stage maps. Also, the quasi-compactness of each descended
nonvanishing open must be checked before eventual affineness; the private proof
uses a finite affine trivializing cover and principal opens. The final cover
uses `exists_map_eq_top` directly and does not require the full eventual-equality
statement for two arbitrary quasi-compact opens. The unit route is preserved;
its own statement and proof steps are unchanged.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
