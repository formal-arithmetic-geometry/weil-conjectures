## What changed

Proved `AlgebraicGeometry.Etale.exists_etale_limit_finite_cover_descent` with its
signature unchanged. Added two proof-only imports: the new finite diagram module
and `Sheaf.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage`.

Added and proved `AlgebraicGeometry.Etale.exists_etale_limit_finite_diagram_descent`
in its own module. Its two private helpers are fully proved: a qcqs single-model
construction from 01ZM and 07RP, and simultaneous scheme-arrow descent for an
arbitrary finite index type. The latter generalizes the Fin n proof pattern of
`FinitePullbackHomDescent`, directly using the same existing spreading-out theorem.
There are no new definitions, changed interfaces, or forced adaptations.

The final proof transfers joint surjectivity through the limit isomorphisms,
descends it using the existing finite-family theorem, and uses pullbackComp
naturality for the exact arrow equations. Cover-preservation supplies all later
stages. Both modules compile cleanly with lcompile.py --all.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.exists_etale_limit_finite_cover_descent`
(node `lem-weil-pbc-etale-limit-finite-cover-descent`).

Also proved the new declaration:
`AlgebraicGeometry.Etale.exists_etale_limit_finite_diagram_descent`
(node `lem-weil-pbc-etale-limit-finite-diagram-descent`).

No sorry remains in either delivered module; no holes were added or split off.
This is a proof from existing library declarations, including their current
transitive proof dependencies; it does not claim the full target closure is
axiom-free. The new helpers contain no sorry. Net delivered holes: one closed,
zero added.

## No longer needed

No original import was removed: the original module imported only the common site
interface. The unused exploratory proof import
`Sheaf.AlgebraicGeometry.FinitePullbackHomDescent` was removed from the new module.
Its narrower Fin n theorem is replaced here by a proved private helper using
01ZM directly, preserving the original Type (u + 1) finite index universe.

The planned `lem-weil-pbc-limit-affine-transition` and module
`Sheaf.AlgebraicGeometry.LimitAffineTransition` are unnecessary on this proof
branch. The limit cone is already supplied; only its affine projections are
needed, via the Mathlib leaf
`lem-weil-pbc-limit-cone-affine-projections-opens` and `isAffineHom_π_app`.
No existence-of-limit construction or restricted-open limit is needed.

There is no need to import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` for the planned continuous
base-change interface: its covering clause is supplied directly by
`Scheme.Hom.coverPreserving_etale` from the original site interface. The broader
base-change-continuity node is retained as the mathematical covering-preservation
reference. This report makes no claim that either module is globally unreachable.

The spreading-out, étaleness descent, cartesian-square pasting, qcqs permanence,
and surjectivity descent facts remain needed, the last through the existing
finite-family theorem. No affine-objects restriction or sheaf machinery is imported.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's broad affine-limit existence theorem is
unnecessary because the statement already supplies a limit. The module initially
had none of the plan's proof imports, despite the standing brief describing them
as present; the proof now imports exactly its required theorem interfaces.

Read Stacks Tags 01ZM, 07RP, and 07RR on their official pages. The affine finite
diagram theorem is not directly applicable to arbitrary qcqs etale objects. Its
single-model and pullback comparison proof patterns do generalize after removing
the unnecessary eventual-affineness step, which is what the new proof does.

Edge cases: K empty is included throughout. Option K retains the target model,
the arrow-descent clauses are vacuous, and the existing finite-family theorem
forces eventual empty target when the empty limit family covers. The index
preorder need not be antisymmetric or have a least element. Directedness and
nonemptiness supply finite upper bounds. No finite-presentation, separation, or
nonempty-source hypothesis was added. The unit sk-thm-p1 route is unchanged.

The finite-family joint-surjectivity node is an existing tool from the curve
estimates chapter, justified here by the exact 07RR step; no sheaf-cohomology
route is substituted. The nearest blueprint ancestor is retained from the
item's existing blueprint.from record; the local ancestor tool returned None.

## New nodes

`lem-weil-pbc-etale-limit-finite-diagram-descent`: the object-and-arrow portion
of the original plan, with no covering assumption or conclusion, fully proved
in its new module. It uses 01ZM for finite-presentation models and morphisms,
07RP for eventual etaleness, and explicit finite upper bounds and pullback
comparisons. It adds no hole. Recorded searches were actually run: LeanSearch
was unavailable (Internal Server Error), LeanFinder gave only partial scheme
limit results, and grep found no exact general qcqs finite-diagram theorem.
Blueprint search `finite.*(diagram|cover).*descent` returned no imported match.
No change record is needed: existing signatures and public imports are unchanged.

## Second reading by S2

1. Compared both delivered modules with the repository version. The existing target
   declaration has the identical signature; the new diagram declaration is recorded
   by its node and introduces no alteration to an existing interface. Verdict: pass.

2. Compiled both modules with `lcompile.py --all`. There are no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by` declarations in the delivered
   files. The proofs use only ordinary library declarations and preserve the stated
   hypotheses, including the empty-family case. Verdict: pass.

3. Checked the new diagram statement against the source plan and searched the
   repository and Mathlib-facing search tools for an existing theorem. It is the
   strict object-and-arrow reduction of the target, with no covering conclusion,
   and its node contains the source, proof steps, dependencies, and searches.
   Verdict: pass.

4. Read the proof from the target downward. The target uses the new diagram result
   and the existing finite-family surjectivity result; the diagram proof uses the
   affine projection, spreading-out, etale descent, pullback pasting, and qcqs
   permanence interfaces. The exploratory finite-pullback import is absent from
   the final module and is documented above as no longer needed. Verdict: pass.

5. Checked the DAG records and unit route. The target node and new diagram node
   agree with the declarations and proof dependencies, and unit `sk-thm-p1` remains
   realized through the original target route. Verdict: pass.

Changed during second reading: added this review record only; no Lean proof or
statement changes were necessary.
