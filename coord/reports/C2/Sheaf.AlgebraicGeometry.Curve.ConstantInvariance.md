## What changed

Proved `AlgebraicGeometry.IsConnectedCurve.constant_cohomology_baseChange_compatible` in
`Sheaf.AlgebraicGeometry.Curve.ConstantInvariance`, preserving its complete original signature.
The proof constructs the prescribed canonical pullback, proves its bijectivity, constructs the
primitive-root cohomology equivalences with the prescribed maps, and assembles every compatibility
clause. Base-change curve structure and both Jacobian clauses use the existing stated declarations.
The proper degree-one coordinates are obtained from proper cohomology and transported through the
inverse of the bijective pullback. Picard restriction to the compactification commutes by
`Pic.map_comp` and `pullback.lift_fst`.

Added four modules, each with one theorem and a corresponding DAG node. Three carry remaining
parts of the argument: degrees zero and one, the primitive-root sheaf square, and proper degree-two
coordinates together with the compactification genus equality. The fourth,
`ConstantKummerNaturality`, is proved from the primitive-root square and the existing
`kummer_base_change_compatibility`: its inclusion, Picard boundary and units boundary equations
are all real Lean proofs. In degree two the main theorem now uses the proper-or-affine dichotomy:
compatible degree coordinates imply bijectivity in the proper case, and affine cohomological
dimension gives bijectivity between zero groups in the affine case. Degrees at least three use
curve cohomological dimension over both fields. Updated the parent node's proof and dependencies
and documented each new theorem's source and complete proof in words.

All added imports of the existing module are private proof imports. No existing definition or
statement was changed, and no target signature was changed. The fixed proper/affine Kummer and
Jacobian route of the unit is retained.

## Proved and sorry left

Proved, with no `sorry` in their bodies:

- `AlgebraicGeometry.IsConnectedCurve.constant_cohomology_baseChange_compatible`
  (`thm-sc-constant-invariance`): the original module's one `sorry` is closed by a compiling
  reduction to named statements.
- `AlgebraicGeometry.IsConnectedCurve.constant_kummer_baseChange_naturality`
  (`lem-sc-constant-kummer-naturality`): the three transported Kummer equations.

Exactly three new `sorry`s remain, each the whole proof of a public named theorem:

- `AlgebraicGeometry.IsConnectedCurve.constant_low_degree_baseChange_bijective`
  (`lem-sc-constant-low-degree-base-change`), module `ConstantLowDegreeBaseChange`:
  bijectivity only in degrees zero and one.
- `AlgebraicGeometry.constant_root_trivialization_baseChange`
  (`lem-sc-root-trivialization-base-change`), module `RootTrivializationBaseChange`:
  the primitive-root square of sheaf morphisms. This statement works for any field extension
  with the given primitive roots; no algebraic closedness or curve hypotheses are needed.
- `AlgebraicGeometry.IsConnectedCurve.constant_proper_degree_coordinates`
  (`lem-sc-constant-proper-degree-coordinates`), module `ConstantProperDegreeCoordinates`:
  equality of source and compactification genera and compatible degree-normalized H2 coordinates.

The imported stage-2 declarations still have their existing obligations; this is a stage-3
reduction, not a claim of a sorry-free target closure. Edge cases checked from the definitions
and the source argument: n = 1 gives zero cohomology, the identity field extension gives the
canonical identity squares, arbitrary composite n is allowed, and the hypotheses exclude n = 0
and the characteristic dividing n. Proper compactification genus equality is justified by the
nonempty open-and-closed image of the proper open immersion into the connected compactification.
The primitive-root square requires only the supplied roots, so it remains valid outside the
algebraically closed setting used by its consumer.

## No longer needed

Removed these eight private proof imports from `ConstantInvariance`:

- `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility`
- `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange`
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final`
- `WeilConjectures.AlgebraicGeometry.Curve.Brauer`
- `WeilConjectures.AlgebraicGeometry.Curve.Kummer`
- `WeilConjectures.AlgebraicGeometry.DensePoints`
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`

These are no longer direct imports for the main proof. The parent's direct proof dependencies
no longer include `lem-weil-separably-closed-geometrically-connected`,
`def-pc-geometrically-irreducible`, `lem-sc-brauer-zero`, `lem-sc-kummer-les`,
`lem-sc-kummer-base-change-compatibility`, `lem-sc-pic-proper-ntorsion`,
`thm-sc-jacobian-representability`, `thm-av-final`, `lem-pc-rational-points-dense`,
`thm-sc-affine-cohomology`, `lem-sc-units-quotient-base-change`, or `lem-sc-pic-affine`.
The first two are supplied through the base-change curve interface. The Kummer, Picard,
Jacobian and units ingredients remain in the new intermediate nodes' proof plans or in
existing dependencies' plans, so they cannot all be removed from the library's global closure.
No claim of global unreachability is made for those modules. The new low-degree node no longer
needs a separate Picard-modulo-n argument: degree two is assembled in the main theorem from
the proper degree-coordinate node and existing affine vanishing.

Also removed unused public imports of `GmPicard` from the new low-degree module and `Gm` from
the new primitive-root-square module before delivery; their statements obtain the needed
objects from their remaining imports.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Two interfaces do not directly provide the detailed conclusion
required here. `kummer_base_change_compatibility` supplies a roots-of-unity ladder but does not
state its compatibility with the canonical constant-sheaf comparison and the chosen
primitive-root trivializations; the new sheaf-square node supplies exactly that missing step.
`sheafH_constantZMod_of_isProper` supplies abstract cohomology equivalences, so it cannot alone
supply H2 coordinates whose values on every line-bundle boundary are prescribed by degree;
the new proper-degree node records that normalized construction. Its compactification-genus
clause explicitly handles the chosen compactification rather than silently identifying it
with the proper source curve.

The blueprint proof is retained as a source, and the Lean reduction explicitly uses its
proper/affine cases. The unit record has empty `realized` lists in the repository; it was read
and left unchanged. Blueprint-wide searches found the original constant-invariance theorem,
primitive-root node, proper-cohomology node and degree-base-change node, but no existing
statement with the needed new detailed interfaces. LeanSearch was unavailable with an
Internal Server Error; this is recorded as unavailable, with actual LeanFinder, Loogle and
Mathlib source searches retained. There is no change record because existing statements,
definitions and public imports are unchanged.

## New nodes

`lem-sc-constant-low-degree-base-change`: source proper/affine computations in degrees zero
and one. It reduces those computations to the existing primitive-root, Kummer, Jacobian,
abelian-variety, units and Picard-torsion interfaces; it contains neither higher vanishing nor
any of the compatibility and coordinate clauses of the original theorem.

`lem-sc-root-trivialization-base-change`: the source's compatible primitive-root
trivialization sentence, stated as an equality of two sheaf morphisms for a Kummer-complex
map with the prescribed units component. Its proof is the power-map identity on generating
constant-presheaf sections followed by cancellation of the roots-of-unity kernel inclusion.

`lem-sc-constant-kummer-naturality`: a proved assembly of the inclusion and two boundary
identities from the preceding sheaf square and the existing Kummer ladder, using cohomology
functoriality, the Picard equivalence, degree-zero sections and `deltaSucc_zero`.

`lem-sc-constant-proper-degree-coordinates`: the proper Pic/n and degree computation,
including the chosen compactification's genus. Brauer vanishing makes the Kummer boundary
surjective, degree zero is n-divisible, a rational point supplies degree one, and preservation
of degree under extension proves compatibility on all cohomology classes.

## Second reading by C2

1. Compared every delivered module with the repository version. The existing target declaration
   is byte-for-byte unchanged; only its proof and private proof imports changed. Verdict: pass.
2. Compiled all five modules with `lcompile.py --all`. There are no forbidden declarations and no
   anonymous or definition-level `sorry`s. The three remaining `sorry`s are named split theorems
   listed above, each with a matching node and proof docstring. Verdict: pass.
3. Checked the split statements against their edge cases and searched the library for duplicates.
   The low-degree, root-trivialization, and proper-coordinate statements are strictly smaller
   than the target and are needed by the reduction; no false statement or duplicate was found.
   Verdict: pass.
4. The proof follows the base-change, proper/affine, Kummer, and cohomological-dimension route;
   all imports removed from the parent are recorded under `No longer needed`, and the remaining
   imported declarations are used. Verdict: pass.
5. The parent and new DAG nodes record the declarations, proof steps, dependencies, split status,
   and origins used by the Lean code. The unit route is retained; the repository unit has no
   realized entries to update. Verdict: pass.

Changed only the report in this second reading; no Lean statements, definitions, or DAG claims
were altered.
