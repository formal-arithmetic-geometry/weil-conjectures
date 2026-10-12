## What changed

Kept the signature and docstring of `Algebra.popescu_lifting` unchanged. Its proof now
chooses prepared finite polynomial data, constructs the specified quotient, proves its
finite presentation, constructs the complete commutative diagram, and applies the
smoothness theorem for that same quotient. No existing definition or statement changed,
and no adaptation or change record is required.

Added `Sheaf.RingTheory.PopescuLiftPresentation`: real finite polynomial data, the
`Prepared` predicate, and the explicit algebra
`ULift (R[x,z] / (f_l - π z_l, p_{kl}))`. No definition chooses a witness of an unproved
existence theorem. The data is obtained by existential elimination in the target proof;
the quotient is then constructed from those data. Its finite-presentation theorem is
fully proved from Mathlib.

Added `Sheaf.RingTheory.PopescuLiftMaps`, with a complete Lean proof of
`Algebra.exists_popescu_lift_maps`. Lift the original generator images to Λ, write
evaluated relations as π²μ, and evaluate z as πμ. The annihilator equality kills the
additional p equations. Quotient universal properties construct φ, ψ, red, c and cmod.
Surjectivity of the presentation map and equality on polynomial generators prove the
commuting square. This theorem has no `sorry` and uses no unfinished theorem.

Added `Sheaf.RingTheory.PopescuLiftSmooth`: smoothness is asserted only for the explicit
quotient, under the cover, conormal basis, differential basis, cleared relation,
normalization, generator-map and quotient-map hypotheses. It never asserts smoothness
for an arbitrary D, c or cmod.

All four modules compile through lcompile.py. Explicit `#print axioms` checks for
the maps theorem and the finite-presentation theorem list only `propext`,
`Classical.choice` and `Quot.sound`. The unit route is retained: this is the
same Tag 07CP argument below unit level, grouped into preparation, maps and smoothness.

## Proved and sorry left

Closed the sole original hole, `Algebra.popescu_lifting`, by a compiling reduction.
The target still depends on two unfinished steps; this is a decomposition, not a
sorry-free proof of Popescu lifting. Holes closed: 1; holes added: 2; net: -1.

Fully proved `Algebra.PopescuLiftPresentation.finitePresentation` and
`Algebra.exists_popescu_lift_maps`. The latter uses the Prepared hypotheses, not
`Algebra.exists_popescu_lift_preparation` or any other unproved theorem.

Exactly two declarations retain `sorry`, each in its own new module and with proof
exactly `:= by sorry`:

- `Algebra.exists_popescu_lift_preparation`:
  `lem-weil-pbc-popescu-lift-preparation`, original plan steps 1--4. No Λ or lifting
  algebra appears in its conclusion: it prepares finite relations and smooth charts.
- `Algebra.popescu_lift_smooth`:
  `lem-weil-pbc-popescu-lift-smooth`, original plan steps 8--18. The quotient is fixed
  explicitly, all presentation/chart hypotheses are supplied, and no existence of
  lifting maps or diagram is asserted.

No sorry remains in the item's module, the maps module, a definition, or a private helper.

## No longer needed

Removed these direct proof-only imports from the upper module:

- `Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`
- `Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`
- `Sheaf.RingTheory.EquationCountFibreDimensionFlat`
- `Sheaf.RingTheory.ExistsAnnihilatorOfSubsingletonLocalizedModule`
- `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`
- `Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension`
- `Sheaf.RingTheory.SmoothAtPrimeFreeConormalBasis`

These are relocated to the two unfinished step modules, whose recorded proof plans
still need them. They are not claimed as pruned from the transitive target closure.
No original node or module is made unnecessary by this route; pruned modules: none.
The old unlanded Core, SmoothOver and ModPi files and their three invalid sandbox nodes
were removed from the candidate delivery; they are not library pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stated smoothness for arbitrary algebras and maps, without recording
the construction hypotheses. The earlier second reader's π=0, R=Z, Cbar=R, D=R/(2)
counterexample is valid for those statements. Merely adding finite presentation would
not repair them. Those statements are replaced entirely by a lemma for the explicit
quotient and the actual conormal/chart hypotheses of Tag 07CP.

Checked edge cases of the new split: for π=0 the quotient has the f and linear p
relations, and smoothness is justified only on the prepared charts; arbitrary singular
quotients cannot be substituted. For π a unit, the quotient eliminates every z and is
a polynomial algebra, while the special-fibre clauses have no primes. For an empty
chart family the cover hypothesis forces the smooth locus to be empty, so the two
conditional special-fibre assertions are vacuous. For m=0 the quotient is the original
polynomial ring and the conormal basis is empty. These cases require no extra
nonzero, domain, nontriviality, or chart-nonemptiness hypothesis.

The original 18-step plan is valid and is kept. Its correction of the Nakayama shrink
to a(a^N+b), rather than ab with b in I, is retained in the preparation docstring.
The cited local Stacks TeX is absent on this machine, so Tag 07CP was read directly
on the official Stacks site and compared with the full existing DAG proof.
LeanSearch returned an internal-server error; this is recorded as unavailable without
claiming a negative search result. LeanFinder/Loogle and source grep supplied the
other searches. No tool failure prevents delivery.

## New nodes

`lem-weil-pbc-popescu-lift-preparation`: the finite polynomial preparation, including
the precise conormal/differential bases and the normalized cleared relations; its
complete source proof is the original steps 1--4, and its declaration remains sorry.

`lem-weil-pbc-popescu-lift-maps`: the compatible diagram maps for the explicit quotient,
with the generator equation needed later. This statement is fully proved in Lean,
including evaluation, annihilator cancellation and quotient factorization.

`lem-weil-pbc-popescu-lift-smooth`: the three smoothness properties of that fixed quotient,
under all the actual construction hypotheses; its complete source proof is the
original steps 8--18, and its declaration remains sorry.

The original node's proof, proof_deps and proof_origin now follow the compiling Lean
composition. All statement fields, target signatures, chapter records and unit records
are unchanged. No change record or forced adaptation is included.

## Second reading by T2

1. **Visible declarations.** Compared every delivered module with the repository version. The
   existing `Algebra.popescu_lifting` signature and docstring are byte-for-byte unchanged;
   all other declarations are new modules recorded by nodes, with no accidental edits.

2. **Compilation and axioms.** Compiled all four modules with `lcompile.py --all`; they compile
   without errors or warnings. The two completed theorems (`finitePresentation` and
   `exists_popescu_lift_maps`) use only the permitted axioms. The only remaining `sorry`s are
   the two named split theorems, each exactly `:= by sorry`; no definition or private helper
   contains a hole.

3. **Statements and split nodes.** Checked the preparation, maps, and smoothness statements
   against Tag 07CP and their edge cases. The maps theorem is a genuine construction for the
   explicit quotient; the two remaining split statements are strictly lower-level reductions,
   with complete source proofs in their docstrings and matching DAG nodes. No duplicate library
   theorem was found by source search.

4. **Pruning and route.** The upper module now imports only the map and smoothness modules plus
   its public prerequisites. The seven former direct proof-only imports remain where the two
   open split modules need them. The unit route and `realized` records are unchanged; no node
   or module became unreachable.

5. **DAG agreement.** Verified that each node's Lean declaration, proof steps, dependencies,
   source, and status match the delivered code. The target node records the explicit preparation,
   maps, finite-presentation, and smoothness composition. Verdict: the proof and split statements
   are unchanged in meaning and the delivery is ready for stage-3 checks.

Changed only this report section during second reading; no Lean code or DAG statement required
repair.
