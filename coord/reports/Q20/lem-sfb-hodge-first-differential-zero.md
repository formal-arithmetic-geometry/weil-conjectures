## Worker report

The module `Sheaf.AlgebraicGeometry.HodgeFirstDifferentialZero` states
`AlgebraicGeometry.hodge_first_differential_zero`. Its proof is `sorry`.
It also supplies the two canonical-map helpers belonging to this node:
`Scheme.Modules.fieldLinearUniversalDifferential` and
`Scheme.Modules.fieldLinearUniversalDifferentialCohomology`. Both contain real
construction data, with no choice of an arbitrary map and no postponed proof.
The first bundles the already defined relative universal derivation, using its
additivity, Leibniz rule, vanishing on base scalars and restriction compatibility.
The second is postcomposition on vector-sheaf Ext, conjugated by the existing
canonical scalar cohomology comparison. This defines precisely the map in the
node, on the existing ordinary module cohomology groups.

Clause-by-clause correspondence:

- A field F of characteristic zero: `(F : Type u) [Field F] [CharZero F]`.
- A scheme W over F: `(W : Scheme.{u})` and
  `(f : W ⟶ Spec (CommRingCat.of F))`. The explicit structure map is accepted
  because the recorded differential and scalar comparison declarations take f.
- Smooth and projective over F: `[Smooth f] [IsProjective f]`, using the
  recorded smoothness and H-projective-plus-quasi-compact projectivity notions.
- No connectedness or geometric integrality: neither appears in the signature.
- The sheaf obtained by gluing affine Kähler differentials:
  `f.relativeDifferentials`, the existing scheme construction. Its affine
  comparison and restriction isomorphisms identify it with the gluing in the node.
- The universal F-linear derivation: `fieldLinearUniversalDifferential f`,
  whose section map is literally `f.relativeDifferentialsDerivation.d`.
  Its source is `scalarSheaf f (SheafOfModules.unit W.ringCatSheaf)` and its
  target is `scalarSheaf f f.relativeDifferentials`.
- Every q ≥ 0: `(q : ℕ)`, including q = 0.
- H^q(W,d) is zero: `fieldLinearUniversalDifferentialCohomology f q = 0`
  as an additive homomorphism between `scalarCohomology` groups.
- Formed in Zariski sheaves of F-vector spaces: the first helper is a morphism
  in `KSheaf W F`, namely `Sheaf (Opens.grothendieckTopology W) (ModuleCat F)`.
  The induced map uses `Abelian.Ext.mk₀` and `postcomp` in that category.
- Canonical agreement with ordinary module cohomology: conjugation by
  `scalarCohomologyExtEquiv` makes source and target the already recorded
  `RingedSpace.moduleCohomology` groups with restricted F scalars.
- d is not regarded as O-linear: there is no morphism of O-modules for d;
  only a morphism between the scalar vector sheaves.
- No embedding F → C: no such datum or typeclass is required.

Dependencies read and used:
`Field` (Mathlib.Algebra.Field.Defs);
`AlgebraicGeometry.Scheme` and its morphisms (Mathlib.AlgebraicGeometry.Scheme);
`AlgebraicGeometry.Smooth` (Mathlib.AlgebraicGeometry.Morphisms.Smooth);
`AlgebraicGeometry.IsProjective` (WeilConjectures.AlgebraicGeometry.Morphisms.Projective);
`KaehlerDifferential`, `KaehlerDifferential.D`, and
`KaehlerDifferential.linearMapEquivDerivation` (Mathlib.RingTheory.Kaehler.Basic),
used through the existing relative differential construction;
`AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`
(WeilConjectures.AlgebraicGeometry.PQFCohomology), with its underlying
`RingedSpace.moduleCohomology` definition;
`Scheme.Hom.relativeDifferentials` and `relativeDifferentialsDerivation`
(WeilConjectures.AlgebraicGeometry.Modules.Differentials);
`Scheme.Modules.scalarMap`, `scalarObj`, `scalarSheaf`, `KSheaf`,
`scalarCohomology`, and `scalarCohomologyExtEquiv`
(WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations).
The last two existing definition nodes were added to stmt_deps to make these
already recorded notions explicit. No dependency record was replaced.
The four new stage-1 proof inputs have no recorded Lean modules, so no imports
for those are yet available. Their full assembly is in the theorem docstring.

Edge cases checked before writing: W empty (no Nonempty assumption and the
unit sheaf is still the structure sheaf); finitely many disconnected components
of unequal dimensions (no dimension, integral, irreducible or connected
hypothesis); q=0 (global regular functions are locally constant over a finite
separable algebra in characteristic zero); positive degrees, including beyond
dimension; zero-dimensional smooth projective schemes; P¹ and elliptic curves;
fields with transcendence degree too large to embed in C. The last case is why
the proof descends to an embeddable field of definition and then uses two
scalar-extension squares. There is no statement correction or disputed claim.
The shared universe is the project scheme-over-field convention, not an
extra smallness condition: any field and scheme can be placed in a common
universe by lifting.

Source reading: opened Popa's author PDF
https://people.math.harvard.edu/~mpopa/271/Kodaira-posted.pdf and read the proof
of Theorem 1.6.6 on printed pp.26–27 (PDF pp.29–30). It treats the exterior
derivative as a C-linear sheaf map and obtains zero by harmonic representatives.
Read Stacks `cohomology.tex`, `lemma-modules-abelian` (Tag 01F1), which compares
module and abelian-sheaf cohomology via the same injective resolution. The
node's accepted proof expands Popa's characteristic-zero field descent and
retains disconnected and empty schemes. No source claim was changed.

Searches for existing statements and constructions:

- LeanFinder query “The universal derivation induces zero on structure sheaf
  cohomology of smooth projective schemes over a characteristic zero field”:
  8 hits, on affine cotangent/formal smoothness results; none is this theorem.
- Loogle query `KaehlerDifferential, sheafCohomology`: no hits (the latter is
  not an indexed identifier).
- Loogle query `"KaehlerDifferential"`: 12 hits, including the recorded
  affine differential module and universal derivation; none is the sheaf-cohomology
  vanishing theorem or its scalar-sheaf arrow.
- LeanSearch query “Hodge differential zero on coherent cohomology of smooth
  projective scheme characteristic zero”: 8 hits on cotangent modules and
  differential-zero identities for cochain complexes; no matching theorem.
- msearch grep `Hodge|deRham|universalDerivation|kaehlerSheaf`: 7 hits about
  period rings and a bibliographic Hodges mention; no matching theorem.
- LeanFinder query “Universal derivation as a linear morphism of sheaves of
  vector spaces on a scheme over a field”: 8 presheaf differential/universal
  derivation hits. They are the underlying machinery, not the bundled vector
  sheaf arrow constructed here.
- LeanSearch query “Universal derivation of scheme as field linear sheaf
  morphism”: 8 hits on presheaf differential universality and
  `Derivation.hasCoeToLinearMap`; no existing scheme scalar arrow.
- msearch grep `relativeDifferentialsDerivation|scalarDifferential` under
  AlgebraicGeometry: no Mathlib hits.
- rg of project `lean/WeilConjectures` and `lean/Sheaf` for Kähler, Hodge,
  derivation, relative differentials and scalar cohomology found the two
  existing scheme constructions and comparison APIs above; no duplicate
  theorem or canonical field-linear derivative arrow. rg of the item id in
  `lean/WeilConjectures` found no match. The upstream name index had no Hodge
  differential/cohomology derivative match.
- DAG searches found `def-sc-relative-differential-sheaf` and
  `def-sc-field-linear-module-cohomology-operations`, reused directly.
  `tools/blueprint_refs.py search 'derivation cohomology'` found zero matches.
  The helper arrow is part of the owning node's notion, so no independent
  definition node is introduced.

Validation: all compilation is through the authorized server scompile wrapper;
no local Lean compiler, global build, shared-repository write or direct Git
command was used. The delivery dry run and push are performed by deliver2.py.

## Second reading by Q20

This is a second pass by the same dispatcher-started worker, not an independent
agent review: the assignment explicitly forbids starting other agents and
reserves the independent review to the maintainer. I reopened the node and the
complete module and checked the following correspondence again.

The field has exactly Field and CharZero, W has exactly a structure map,
smoothness and the recorded projectivity class, and q ranges over all naturals.
No connectedness, integrality or complex embedding occurs. The target is
exactly the zero additive homomorphism on the canonical ordinary module
cohomology carriers. The source module in that expression is the unit
O-module and the target is the existing relative differential module. The
helper sheaf arrow has precisely the existing universal derivation as each
component; its scalar-linearity uses that base scalars have zero differential,
not a hypothesis that the derivation is O-linear. Its naturality is precisely
the existing derivation restriction law. Its induced arrow uses the constant
field unit as the Ext source in vector sheaves and canonical comparison at
both ends, hence does not confuse O-linear and F-linear cohomology maps.

I checked every docstring against its owning node id and the four accepted
proof steps. The two helpers are constructions within this node, with real
data and no extra theorems. No definition node or dependency replacement was
needed. The two added statement dependencies already carry landed declarations.
The old module split into a separate helper file was consolidated into this
single owning-node module before delivery. Scalar carrier annotations and
direct equalities were made explicit in response to compiler diagnostics;
these did not change any mathematical hypothesis or clause. No mathematical
mismatch with the node was found in this second pass.

Final validation: scompile compiled both the isolated sandbox and final library
module without errors or warnings (about 20–23 seconds per invocation). The
first delivery preflight caught the assignment delimiter in lean.statement;
the record was repaired to use exactly the signature before `:=`.
