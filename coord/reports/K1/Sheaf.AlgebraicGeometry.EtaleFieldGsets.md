## What changed

Replaced the sole sorry in `AlgebraicGeometry.etaleFieldGsets` by a compiling reduction.
The concrete geometric-point action and functor are actual definitions: the action is
precomposition by `Spec g`, and maps act by postcomposition. The unit, multiplication,
equivariance, identity and composition laws are proved. Continuity is proved from a finite-type
affine neighborhood: the stabilizer is a finite intersection of open Krull stabilizers of
images of algebra generators. The original two forgetful instances are unchanged; the new
modules use local, definitionally equal discrete forgetful instances.

Full faithfulness and essential surjectivity are isolated in two separate new theorem modules.
Their instances construct `F.asEquivalence`. The original geometric-point identifications,
naturality and action clause then hold definitionally. The entire covering clause is proved
using Mathlib's lifting over separably closed fields and its surjectivity theorem for the
geometric-point-to-underlying-point map. No statement or target signature was changed.

All four modules compile locally, without warnings. The delivery dry run checks the set,
axioms and server compilation. Sources read: Stacks [03QR](https://stacks.math.columbia.edu/tag/03QR),
[03QS](https://stacks.math.columbia.edu/tag/03QS), and
[02GL](https://stacks.math.columbia.edu/tag/02GL), alongside the Mathlib source.

## Proved and sorry left

Decomposed, not proved outright: `AlgebraicGeometry.etaleFieldGsets` (node `lem-exc-etale-field-gsets`).
Its covering, naturality and action clauses contain no deferred steps.

Proved outright: `AlgebraicGeometry.etaleFieldGeometricAction_continuous`
(node `lem-exc-etale-field-geometric-action-continuous`), including the private proved
`finiteType_embedding_stabilizer_open` helper. No sorry remains in the action module or in
any definition.

Hole accounting: closed the original hole `AlgebraicGeometry.etaleFieldGsets`; added the
two holes below. Thus this is one decomposition, zero of the one original declarations
proved outright, and a net increase of one hole, not positive ledger progress. The new
continuity theorem is proved outright but did not close an existing hole.

Every sorry left by this delivery:

- `AlgebraicGeometry.etaleFieldPointFunctor_fullyFaithful`, in
  `Sheaf.AlgebraicGeometry.EtaleFieldPointFunctor`, node
  `lem-exc-etale-field-point-functor-fully-faithful`.
- `AlgebraicGeometry.etaleFieldPointFunctor_essSurj`, in
  `Sheaf.AlgebraicGeometry.EtaleFieldPointFunctorEssSurj`, node
  `lem-exc-etale-field-point-functor-ess-surj`.

Each is a strict part of the argument, has a complete proof in words and its own DAG node,
and has proof exactly `by sorry`. The full-faithfulness statement concerns the explicitly
constructed functor, and the essential-surjectivity statement is independently the orbit
construction. Neither restates the original theorem or its covering clause. Edge cases
checked: empty source, empty target, empty G-set, empty covering family, trivial Galois group,
and arbitrary universe of family indices. The quotient orbit index set and fixed fields
stay in universe u.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields`;
- `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`;
- `Sheaf.FieldTheory.EtaleFieldGaloisClassification`;
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`.

These modules' results remain in the plans and proof imports of the two categorical gaps: they are not claimed
to be globally pruned. Their corresponding nodes
`lem-exc-etale-coproduct-etale`, `lem-weil-pbc-etale-fibre-discrete-separable-points`,
`lem-exc-etale-field-galois-classification`, and
`lem-weil-pbc-finite-separable-extension-etale` are therefore still needed below those gaps.
The original node now depends directly on the three new nodes and the small-etale-site node.

The fibre decomposition and finite-field classification are no longer needed for continuity
or for either direction of the covering criterion. The covering proof uses the already
proved Mathlib theorems `Scheme.exists_fac_of_etale_of_isSepClosed` and
`Scheme.pointSmallEtaleFiberObjToPreimage_surjective`. The new continuity module needs only
Mathlib; a trial import of `Mathlib.AlgebraicGeometry.Sites.EtalePoint` there was removed.
No unit statement or realized step was bypassed: `sk-prop-h2.realized` does not list this node
or any of these dependencies as a fixed step, and the categorical gaps preserve the original
finite-spectrum and orbit construction route. No module is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original DAG's covering proof routes through finite-spectrum transitivity. Mathlib now
already proves lifting for separably closed fields (not just algebraically closed fields),
so that route is unnecessary here. `IsSepClosure.sep_closed K` must be installed locally;
it is not a global typeclass instance. Likewise continuity does not need the entire
finite-separable-spectrum decomposition: local finite type suffices.

LeanSearch returned Internal Server Error and is recorded as unavailable, without a verdict.
LeanFinder, Loogle and local source searches were available. The literature source path from
the DAG is absent on this machine; the cited Stacks tags were read on the official website.
No tool or process failure blocked the work.

## New nodes

`lem-exc-etale-field-geometric-action-continuous` records the explicit action and its proved
continuity, in `lean/Sheaf/AlgebraicGeometry/EtaleFieldGeometricAction.lean`. Its proof uses
only Mathlib and the affine finite-type argument.

`lem-exc-etale-field-point-functor-fully-faithful` records the remaining full-faithfulness
argument for the explicit functor, in `lean/Sheaf/AlgebraicGeometry/EtaleFieldPointFunctor.lean`.
Its plan reuses the existing fibre decomposition and finite Galois classification.

`lem-exc-etale-field-point-functor-ess-surj` records the remaining orbit-realization argument,
in `lean/Sheaf/AlgebraicGeometry/EtaleFieldPointFunctorEssSurj.lean`. Its plan reuses the
existing finite Galois classification, finite-separable-etale theorem and coproduct theorem.

All three nodes are under `dag/nodes/sec-curve-estimates/`; the original node's proof,
proof dependencies and proof origin were updated. No change record is necessary: existing
statements, definitions, instances and public imports are unchanged.


## Second reading by K1

1. Compared the entire original module against the repository using `diff -u`.
   Its two instance definitions, theorem signature (including both universes and all
   three clauses), public imports and existing docstrings are byte-for-byte unchanged.
   Only proof imports and the proof body changed. The other three modules are new.
   No target statement or existing definition changed; no change record is required.

2. Read all four modules, including the finite-generator stabilizer helper and the
   affine-open factorization. Recompiled the set in import order without errors or
   warnings. The only two sorries are the named full-faithfulness and essential-
   surjectivity theorems listed above; neither is hidden inside a definition. No forbidden
   declarations or attributes occur. A scratch `#print axioms` check covers the base
   point, its automorphisms, the action, continuity, the point object, the functor and
   all three categorical theorems. Continuity and the concrete definitions use only
   the allowed axioms; the two gaps and the original reduction additionally use sorryAx.
   In particular the original theorem is not an axiom-free completed proof.

3. Read Stacks Tags 03QR (lemma-sheaves-point), 03QS and Morphisms 02GL on the official
   website, and the signatures of `etale_fibre_discrete_separable_points`,
   `finite_separable_extension_galois_classification`,
   `etale_sigmaDesc_spec_of_finite_separable`, and `of_finite_of_isSeparable`.
   Full faithfulness uses precisely the decomposition and the finite-spectrum
   Hom-bijection, assembling component maps by the coproduct property. Essential
   surjectivity uses the finite transitive orbit clause and the etale coproduct result.
   Both gaps are true, independent proper parts of the equivalence argument; neither
   repeats the equivalence together with its point identifications and covering clause.
   Checked empty schemes/sets, trivial absolute Galois group, nonempty transitive
   orbits, and arbitrary disjoint unions. Orbit quotients and fixed subfields fit
   universe u; covering indices remain in arbitrary universe w. Independently ran
   LeanFinder on equivariant maps determining morphisms of etale schemes, Loogle on
   `CategoryTheory.Functor.EssSurj`, msearch grep and `rg` in the library, upstream
   geometry and Mathlib. The hits provide general categorical machinery and finite
   etale/fundamental-group results, not either exact arbitrary-etale statement.
   Neither gap has a short proof from the currently available interfaces.

4. The concrete action has the correct left multiplication order because Spec is
   contravariant. Continuity reduces to finitely many algebra-generator images with
   open Krull stabilizers. The covering proof directly applies Mathlib's separably
   closed lifting and geometric-fiber surjectivity, with the singleton Spec K base;
   it does not require the deferred categorical results except to package the functor
   as an equivalence. Read `sk-prop-h2.realized`: it fixes no step using these removed
   direct imports. All four old dependency nodes are listed above and remain needed
   below the two gaps. Restored their proof imports there, so this delivery does not
   accidentally prune unresolved prerequisites. Removed the redundant public import
   `Mathlib.CategoryTheory.Equivalence` from the new point-functor module; the full set
   still compiles. Existing public imports are preserved.

5. Read all four delivered node records against their Lean declarations. The original
   node's three steps construct the action, assemble the equivalence from the two
   categorical properties, and prove covers by the cited site criterion and Mathlib
   lifting. The continuity node's steps match the implemented affine argument. The
   two open nodes cite exactly the decomposition/classification/coproduct facts their
   docstring proofs require; their proof_deps are the unions of step citations. New
   nodes contain source, blueprint provenance, searches, created metadata and Lean
   records. The original statement and statement dependencies are unchanged.

Changes by the second reader: restored proof-dependency imports in the two gap modules,
removed the redundant new public Equivalence import, and corrected the report's hole
accounting to distinguish decomposition from an outright proof. No Lean proof body or
statement needed repair. No module is claimed globally pruned.
