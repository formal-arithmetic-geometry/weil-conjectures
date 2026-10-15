## What changed

Proved `CategoryTheory.locallyFree_derivedHom` by local dual-basis comparison, exact adjoints,
Mathlib's HomComplexSingle cohomology-class equivalence, localization into K-injectives, and the
existing constructed functorial K-injective resolution. The equivalence, its naturality in both
variables, and its evaluation normalization are constructed and proved in Lean. The construction
works for arbitrary complexes and is specialized to the unchanged bounded-below statement.

Used the existing private generic-site `SheafOfModules.dualTensorHom_comparison` through
`import all Sheaf.AlgebraicGeometry.DualTensorHomComparison`. Lean exposes that proved lemma to
this proof without changing the dependency module or any public interface. Its scheme
specialization alone was insufficient for an arbitrary ringed site.

Factored the global cohomology comparison through its generic natural transformation and used
the canonical closed-category evaluation and dual-map APIs. Equalities to the old defining
formulas are the existing source theorems `SheafOfModules.ihom_ev_app` and
`SheafOfModules.pre_app`. The resolution and naturality argument is proved for an abstract
abelian monoidal category in the same file, then specialized to sheaves through shared definitions. Cached aliases of the standard categorical
structures avoid expensive repeated inference. The specialization uses the concrete category directly
and unfolds the small wrappers before applying the cycle formula. Public target statements and
their mathematical meaning are unchanged.

Updated the existing DAG proof and proof dependencies to this route. This node is below the
blueprint unit level, and no unit realization or unit proof step is bypassed.

Change records:

- `coord/changes/c4-locally-free-comparison-api.md`

## Proved and sorry left

Closed the one original hole: `CategoryTheory.locallyFree_derivedHom`
(`lem-weil-pbc-ringed-site-locally-free-derived-hom`). No holes added and no `sorry` left in the
delivered Lean module. All intermediate constructions and their properties are proved.
This is a proof, not a decomposition. The complete proof compiled in 58.2 seconds.
The required delivery compile and axiom probes passed in `deliver3.py --no-push`.

## No longer needed

Removed imports:

- `Mathlib.Algebra.Category.Grp.EpiMono` (unused proof import from the earlier attempt)
- `Mathlib.CategoryTheory.Sites.LocallyBijective`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`
- `Sheaf.Algebra.Homology.HomComplex`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatCoefficientUniverse`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`

Removed proof dependencies (these obligations are no longer needed by this item):

- `def-pc-kflat-complex`
- `def-pur-hom-complex`
- `lem-galois-set-sheaf-local-bijection-isomorphism`
- `lem-pur-hom-kflat-into-kinjective`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sc-bounded-below-injective-resolution`
- `lem-sc-finite-free-internal-hom-exact`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-kinjective-shift`
- `lem-weil-pbc-ringed-site-module-sheafification-exact`

The corresponding staged K-flat, sheaf Hom-complex, slice-exactness and bounded-below resolution
modules are not imported. Local bijectivity, localization and K-injective comparison are supplied
directly by the existing source/Mathlib APIs. No claim is made that another target cannot still
reach these nodes through a different route.

## Where the brief, the DAG or earlier work was wrong

The planned K-flat/sheaf-Hom-complex and repeated bounded-below injective-resolution route is
unnecessary. Finite locally free duality makes the relevant functors exact as adjoints, and the
existing functorial unbounded K-injective resolution supplies naturality directly. No false
statement or change of hypotheses was needed. Rank zero and varying local ranks are handled by
the existing finite free local-generator calculation.

The earlier attempt had no proof holes but exceeded the compilation limit. Its completion claim
was premature. The repair retains its mathematical argument while abstracting the expensive
homological constructions and replacing repeated definitional reductions with explicit API lemmas.

The generic-site dual-tensor comparison existed privately. `import all` reuses it without an
export change and avoids specializing an arbitrary ringed site to the public scheme theorem.

## Second reading by C4

1. Compared the complete delivered module with the repository version. All seven existing
   declaration signatures are byte for byte identical, including the bounded-below hypothesis,
   contravariance in P, covariance in K, additive equivalence, and cycle normalization of
   `CategoryTheory.locallyFree_derivedHom`. The six changed definition bodies are explicitly
   recorded in `coord/changes/c4-locally-free-comparison-api.md`. The cached structures are
   transparent aliases with local attributes. The dual tensor and sections objects are the
   original objects; `SheafOfModules.pre_app` identifies the new dual-map formula with the old
   one, and `SheafOfModules.ihom_ev_app` identifies evaluation. The global comparison expands
   to the original natural-transformation formula. No other library module is delivered.
   A scratch module also proves equalities of all six old and new definition bodies:
   four by reflexivity, the dual map by `SheafOfModules.pre_app` and reflexivity, and
   evaluation by `SheafOfModules.ihom_ev_app` and reflexivity. This compiled cleanly.
   Verdict: no accidental statement or semantic change.
2. Read the entire proof, including the abstract model, the single-complex Hom equivalence,
   its cycle formula, K-injective localization, and transport along the constructed functorial
   resolution. The module compiles cleanly through `lcompile.py` (59.3 seconds in this reading).
   There is no `sorry` or prohibited declaration/attribute in its source. Every equivalence
   is constructed from explicit functors and isomorphisms; the resolution is the existing
   small-object-argument construction, not an arbitrary witness extracted from a holed
   existence theorem. The delivery tool additionally probes the axioms of every declaration.
   An explicit `#print axioms CategoryTheory.locallyFree_derivedHom` in the scratch module
   reports exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
   Verdict: the original hole is closed by a proof, with no lower holes added.
3. There are no split-off statements or new nodes to review. Checked rank zero, varying local
   ranks, the zero complex, and unbounded complexes: finite local generators allow empty and
   varying bases, the local bijectivity argument remains valid, and the homological proof
   works without boundedness before specialization. The pairing equivalence follows from
   the closed-category comparison, rather than assuming an equivalence with the desired
   conclusion. Verdict: no decomposition or relabelled obligation.
4. Checked the shorter-route question against the existing sheaf dual-tensor comparison,
   finite-free dual-basis theorem, Mathlib HomComplexSingle and K-injective localization,
   and the source right-derived-functor comparison API. These are used directly. The proof
   avoids the former K-flat and bounded-below replacement route. Compared both node versions:
   all ten removed proof dependencies occur under `No longer needed` above. Opened
   `dag/units/sk-thm-properbasechange.json`; this item realizes neither its statement nor a
   specified step, and its three unit steps and realization records are preserved.
   Also compiled the unchanged direct importer
   `Sheaf.Paper.CondensedLocalPieceHomContinuity` against the scratch overlay of the new
   module (8.2 seconds), checking removal of the public K-flat import against its user.
   Verdict: the unit route is kept and pruning is recorded completely.
5. Compared the DAG proof with the Lean argument step by step: local dual-basis bijectivity
   and the generic-site comparison; exact adjoints and dual/bidual transport; single-Hom
   cohomology classes; K-injective localization and the sections comparison; functorial
   resolution and its tensor naturality square. The new proof dependencies are precisely
   the retained definitions, generic comparison, and functorial resolution. Only `lean`,
   `proof`, `proof_deps`, and `proof_origin` differ in the existing node. No unit, source,
   statement, or statement dependency is changed. Verdict: the node agrees with the proof.

The second reading made the proof-only helper `locallyFreeDerivedComparison_isIso` private
and removed it from the node's public declaration list. Its proof is unchanged and only a
private theorem uses it. It also added this independent review and expanded the change record
to list all 15 transitive importers and their holders.
The first dry run compiled with the all-declaration axiom probe and reached preflight; its
sole failure was that it had read the report before this second-reading section was added.
After the visibility repair, `deliver3.py --no-push` printed OK for commit `ff0ce6afcd`,
including compilation, the all-declaration axiom probe, and preflight.
