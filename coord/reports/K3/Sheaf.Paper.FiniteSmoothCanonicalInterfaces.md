## What changed

Proved `AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison_existsUnique`.
The existence proof constructs affine Rees/associated-graded ring isomorphisms with
all homogeneous representative formulas, proves their naturality, descends them along
the ambient affine basis, and applies the affine-morphism/relative-Spec
anti-equivalence. It verifies projection and augmentation compatibility. Uniqueness
uses the proved degree-one algebra and scheme-morphism detection theorems.

Moved the three normalization definitions verbatim into
`Sheaf.AlgebraicGeometry.ReesConeNormalization`, below the existence and uniqueness
modules, to avoid an import cycle. The assigned module publicly re-exports them.
All six original signatures and all five original definition/abbreviation bodies
match current sources. No target statement changes. All seven delivered Lean files
are module files with lines of at most 100 characters.

The relative-Spec augmentation calculation uses private transport and counit
cancellation helpers. Private equations for the chosen functor's objects and section
maps normalize the anti-equivalence explicitly, avoiding repeated expansion of its
existential specification. The generic calculation assumes an arbitrary subcategory
predicate and uses the exact section-map formula. The final public specialization
simplifies the identity base map explicitly. The complete zero-section file compiles
without warnings in 5.4 seconds under the unchanged 60-second limit.

## Proved and sorry left

Original hole closed:
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison_existsUnique`
  (`def-pur-finite-smooth-canonical-interfaces`).

Additional proved public theorems:
- `AlgebraicGeometry.ConormalGradedAlgebra.hom_ext_degree_one`
  (`lem-pur-conormal-graded-algebra-hom-ext`).
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.conormalCone_hom_ext`
  (`lem-pur-conormal-cone-hom-ext`).
- `Ideal.rees_associatedGraded_chart` (`lem-pur-rees-associated-graded-chart`).
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison_exists`
  (`lem-pur-rees-cone-normalized-existence`).
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.coneZeroSection_app`
  (`lem-pur-conormal-zero-section-pullback`).

Actual textual counts: one original hole closed, zero holes added, zero `sorry`s in
all seven delivered Lean files. No result is delegated to an unproved new statement.
The unchanged direct importer `Sheaf.Paper.FiniteSmoothPurityMaps` compiled against
the retained overlay without warnings in 6.5 seconds. Full delivery checks are run
through the required `deliver3.py` workflow.

## No longer needed

No pre-existing proof dependency or public import is removed. No whole module is
pruned. Removed redundant `VectorBundleZeroSection` and `AffineMorphismRelativeSpec`
import lines from the new `ConormalConeHomExt` and `ReesConeNormalizedExistence`
modules; retained dependencies publicly import the declarations they need.

No regularity, finite generation, smoothness, or bundle-frame lemma is needed. The
existing `purityNormalCone_comparison` is not a proof input: its statement does not
specify the homogeneous representative formula required here. No unit realization
or prescribed unit-level proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node had no numbered proof or proof dependencies, contrary to the
generic brief; its Lean docstring supplies the homogeneous representative argument.
The node copy now records the actual proof and its dependencies.

The retained work included complete algebraic and descent constructions but also
left diagnostic heartbeat settings in the augmentation proof. Resumption checked the
interrupted dry-run result before mutation: it had reported success at 82ea55c4a2,
without pushing. Fresh compilation exposed the diagnostic cap and expensive matching
of the chosen equivalence. Raising the cap alone did not fix the file-time failure.
The private functor equations, generic transport calculation and explicit final
simplification repair that performance problem without changing any definition or
statement, splitting the file, or raising the 60-second file limit.

Empty schemes, zero ideals and unit ideals are included: the affine chart theorem
uses no regularity hypothesis, the uniqueness argument uses ideal-product induction,
and the zero-section calculation is functorial augmentation compatibility.

The three downstream scans were repeated against current sources and each reports
27 consumers. Only the assigned module directly uses the relocated names; the public
re-export preserves every consumer's interface, so none requires adaptation. No
launcher or repository tool was edited or bypassed.

## New nodes

`lem-pur-conormal-graded-algebra-hom-ext`: proved degree-one algebra uniqueness for
the conormal presentation and arbitrary target algebra sheaf, using ideal-product and
direct-sum induction.

`lem-pur-conormal-cone-hom-ext`: proved scheme-morphism detection for any affine
realization of the conormal algebra and any source scheme, by algebra uniqueness
and affine restrictions.

`lem-pur-rees-associated-graded-chart`: proved the affine ring isomorphism and all
homogeneous representative formulas, using quotient lifting, algebra-adjoin
induction, and Laurent-coefficient injectivity.

`lem-pur-rees-cone-normalized-existence`: proved normalized comparison existence by
chart naturality, sheaf descent, the anti-equivalence, and augmentation compatibility;
its statement asserts no uniqueness.

`lem-pur-conormal-zero-section-pullback`: proved section-map compatibility of the
relative-Spec zero section with its defining augmentation.

`def-pur-rees-cone-normalization`: records the verbatim relocation of the three
normalization definitions.

Change record: `coord/changes/K3-rees-cone-normalization-location.md`.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
