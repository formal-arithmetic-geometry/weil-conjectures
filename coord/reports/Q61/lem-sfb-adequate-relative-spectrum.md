## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateRelativeSpectrum` states
`CategoryTheory.adequate_relative_spectrum`, with exactly one postponed theorem.
It constructs the relative-spectrum functor of points, rather than assuming a
map between arbitrary stacks. All helper declarations belong to the item's
explicit description of relative spectra and direct image; they are listed in
`lean.declarations`. There are no new independent definition nodes.

Hypotheses and clauses, in statement order:

- The field is `{k : Type u} [Field k]`, with base `Spec (CommRingCat.of k)`.
- The stack is `F : BasedCategory.{v, w} (Over ...)`, with
  `hF : IsAlgebraicModuliStack F`. This preserves the total fibred groupoid and
  automorphisms, rather than passing to isomorphism classes.
- The algebraic space is `Y : AlgebraicSpace (Spec (CommRingCat.of k))`.
- The map is `φ : BasedFunctor F (discreteModuli Y.obj.obj)` and its adequacy is
  the recorded `hφ : IsAdequateModuliSpace F hF Y φ`. That predicate includes
  qcqs, the canonical structure-sheaf isomorphism, and the local power-lifting
  test for all algebras on the actual affine étale 2-base changes.
- The commutative algebra is `B : ModuliAlgebraSheaf F hF.1.1`, with precisely
  `hB : IsQuasicoherentModuliAlgebra B` and no finite-generation, flatness or
  reducedness restriction.
- The explicit common ambient-universe correction is
  `hsmall : ∀ x : F.obj, Small.{u} (B.right.obj.obj (op x))`.
  The site universes `v` and `w` remain independent of `u`. It does not identify
  those universes, nor force compatible-family rings into the smaller universe.
- A `ModuliDirectImageAlgebraModel ...` contains an algebra `M.algebra : Y.QCAlg`,
  so its underlying module is quasi-coherent. The fields `sections`,
  `naturality`, and `structure_map` identify this algebra with the *existing*
  `moduliDirectImage` as rings, naturally on every étale chart, and with the
  canonical action of regular functions. Thus this is the stated direct image,
  up to its required canonical size transport, not an arbitrary QC algebra.
- `ModuliAlgebraPoint B x` is a natural ring map from the algebra on the entire
  slice `F/x` to regular functions on that slice, splitting its structure map.
  Since F is fibred in groupoids, `F/x` is equivalent to schemes over the test
  scheme of x. By the inverse-image/direct-image algebra adjunction, this is
  exactly an O_T-algebra map from x^*B to O_T. In particular the structure-map
  equation matters: a mere ring homomorphism would not give the stated points.
- `moduliAlgebraPointPresheaf` restricts these points by `Over.map`; the opposite
  category of its elements is `moduliRelativeSpectrum B`. Its arrows are the
  original arrows compatible with these algebra maps. Its projection remembers
  x. The object and morphism data are real constructions, with identity and
  composition proofs in their structure fields and no sorried data.
- The existential `hV` asserts algebraicity of this particular source stack.
  On a scheme chart the same functor is the relative spectrum represented by
  gluing affine spectra, by Stacks Constructions, `equation-spec`,
  `lemma-spec-affine`, `lemma-spec`, `lemma-glueing-gives-functor-spec` and
  `definition-relative-spec`. Thus the functor does not choose an alternative
  relative spectrum construction.
- The target `moduliImageRelativeSpectrum M` uses the *existing*
  `RelativeSpecData.relativeSpec`, with data from
  `space_relative_spec_correspondence`. It is an `AffineOver Y` object, and
  therefore an algebraic space (and its discrete fibred category is the
  corresponding algebraic stack). The correspondence identifies its affine
  charts with spectra of `M.algebra` and fixes its counit algebra. The choice
  is made from a normalized anti-equivalence, which determines the object up
  to the canonical isomorphism used here; it is not a choice from bare existence.
- `IsModuliRelativeSpecEvaluation φ B M h` first requires the projection square
  to commute. Its second clause quantifies over every source point, target
  étale chart, compatible source chart over it, chart of the target spectrum,
  and map from the source point to that chart. The left side takes a direct
  image section and evaluates it using the algebra point. The right side pulls
  back its tautological function, using the recorded counit and direct-image
  projection of the space relative Spec. This is exactly evaluation
  φ^*φ_*B → B followed by tautological evaluation. Checking over all such charts
  specifies the canonical arrow, rather than an unconstrained adequate map.
- The final conjunct is `IsAdequateModuliSpace` for that source, target and arrow.
  There is no extra condition on B in this conclusion or its construction.

Dependency declarations read and used:

- Mathlib `Field` in `Mathlib.Algebra.Field.Defs` (commutative ring and division
  ring, with nontriviality).
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`,
  `CategoryTheory.IsAdequateModuliSpace`, full definition and docstring read.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`,
  `ModuliAlgebraSheaf`, `IsQuasicoherentModuliAlgebra`,
  `moduliStructureSheaf`, `ModuliPushforwardIndex`, `moduliDirectImage`,
  `moduliChartSchemeMap`, and their definition/docstring dependencies read.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`, `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`, `AlgebraicGeometry.AlgebraicSpace`;
  actual fppf sheaves, representable diagonal and étale scheme atlas.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence`,
  `space_relative_spec_correspondence`, `RelativeSpecData.relativeSpec`,
  `RelativeSpecData.counitAlgebra`, `StructureAlgebraModel.projection`;
  their full structures, normalizations, signatures and docstrings were read.
  This already landed node is added to stmt_deps because the statement uses its
  target construction, already described in the original prose.
- The metatheoretic size convention `def-weil-size-convention` is represented
  by explicit universe binders and `hsmall`, not a duplicate Lean definition.
- `StablePointedModuliGroupoids` supplies the existing `discreteModuli`,
  `discreteModuliMap` and stack interfaces, through the public dependencies.
- Stated proof dependencies are imported privately:
  `StackQuasiCoherentSchemeRestriction` and `ChartwiseEtalePermanence`.
  The other proof dependencies have no recorded modules and are documented in
  the theorem's complete five-step proof, rather than invented or assumed as
  extra hypotheses. The definition dependencies already publicly import the
  other recorded proof dependencies. No import cycle is introduced.

Edge cases checked:

- For the zero algebra, a map to regular functions exists only over the empty
  test scheme; the resulting relative spectrum is empty, as required. No
  `Nontrivial` assumption is put on B.
- For the structure algebra the only retraction is its identity; its relative
  spectrum is the original stack, and evaluation reduces to the original map.
- For an empty source the slice and element constructions still make sense;
  no `Nonempty` assumption occurs.
- Non-affine test schemes are handled by maps of presheaves on the entire
  slice, not by algebra maps on global sections alone.
- Arbitrarily generated algebras within the chosen ambient scheme universe,
  positive characteristic, nonreduced algebras and nonflat algebras remain
  allowed. A polynomial algebra exceeding the scheme universe detects the
  missing size convention addressed below.
- Independent site object and arrow universes are preserved. The canonical
  ULift maps in the dependency preserve regular functions, multiplication and
  all evaluation equations.

Searches (2026-10-24; wrapper output in searches.jsonl):

- LeanFinder via msearch.py: “Relative spectrum of a quasi coherent algebra on
  an algebraic stack preserves adequate moduli spaces”. Eight hits, headed by
  `AlgebraicGeometry.isAffine_Spec`, affine-scheme and affine-morphism facts;
  none states this theorem or defines its stack functor.
- Loogle via msearch.py: `"adequate", "Spec"`: zero hits.
- Mathlib grep via msearch.py: `relativeSpec|RelativeSpec|adequateModuli`,
  subdirectory AlgebraicGeometry: zero hits.
- LeanSearch and LeanFinder via msearch.py: “Relative spectrum functor of
  algebra homomorphisms to the structure sheaf on an algebraic stack”. Eight
  hits each, concerning `Spec.toSheafedSpace`, `Spec.map`, and ordinary scheme
  Spec; no fibred-groupoid relative spectrum or adequacy statement.
- rg on WeilConjectures and Sheaf for
  `relativeSpec|RelativeSpec|relative[Ss]pectrum|adequate.*[Ss]pec`:
  found the scheme relative spectra and the already landed algebraic-space
  correspondence. Read and reused the latter. No stack algebra-point functor
  or adequacy-preservation statement was present.
- rg for the item id in WeilConjectures: no match.
- DAG filenames and concept searches found the unstated
  `lem-sfb-stack-relative-spec-construction` theorem and the landed
  `lem-sfb-space-relative-spec-correspondence`. The former is a stronger proof
  dependency and is not used as an assumed declaration; the algebra-point
  helpers are the item's own explicit definiendum, as allowed by the brief.
- `tools/blueprint_refs.py ancestor` returns ancestor None for this imported
  supporting item; its search for “relative spec” finds eight scheme/purity
  definitions, none a duplicate of the stack algebra-point construction.

No remaining STATEMENT-DISPUTED flag. The precise node fault is corrected and
recorded below. Only the final theorem is `sorry`, with its original five-step
proof and all named prerequisite uses in its docstring.

## Statement corrected

The old statement is preserved verbatim in `statement_change.old_statement`.
It asserted the same relative-spectrum result for an arbitrary algebra in the
recorded ambient coefficient universe, without saying that its chart rings
fit the universe of schemes. The algebra interface permits coefficients in
`max (u+1) v w`, whereas `AlgebraicSpace` and `IsAlgebraicModuliStack` use
`Scheme.{u}`. A polynomial algebra on a set larger than universe u is already
a counterexample to that size-unqualified claim over Spec k: it is QC, but its
spectrum cannot be a scheme in that smaller universe. The source's ordinary
relative-Spec construction uses schemes and chart rings in a common ambient
universe. We make this necessary size convention explicit, allowing compatible
section families and the site to retain their larger independent universes.
The cited source is Stacks Constructions, `situation-relative-spec`,
`equation-spec`, `lemma-spec-affine`, `lemma-spec`, `definition-relative-spec`,
and Alper arXiv:1005.2398v3 Lemma 5.2.11, printed p.28 (read online).
This supporting node is not the blueprint unit's own statement.

The only actual citers (filtered by stmt_deps/proof_deps after the full rg
search for the item id) are:

- `lem-sfb-adequate-closed-substack-affinization`: holds. The algebra in its
  application is the quotient by the closed substack's ideal, so its chart
  rings are small in the scheme universe.
- `lem-sfb-adequate-integral-comparison-finite`: holds. Its application is to
  the integral-closure algebra in the normalization of the finite-type
  representable map, constructed inside the small scheme-test rings.

No citer is edited. The extra filename hit
`lem-sfb-stack-relative-spec-construction` only mentions this item in lineage
metadata and is not a statement/proof dependency citer. Proof and proof_deps
are unchanged. stmt_deps gains the size-convention node and the already landed
space relative-Spec correspondence used for the original target construction.

## Second reading by Q61

A second pass by the same dispatcher worker reopened the full node and module.
No independent worker was started, as the dispatcher forbids delegation; the
maintainer supplies the independent review. This pass checked all binders and
both conjuncts against the clause mapping above. It found and repaired the
missing universe convention explicitly, rather than silently specializing the
algebra or identifying site universes. It also checked the orientation of the
base-triangle transports: both sides start at the source test scheme, using
`(φ.w_obj ...).symm` and `(h.w_obj ...).symm` respectively.

The pass verified that the functor of points uses the full slice and its
algebra equation, so it includes automorphisms and non-affine test schemes.
The direct-image equivalences are multiplicative, natural and compatible with
regular functions; the target uses the existing normalized correspondence.
The evaluation equation fixes the canonical map on all chart functions. The
zero algebra, structure algebra, empty source and arbitrary generated algebra
cases introduce no added mathematical assumptions. The concluding adequacy
predicate is the recorded dependency, with no private redefinition.

Validation: the complete delivery module compiled under both its sandbox name
and actual library module name with scompile.py, approximately seven seconds
each, without errors or warnings other than the expected postponed-proof
warning. Dry-run and final delivery validation follow through deliver2.py.
