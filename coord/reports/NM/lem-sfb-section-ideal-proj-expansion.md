## Worker report

The module `Sheaf.AlgebraicGeometry.SectionIdealProjExpansion` states
`AlgebraicGeometry.SectionIdealExpansion.section_ideal_proj_expansion`. Its proof is the
only `sorry` introduced. All auxiliary declarations belong to the specified expansion,
are recorded in `lean.declarations`, and have source/blueprint docstrings. There is no
chosen replacement module, arbitrary expansion morphism, or unspecified symmetric algebra.

The previous worker's stale-dispatch diagnosis concerned stage 1. The live item has
`status: split` and a Q65 stage-1 review dated 2026-10-22, but no `lean` or `reviewed_lean`
record. Stage 2 therefore still had work to do. This delivery preserves Q65's entire
statement, proof, proof dependencies and stage-1 review. It adds the Lean record and four
already-landed statement dependencies for the exact APIs used below.

Hypotheses, in the order of the node:

* An arbitrary scheme T and family X/T are `(T X : Scheme.{u}) (f : X ⟶ T)`.
  `[IsProper f]`, `[Flat f]` and `[LocallyOfFinitePresentation f]` render properness,
  flatness and local finite presentation. Properness supplies quasi-compactness and
  quasi-separatedness, so this is finite presentation, with no extra finiteness condition
  on T. There is no Noetherian or reduced-base assumption.
* `FibreConditions f g` includes the recorded `HasNodalGeometricFibres f`, hence nonempty
  connected geometric fibres, Krull dimension one and the completed-local-ring nodal test.
  It explicitly requires `IsReduced` and `Scheme.IsPureDimension 1` on every geometric
  fibre. Thus topological dimension one is not substituted for pure dimension one.
* `(g : ℕ) (hg : 2 ≤ g)` and the last clause of `FibreConditions` give exactly the same
  genus on every geometric fibre. The clause uses `Scheme.arithmeticGenus` with the
  `Over` structure whose morphism is `pullback.snd f a`, so genus is dimension H1(O),
  including for reducible nodal curves. No smooth-curve genus is silently substituted.
* `(r : ℕ) (s : Fin r → (T ⟶ X))` and `hs` give the ordered finite list of old sections.
  `hdisjoint` is disjointness of their images, and `hsmooth` places every old image in
  `f.smoothLocus`. The empty list is allowed.
* `(d : T ⟶ X) (hd : d ≫ f = 𝟙 T)` is the arbitrary extra section Delta. No smoothness,
  disjointness, Cartier or stability condition is imposed on it.

Constructions and conclusions, clause by clause:

* Delta's ideal is the existing `d.ker`, and its module is `d.ker.toModules`. Since f is
  proper and d is a section, d is a closed immersion, so this is exactly the kernel of
  O_X to Delta_* O_T, rather than a different support ideal. The dual is the existing
  `Scheme.Modules.dual`, with notation `ᵛ`, namely the internal O-linear Hom into O.
* `oldIdeal s` is the product of the old section ideals. For disjoint smooth sections this
  is the Cartier ideal of the sum D. Its dual `(oldIdeal s).toModulesᵛ` is precisely the
  recorded divisor-line-bundle convention. The conclusion `(oldIdeal s).IsInvertible`
  supplies the Cartier property; it is not an added hypothesis.
* `inclusion J` is the transpose of `J.toModulesι` after the evaluation-at-one
  identification `dualUnitIso.inv`. Thus its value on a function is multiplication on J.
  `diagonal s d` is `biprod.lift` of these two specified inclusions, with the plus sign
  `(u,u)` required by the node. `moduleK s d` is its actual categorical cokernel.
  `Mono (diagonal s d)` says that the defining sequence starts with zero; the chosen
  cokernel and its projection give exactness and the terminal zero in the abelian module
  category. `(moduleK s d).IsFinitePresentation` is the claimed finite presentation,
  and the existential `hqc` supplies quasi-coherence without assuming it as an input.
* `firstToK` and `secondToK` are the inclusions of the two biproduct summands followed by
  the fixed cokernel projection. `oldQuotient` is the cokernel of `firstToK`, and
  `newQuotient` the cokernel of `secondToK`. These are K modulo the images of the two
  summands, with the order required by the node.
* `schemeZ s d` and `projection s d` are exactly `relProj` and `relProjHom` of
  `SymmetricAlgebraSheaf.gradedAlgebraData (moduleK s d)`. The canonical affine section
  rings, symmetric grading and restriction maps come from that dependency; no alternate
  projective-bundle construction or generic isomorphic scheme replaces them.
* `Lifts.old_invertible` and `extra_invertible` state invertibility of the specified
  restricted cokernels. The `old_surjective` and `extra_surjective` fields state that the
  actual pullbacks of their quotient maps are epimorphisms.
* The `tautological` field uses the existing chart-normalized
  `ProjectiveBundleQuotientGeometry.TautologicalQuotient`. The `old_classifies` and
  `extra_classifies` fields use that module's exact `Classifies` relation for these
  quotient maps. `old_unique` and `extra_unique` say any map classifying that same quotient
  equals the chosen lift. They do not assert uniqueness of all lifts of an old section.
  `old_over` and `extra_over` give the maps over X; the section fields give sections over T.
* `IsProper (projection s d ≫ f)`, `Flat` of that morphism and the existential `hfp`
  render properness, flatness and finite presentation of Z/T, with properness again
  supplying quasi-compactness and quasi-separatedness. `FibreConditions` of the same
  composite gives nonempty connected reduced pure-one-dimensional nodal geometric fibres
  with unchanged H1 genus g. Smoothness of all lifts is explicitly in the theorem, and
  their pairwise disjointness is in the two `Lifts.disjoint_*` fields.
* `FibreGeometry` quantifies over every algebraically closed field in the scheme universe
  and every geometric point a. `fibreMap` is the actual morphism on pullback schemes,
  and every marking is the recorded `Scheme.Hom.baseChangeSection`, rather than a chosen
  point with the same image. Its first clause says that the smooth, noncolliding case
  has an isomorphism p on the entire geometric fibre (the categorical meaning of identity
  here, since Z and X are separately constructed schemes).
* In the collision case the geometric Delta and old section are equal as Omega-morphisms.
  `ExceptionalFibre` with attachment count 1 says the fibre over that point is a P1 over
  Omega embedded as an irreducible component. Both lifted sections lie on it; global
  disjointness and smoothness make these two points distinct from one another and from
  the attachment. There is exactly one nonsmooth point on this component. Since the
  whole fibre is nodal and the component is a smooth embedded P1, these are exactly
  the transversal attachments to the other components.
* When Delta is nonsmooth, `ExceptionalFibre` with count 2 gives the P1 bridge, its two
  distinct attachments and the smooth lifted new point on it. Self-nodes are allowed:
  the two attachments can meet the same old component.
* In both exceptional cases `ExceptionalFibre` says that p restricts to an isomorphism
  over every open avoiding the centre. The centre is a closed geometric point, so this
  includes its whole complement and is exactly being an isomorphism off the inserted P1.
* `UnchangedComponents` gives a bijection from all old irreducible components to all new
  components except the inserted one. Its normalization isomorphisms commute with the
  maps to the original curve. Equality of inverse images of `specialPoints` retains all
  markings and branches, including two branches of a self-node. On an old component a
  lost colliding marking or branch is replaced by the attachment at the corresponding
  normalized point. All other marked sections are also individually retained by the
  equations in `Lifts.old_over` and the isomorphism away from the centre.
* The final quantifier ranges over every cartesian diagram of families, with arbitrary
  base morphism b and X-morphism h preserving each ordered section and Delta. The added
  premises `(∀ i : Fin r, s' i ≫ f' = 𝟙 T')` and `d' ≫ f' = 𝟙 T'` explicitly
  require the primed maps to be sections of the primed family. No
  flatness of b is required. It supplies quasi-coherence of the rebuilt K and its actual
  quotient-classifying lifts, then uniquely specifies `SequenceComparison` and the
  comparison morphism j satisfying `Compatible`.
* `SequenceComparison.ideal` and `divisor` preserve the actual ideal inclusions;
  `dual` and `divisorDual` preserve evaluation, which characterizes the dual comparison
  rather than merely asserting an abstract isomorphism. `multiplication` and
  `divisor_multiplication` retain both diagonal inclusions. `first` and `second`
  preserve the maps from both summands to the actual cokernel K; `exact_left` retains
  injectivity after pullback. Cokernel right exactness gives the rest of the whole
  sequence after base change. The normalized quotient comparison is therefore unique.
* `Compatible` makes the square for the actual relative-Proj projection cartesian and
  preserves the tautological quotient, using the existing section-normalized tensor
  composition maps. Its final two equations preserve every lift. The existence-unique
  quantifiers give canonicity. Taking the cartesian maps to be isomorphisms gives exactly
  compatibility with isomorphisms preserving the ordered old sections and Delta; taking
  the canonical pullback square gives arbitrary base change. Identity diagrams are included.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`; its definition includes
  separatedness, universal closedness and local finite type.
* `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, the affine-local flatness condition.
* `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
* `Sheaf.AlgebraicGeometry.NodalGeometricFibres`: `HasNodalGeometricFibres`, read in full,
  also checked against the live server via `scompile.py --source`.
* `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules`, with its O(D)=I_D-dual
  docstring, and the existing `toModules`/`dual` convention. The transposed actual ideal
  inclusion uses `Modules.dualMap` and `Modules.dualUnitIso` from the existing dual API.
* `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj` and `relProjHom`, read with their gluing docstrings.
* `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `SymmetricAlgebraSheaf.gradedAlgebraData`, read in full, including the actual section
  rings, grading, restriction and degreewise base-change theorem.
* `def-per-projective-bundle-quotient-data` owns
  `ProjectiveBundleQuotientGeometry.TautologicalQuotient`, `pulledQuotient` and
  `Classifies` in `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`. Their
  full signatures and chart-normalization docstrings were read. This existing definition
  node is added to `stmt_deps`; `lem-trf-projective-bundle-quotient-geometry` is the
  existence/universal-property theorem and remains a proof dependency.
* Other added already-landed dependencies: `def-sfb-stable-pointed-curve` for
  `Scheme.normalizedComponentMap` in `Sheaf.AlgebraicGeometry.StablePointedCurve`;
  `def-weil-pure-dimension` for `Scheme.IsPureDimension` in
  `Sheaf.AlgebraicGeometry.PureDimension`; `def-pc-genus` for `Scheme.arithmeticGenus`
  in `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`. Their records and full
  declarations/docstrings were read. No stability hypothesis is taken from the first:
  only its already-shared normalization map is used.

All recorded proof dependencies with existing module records or Mathlib matches have
their modules imported, privately when used only by the future proof. The new stage-1
algebra lemma `lem-sfb-split-node-section-dual-presentation` has no Lean statement yet;
there is no nonexistent import for it. This is a proof prerequisite, not an object needed
to type the statement.

Edge cases checked before and during statement writing:

* r=0: the old ideal is the empty product, hence O; there are no old quotient/lift
  requirements. The extra section can still pass through a node. No Nonempty Fin r binder.
* Empty base: sections and the construction exist on empty schemes; all geometric tests
  are vacuous. The genus lower bound does not assert a nonempty base.
* No assumptions on characteristic. The smooth collision's attachment [1:-1] differs
  from [1:0] and [0:1] also in characteristic two. The bridge's two points 0 and 1
  remain distinct in every field.
* Reducible fibres, self-nodes and positive-genus old components are allowed. Component
  bookkeeping is on canonical normalizations and keeps the branch points separately.
* Nonreduced/non-Noetherian bases and nonflat changes of base are included literally.
* The P1 index is `ULift.{u} (Fin 2)`, retaining two coordinates in the scheme universe;
  using `Fin 2` directly would accidentally restrict the universe. All universes and
  variables are explicitly bound, and both autoImplicit options are false.

Searches for existing notions and statements:

* `msearch.py NM lem-sfb-section-ideal-proj-expansion leanfinder` with query
  "Knudsen expansion of a nodal curve from the dual ideal of a section using relative
  Proj of the symmetric algebra": eight results, including `Proj`, `Proj.toSpecZero`,
  `Proj.fromOfGlobalSections` and unrelated Weierstrass point ideals; no expansion theorem.
* `msearch.py ... loogle` with query
  `AlgebraicGeometry.Scheme.Modules.dual, AlgebraicGeometry.HasNodalGeometricFibres`:
  zero hits; Loogle's indexed environment did not know the project dual declaration.
  This is not evidence that the dual is missing; its actual project source was read and reused.
* `msearch.py ... grep 'Knudsen|sectionIdealProjExpansion|rationalTail|rationalBridge'
  AlgebraicGeometry`: zero Mathlib hits.
* `rg` on `lean/WeilConjectures` and `lean/Sheaf` for Knudsen/knudsen, rational-tail/bridge,
  SectionIdealProj/section_ideal_proj and the item id found no expansion declaration.
  Nearby projective-stable-level and logarithmic-dualizing modules merely cite Knudsen.
* Further direct `rg` searches for `arithmeticGenus`, `MultipointedCurve`, projective
  bundle quotient geometry, dual maps and tensor-pullback comparisons found the shared
  APIs used above. The existing multipointed-curve structure does not encode this Proj
  construction, its arbitrary extra section or its quotient-defined lifts and was not copied.

Source consultation: the current stage-1 statement/proof was read in full. Knudsen's
primary-author arXiv HTML https://arxiv.org/html/1106.1588 was opened at the introduction's
construction and Section 5, Theorems 5.1 and 5.2. The general-base claim follows the
already-reviewed node's etale-local algebra and descent argument; no Noetherian hypothesis
from that paper's Main Lemma was silently imposed.

No statement correction or mathematical dispute was necessary. The natural-language
statement is unchanged.

Validation: `scompile.py NM lem-sfb-section-ideal-proj-expansion <module>` compiled the
full statement in both sandbox and library module modes with no errors or warnings except
the permitted theorem sorry. The final delivery dry run and delivery are recorded by their
wrapper output. No global build, direct repository write, or direct Git command was used.


## Repair of returned head 32789282eead

* H3/H6: the base-change clause now assumes both
  `(∀ i : Fin r, s' i ≫ f' = 𝟙 T')` and `d' ≫ f' = 𝟙 T'` before asserting
  the existence of `L'`. Compatibility with h alone did not imply these equations.
  In the return's counterexample T'=T ⨿ T, the map d' over the swap of the summands
  satisfies compatibility with the codiagonal but fails the new section premise.
  Actual pullback sections satisfy both premises by construction. The correction
  retains arbitrary b, identity diagrams, isomorphisms, r=0 and the empty base.
  The node already says base change of sections, so its natural-language statement
  requires no correction. Its `lean.statement` is the revised signature verbatim.
* H2/H4: added the already-landed `def-per-projective-bundle-quotient-data` to
  `stmt_deps` and corrected the ownership attribution above. The existing public
  import already exposes its exact data and classification definitions, so no new
  module or duplicate declaration is introduced. This is a repaired delivery with
  the authorized statement-dependency addition, not a stage-2 FIX.
* Compared the saved packet with current main's node: the main statement, proof,
  proof dependencies and all stage-1 fields remain unchanged. Only `lean` and the
  list of additional already-landed statement dependencies differ.

Required self-check: read the final theorem and the `Lifts` fields together.
The section premises now supply exactly the equations forced by `old_over` plus
`old_section`, and `extra_over` plus `extra_section`. All other hypotheses and
conclusions are retained. The definition node's recorded module and declarations
agree with the existing import and `Lifts` uses. No additional sorry or declaration
was introduced by this repair; all variables remain explicitly bound.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
