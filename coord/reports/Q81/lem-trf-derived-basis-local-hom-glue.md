## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue` states
`AlgebraicGeometry.derived_basis_local_hom_glue`, with its single proof `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The old NQ delivery was stage 1: its report explicitly says that no Lean was written,
and the current item has no Lean record. This delivery supplies stage 2.

Hypothesis and conclusion correspondence:

- The scheme is `(X : Scheme.{u})`; `C : Set X.Opens` is precisely a set of opens,
  without an enumeration, finiteness, quasi-compactness, or basis assumption.
- The cover condition is `hcover : sSup C = ⊤`. Supremum in `X.Opens` is union.
- For each `U ∈ C` and `V ∈ C`, `hrefine` says
  `sSup {W : X.Opens | W ∈ C ∧ W ≤ U ⊓ V} = U ⊓ V`.
  Thus the collection refines intersections exactly as in the node. It need not
  refine arbitrary neighbourhoods in the topology of X.
- `M N : schemeDerivedCategory X` are arbitrary unbounded derived objects of
  O_X-modules, using the recorded dependency declaration. There is no boundedness,
  quasi-coherence, constructibility, self-Hom, or concentration hypothesis.
- `hnegative` quantifies over exactly `U ∈ C`, every integer `i`, and `i < 0`.
  It says `Subsingleton (rU.obj M ⟶ (rU.obj N)⟦i⟧)`, where this report's `rU`
  denotes the explicit term
  `(SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).mapDerivedCategory`
  in the file. This is exactly vanishing of the cross Hom group: a preadditive
  Hom type already contains its zero, so subsingleton is the zero-group condition.
  The shift is applied after restriction, as in the node.
- The conclusion quantifies over every `O : X.Opens` satisfying
  `sSup {U : X.Opens | U ∈ C ∧ U ≤ O} = O`. This is exactly being a union of
  members of C: one may use all members contained in O instead of choosing a
  particular subfamily. The first conjunct gives the same negative Hom vanishing
  for every integer `i < 0` on O.
- In the second conjunct the local family has index type
  `{U : X.Opens // U ∈ C ∧ U ≤ O}`. Its component `a U` has source the restriction
  of M and target the restriction of N on U. Each inclusion `h : V.val ≤ U.val`
  is tested by
  `derivedOpenHomRestriction X.toRingedSpace (homOfLE h) (a U) = a V`.
  This is inclusion compatibility, not an additional overlap condition.
- The conclusion `∃! f, ∀ U, derivedOpenHomRestriction ... f = a U` is the
  singleton-fibre characterization of the asserted bijection under canonical
  restriction. Existence is surjectivity and uniqueness is injectivity. The
  canonical restriction maps preserve inclusion compatibility by their composition
  law; no arbitrary map or chosen comparison is substituted. This is the same
  unique-gluing formulation Mathlib uses for `TopCat.Sheaf.existsUnique_gluing'`.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Opens`
  for `def-pc-scheme`. I read its structure, local-affine condition, and morphism
  structure in the pinned source.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` for `def-pc-derived-category`.
  This recorded module is absent from the older local source checkout, so I read
  its complete current server source with `scompile.py --source`. It imports the
  upstream `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`, which gives
  the shared `moduleRings`, restriction exactness instances, and
  `derivedOpenHomRestriction`. I read that server module too. The statement uses
  these upstream names and does not import the retired side-library duplicate.
- `SheafOfModules.overFunctor` and `overMap`, and their comparison
  `SheafOfModules.overFunctorMap`, are Mathlib's open-site restrictions. The Hom
  restriction is the shared conjugation by their derived composition comparison.
  The category on the slice over U is canonically equivalent to O_U-module
  sheaves via `Scheme.Modules.overEquiv U`, as in the existing derived Hom
  Mayer--Vietoris interface. Thus the objects are exactly the node's restrictions
  to opens; this does not replace them by a different coefficient category.
- The ambient and all-open `HasDerivedCategory.{w}` instance binders fix compatible
  localization representations, following the shared interface. They add no
  geometric or vanishing condition, impose no equality of independent universes,
  and retain arbitrary `u` and `w`.
- The already stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms` for
  `CategoryTheory.Precoverage.IsSiteForCoverings`, and
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace` for the recorded locally
  ringed-space-morphism dependency. These imports retain the node's proof plan.
  The quotient-map and local-Ext-sheaf proof nodes have no Lean records yet, so
  there is no module of those proof-only dependencies to import. Neither notion
  is required for typing the item's statement.

Source check: I read `cohomology.tex` at
`lemma-vanishing-and-glueing` (0D66(2)) and `lemma-uniqueness` (0D68), and
`topology.tex` at `lemma-create-map-from-subcollection` (0D5Q). The node's five
proof steps are fully included in the theorem docstring: quotient map; direct-image
ring sheaf; application of 0D66; overlap comparison and unique gluing; negative
vanishing and empty covers. The quotient target is only a ringed space, and no
locally ringed condition on it enters the statement.

Edge cases checked before writing: O empty with no C member inside it; O empty
with the empty open in C; X empty and C empty; C={X}; disjoint covering members;
zero M or N; negative i=-1 and arbitrary smaller degrees. No `Nonempty` or finite
instance occurs. With empty C the covering equation forces X empty, and the
unique-preimage conclusion gives the unique map to the empty family. With an
empty open present its unique local morphism is retained by the subtype indexing.
The condition excludes i=0 from vanishing while retaining degree-zero morphisms
in the gluing assertion. The subtype includes equality inclusions and all members
contained in O, exactly as required.

Searches made:

- `msearch.py leanfinder`: “Derived category morphisms between global objects glue
  uniquely on an intersection refining open cover under local negative Hom
  vanishing”. Eight hits: ordinary sheaf unique-gluing and Mayer--Vietoris sheaf
  gluing, plus `DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`.
  The latter is a degree-support criterion, not this local-to-global theorem;
  the former assume the sheaf condition which our node supplies. I opened both
  the derived-Hom candidate and `TopCat.Sheaf.existsUnique_gluing'` in Mathlib.
- `msearch.py leansearch`: “Negative local Ext vanishing on an intersection refining
  open cover implies unique gluing of morphisms in the derived category”. Eight
  ordinary presheaf/sheaf unique-gluing hits; no derived negative-Ext criterion.
- `msearch.py loogle`: `"DerivedCategory", "hom"`. Twelve hits for localization,
  shift, additivity and single-complex comparison declarations, no matching theorem.
- `msearch.py grep`: `negative.*(Hom|Ext)|[Dd]erived.*[Gg]lu|[Gg]lu.*[Dd]erived`
  under Mathlib `Algebra/Homology`: zero hits.
- Direct `rg` of the source repository, `lean/Sheaf`, and the upstream name index:
  `derived.*(hom_gl|hom_des|basis)|local.*negative|0D66|0D68|lem-trf-derived-basis-local-hom-glue`.
  No declaration of the item. The nearest side-library results are binary-open
  `scheme_derived_hom_gluing`, its open-union consumer, and perfect-object stalk
  descent. The binary theorem gives existence with no uniqueness and only two
  opens; the perfect-object theorems have different hypotheses. I opened the
  binary theorem's complete signature and docstring. None can be recorded as an
  exact existing match. A search for derived restriction and Hom restriction names
  found the existing shared canonical construction used here.

No statement dispute or mathematical node fault was found. No claim of an
independent second reading is made: the worker delivers directly for the
maintainer's independent review under the launcher's current instructions.

## Second reading by Q81

Independent maintainer second reading, 2026-10-18, of immutable delivery
`576108da99230c4395568a1a055f89e33c84db3d`. This reading was performed by the
external reviewer, not by the worker. The snapshot files, rather than a moving
branch, were reviewed.

Hypotheses and conclusions checked:

1. `X : Scheme.{u}` uses the recorded Mathlib scheme, including the local-affine
   condition (Scheme.lean:42); `C : Set X.Opens` is a set of actual opens.
   `hcover : sSup C = ⊤` is exactly the covering equation. No finiteness,
   quasi-compactness, separatedness, or basis-for-the-original-topology assumption
   appears. Verdict: exact.
2. `hrefine` takes precisely two members of C and asserts that all C members below
   their intersection have supremum that intersection. This matches the node's
   intersection-refinement equation, including equality inclusions. Verdict: exact.
3. `M N : schemeDerivedCategory X` uses the recorded shared category of all
   unbounded derived objects of O_X-modules. The current source was read through
   `scompile.py --source WeilConjectures.AlgebraicGeometry.DerivedCategory`:
   `schemeDerivedCategory` is the genuine DerivedCategory of SheafOfModules, not
   the quasi-coherent full subcategory. Both statement dependency JSON files were
   read in the snapshot. Verdict: exact.
4. `hnegative` quantifies over every U in C and every integer i < 0, with source
   the restriction of M and target the restriction of N shifted by i. In an
   additive derived category Hom contains zero, so `Subsingleton` means precisely
   the zero Hom group. This is cross Hom, not self Hom. Verdict: exact.
5. Every open O with `sSup {U | U ∈ C ∧ U ≤ O} = O` is considered. This equation
   is equivalent to O being a union of any subfamily of C: any chosen subfamily
   is contained in the full set of C members below O, and all those members lie
   in O. The first conjunct propagates exactly the same negative vanishing.
   Verdict: exact.
6. Local maps are indexed by `{U // U ∈ C ∧ U ≤ O}`, with the correct restricted
   source and target. Compatibility tests every inclusion V ≤ U by the shared
   `derivedOpenHomRestriction`. The `∃! f` conclusion states that each compatible
   family has one global preimage with precisely these restrictions. Restrictions
   preserve compatibility by functoriality of the canonical comparisons, so this
   is equivalent to the asserted restriction bijection, including injectivity.
   Verdict: exact.

Canonical constructions and universes:

The exact current `moduleRings` and `derivedOpenHomRestriction` definitions and
module docstring were read with
`scompile.py --source WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`.
`moduleRings` forgets commutativity on the genuine structure sheaf.
Hom restriction applies the derived `overMap` and conjugates by the derived
composition/`overFunctorMap` isomorphism. It has real data, not an arbitrary map
or a choice from a bare existence claim. Mathlib
Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:59,76,83 supplies
`overFunctor`, `overMap`, `overFunctorMap`; AlgebraicGeometry/Modules/Sheaf.lean:
558,566,605 supplies `overEquiv`, `overMapCompOverEquiv`, `overFunctorEquiv`.
These identify this slice-site encoding with the node's restriction to the open
subscheme, including its restriction maps.

`u` and `w` are explicitly bound independently. The ambient and all-open
HasDerivedCategory binders choose localization models in the same Hom universe;
they impose no geometric hypothesis or equality of independent site universes.
Mathlib DerivedCategory/Basic.lean:72-82 provides the localization meaning and
standard construction; the shared GrothendieckAbelian/HasDerivedCategory module
also supplies small-Hom models via K-injectives. A common sufficiently large w
always permits the standard construction for every open. No new helper or
statement prerequisite is needed to type the theorem. Proof-only nodes without
Lean records are not missing notions in this signature.

Source and proof audit:

Read the group clone's literature/stacks-project/cohomology.tex:11127-11162
(Tag 0D66(2)), :11188-11225 (Tag 0D68), and topology.tex:377-414 (Tag 0D5Q),
as well as schemes.tex:1648 (01IJ). The ringed-space result has no hidden
Noetherian, boundedness, or quasi-coherence premise. The five docstring steps
match the node: construct the continuous map with saturated cover members;
put the direct-image structure sheaf on its target; apply 0D66(2); check overlaps
by their refining cover and glue uniquely; propagate negative vanishing and
handle empty covers. The word quotient in this construction describes the
quotient of the point set in 0D5Q; no final-topology/QuotientMap property is needed.
The target only needs to be ringed, so no locally ringed-space condition was
silently imposed. Read the proof-dependency statements in the group clone:
open-subcollection-map supplies the three requisite properties; local-ext-sheaf
supplies the all-open vanishing and sheaf assertion. The sites definition gives
the equalizer/sheaf axiom, and the ringed-space-morphism definition allows the
identity map into the direct image. The image/intersection and overlap arguments
are elementary consequences of saturation and the sheaf axiom.

Edge cases: O empty, both with and without the empty open in C; X empty and C
empty; C = {X}; disjoint members; zero M or N; and every negative integer,
including -1, are retained. Empty-cover sheaf sections are singletons. If the
index contains the empty open, its Hom set is also a singleton. Degree zero is
not incorrectly subjected to the vanishing hypothesis. There is no restriction
on characteristic and no Nonempty or finite instance.

One-definition-per-notion searches:

Independent rg searches used negative shifted Hom/Ext, morphism descent,
0D66/0D68, local negative, and derived Hom gluing in Mathlib's derived-category
sources, the slopmaster2 WeilConjectures tree and the group clone's lean/Sheaf.
An independent LeanSearch query about local vanishing of negative shifted
morphisms and unique descent returned effective-epimorphism descent and general
pseudofunctor descent, not this theorem. Loogle `DerivedCategory, Subsingleton`
returned `DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`;
its exact signature in Fractions.lean:163 requires strict cochain degree bounds
and is not this local-to-global criterion. Opened SchemeDerivedHomGluing.lean:89:
its theorem handles two opens and existence without uniqueness. Perfect-object
stalk descent also has different hypotheses. No exact existing duplicate was
found; the existing canonical restriction construction is reused.

Records and maintainer gates:

The immutable commit changes only the item lean record, its single module and
the worker report. Both statement dependencies are unchanged. The lean record's
statement was programmatically compared with the file from `theorem` to before
`:=`: verbatim equal. All lines are at most 100 characters, autoImplicit is
false, and all variables/universes are bound. There is exactly one theorem with
proof `by sorry`; no definitions, extra proofs, axioms, private constructions or
local instances were delivered. Both module and theorem docstrings name the
source and blueprint id and the theorem docstring gives all five proof steps.
Public imports supply the statement; non-public imports are proof-plan imports.
No pro-etale substitute or dropped infinity/dg/model-category machinery occurs.
The item and every direct statement/proof dependency were compared against the
available origin/newtargets-dag route-pivot-dropped.txt: no hits. No repair note
for this item exists in that ref. Refresh was attempted as requested but the
remote denied the fetch; this route check therefore uses the available ref.

Compiler evidence:

The original report did not record a per-file compiler outcome. The independent
review reproduced compilation of the sole immutable delivered file using:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q81
lem-trf-derived-basis-local-hom-glue
snapshot/lean/Sheaf/AlgebraicGeometry/DerivedBasisLocalHomGlue.lean`

Result: final process exit code 0, captured explicitly after waiting for the
wrapper to finish. The output recorded successful sandbox compilation of
`Sheaf/Stage2/Sandbox0.lean` into its temporary overlay [94.2 s], followed by
successful library compilation of
`Sheaf/AlgebraicGeometry/DerivedBasisLocalHomGlue.lean` [17.8 s]. These are the
wrapper's reported elapsed durations; its progress lines specify a 60-second
limit after slot acquisition for each Lean invocation. No Lean errors or warnings
were emitted. The installed wrapper's source/help explicitly says it now uses
the server side overlay with --wire-confirm; it no longer runs the older
documented local overlay. The initial invocation's progress was insufficient to
establish its final result, so this explicitly completed invocation supplies the
compiler evidence. No lake build, global build, live Lean write, direct SSH command,
claim, delivery or merge was run by the reviewer.

Compiled file SHA-256:
`54927d707dcf75da5767cd4055e78a6178c984c014de77a86ddbfcc5586c54dd`.

Findings and correction:

The mathematics, signature, dependency interfaces and source agreement pass.
The original second-reading section was only a disclaimer, not the required
hypothesis-by-hypothesis reading (H11); it is replaced by this actual independent
reading. The missing recorded compiler outcome is supplied above. Worker-report
text is preserved. No Lean or node change, statement correction or citer audit is
needed. This is a report-only FIX, with the complete replacement report supplied
as lem-trf-derived-basis-local-hom-glue.report.md in the fixes directory.
