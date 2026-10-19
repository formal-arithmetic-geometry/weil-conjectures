## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance` states
`AlgebraicGeometry.Scheme.proEtaleSheaf_topological_invariance`. Its single theorem has
proof `sorry`; it introduces no definitions. The module and theorem docstrings cite
Stacks Tags 09AB and 04DF, and the theorem docstring contains all eight expanded DAG
proof steps, including their named inputs. No statement correction or new node is needed.

Clause-by-clause correspondence:

- Schemes and the given morphism: `{X Y : Scheme.{u}} (r : X ⟶ Y)`.
- Universal homeomorphism: `(hr : (topologically IsHomeomorph).universally r)` is
  exactly the recorded `def-weil-universal-homeomorphism` specialization: every
  pullback square has homeomorphic underlying topological map. This does not assume
  that `r` is an isomorphism, finite, or weakly etale.
- Small pro-etale sites and compatible sizes: `ProEt.topology X` on `X.ProEt` and
  `ProEt.topology Y` on `Y.ProEt`. Site objects are in universe `u+1`, morphisms in
  universe `u`, and set values in `Type (u+1)`, with the same size choices on both
  sides. This is the size convention of the recorded inverse-image declaration.
- The specified inverse/direct image adjunction: `proEtaleSheafAdjunction r
  (Type (u + 1))`. Its left functor is `proEtaleSheafInverseImage r (Type (u + 1))`,
  the left Kan extension followed by sheafification; its right functor is
  `proEtaleSheafDirectImage r (Type (u + 1))`, evaluation after base change.
- The two functors are equivalences: the first two conjuncts are precisely
  `(proEtaleSheafInverseImage r (Type (u + 1))).IsEquivalence` and
  `(proEtaleSheafDirectImage r (Type (u + 1))).IsEquivalence`.
- For every set sheaf `F` on `Y`, the third conjunct quantifies
  `F : Sheaf (ProEt.topology Y) (Type (u + 1))` and states
  `IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).unit.app F)`.
  Its type is exactly `F ⟶ r_* r⁻¹ F`.
- For every set sheaf `G` on `X`, the fourth conjunct quantifies
  `G : Sheaf (ProEt.topology X) (Type (u + 1))` and states
  `IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).counit.app G)`.
  Its type is exactly `r⁻¹ r_* G ⟶ G`.
- These are the actual unit and counit of the specified adjunction; invertibility
  gives the quasi-inverse compatibility, including the triangle identities already
  carried by that adjunction. No arbitrary equivalence or composite isomorphism is used.

Statement dependencies read and used:

- `def-weil-universal-homeomorphism`: `CategoryTheory.MorphismProperty.universally`
  (`Mathlib.CategoryTheory.MorphismProperty.Limits`), `AlgebraicGeometry.topologically`
  (`Mathlib.AlgebraicGeometry.Morphisms.Constructors`), and `IsHomeomorph`
  (`Mathlib.Topology.Homeomorph.Defs`). Read their full signatures and docstrings;
  these are the dependency record's explicit construction.
- `def-weil-pbc-proetale-site`: import its recorded module
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, whose declaration
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` is built on Mathlib's
  `Scheme.ProEt` and `Scheme.ProEt.topology`. Only its underlying small site is used
  here. Read those site definitions and the recorded declaration; no derived or
  module category is substituted for the set sheaf category.
- `def-weil-proetale-inverse-image`: import its recorded module
  `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`. Its primary declaration
  `sfIntrinsicConstantModuleAdjunction` concerns finite-coefficient modules, but the
  module publicly reexports `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, where
  `proEtaleBaseChange`, `proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`, and
  `proEtaleSheafAdjunction` supply exactly the set-sheaf clause needed here. Read those
  full declarations and their docstrings. The existing record need not be repaired:
  its original arbitrary-ring and site constructions are expressly reexported.

All currently recorded project proof-dependency modules are imported without `public`;
the Mathlib leaf interfaces are also imported for the documented future proof. No known
import cycle requires an omission. The source document `proetale.tex` at
`lemma-thickening` was read: its hypothesis is integral, universally injective,
surjective, equivalent to the node's hypothesis by `morphisms.tex`,
`lemma-universal-homeomorphism` (Tag 04DF). Its conclusion is the two quasi-inverse
pro-etale topos functors. The expanded proof follows the same affine ind-etale basis
route rather than asserting descent of every weakly-etale object as a site object.

Edge cases checked before writing:

- Empty schemes remain allowed. The empty site's empty covers impose the expected
  terminal sheaf category, so neither quantification needs a nonempty-site hypothesis.
- The identity morphism is included with its canonical adjunction maps; no separate
  nonidentity or nontriviality assumption occurs.
- Nilpotent thickenings and purely inseparable field extensions are included: a
  universal homeomorphism need not be an isomorphism of schemes or weakly etale.
- Integral non-finite universal homeomorphisms remain included; no finite-type,
  quasi-compact scheme, Noetherian, or quasi-separated hypothesis has been added.
- Both sites and sheaf values use the compatible recorded size convention; all
  variables and universes are explicitly bound, and `autoImplicit` is disabled.

Searches for an exact existing statement:

- `msearch.py leanfinder`, query "A universal homeomorphism of schemes induces an
  equivalence of small pro-etale sheaves of sets": 8 hits, all etale-site definitions
  or related ingredients; no matching set-valued pro-etale invariance theorem.
- `msearch.py loogle`, query `"proetaleTopology", "IsEquivalence"`: 0 hits.
- `msearch.py grep`, query `universalHomeomorph|universal_homeomorph|thickening`,
  subdirectory `AlgebraicGeometry`: one unrelated formally-unramified thickening hit.
- `msearch.py leansearch`, query "A universal homeomorphism induces an equivalence
  on the small pro-etale topos": 8 hits concerning topological presheaves,
  homeomorphisms of schemes, and the small etale topology; no match.
- `rg` searches in upstream `WeilConjectures/AlgebraicGeometry`,
  `WeilConjectures/SixFunctors/ProEtale`, and project `lean/Sheaf/AlgebraicGeometry`
  for topological invariance, universal-homeomorphism names, and this blueprint ID;
  the exact blueprint ID has no upstream declaration. Read both available copies of
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.TopologicalInvariance`:
  `isEquivalence_lowerStar_of_isUniversalHomeomorphism` and its upper-star corollary
  require `[Abelian A] [IsGrothendieckAbelian A]`, so cannot apply to sheaves of sets.
  Existing derived/module invariance statements also concern different categories.
- Searched the proposed full declaration name in `dag/lean_names_upstream.json`,
  `lean/Sheaf`, and upstream `WeilConjectures`: no duplicate.

No `STATEMENT-DISPUTED` issue was found. No source or target statement changed.

Validation: `scompile.py NC lem-trf-proetale-topological-invariance` compiled the
sandbox file and the library module cleanly (2.1 s and 2.4 s respectively), with
no errors or warnings. The prescribed delivery dry run is the remaining check. No direct Git operation, live edit,
local Lake command, global build, or push is performed by this worker.

## Second reading by NC

Independent second reading, 2026-10-17. I opened the sandbox node and module, the
three statement-dependency records and their actual declarations, the Stacks source,
and both upstream copies of the potentially overlapping invariance theorem. No
repair note for this item is present. There are no new nodes or dependency modules
in this delivery, and no statement_change requiring a citer audit.

Source first: proetale.tex, lemma-thickening (Tag 09AB), assumes precisely an integral,
universally injective, surjective morphism of schemes and concludes that its actual
direct and inverse images are quasi-inverse equivalences. The surrounding
section-morphism constructs these functors for arbitrary scheme morphisms. The
quasi-compact/quasi-separated assumptions in the following comparison lemma belong
to that lemma, not this result. In morphisms.tex, definition-universal-homeomorphism
and lemma-universal-homeomorphism (Tags 04DD and 04DF), the source explicitly identifies
this hypothesis with the universal-homeomorphism hypothesis used by our node.

My object/hypothesis/conclusion checklist against the Lean signature:

1. Arbitrary schemes X and Y and the given morphism r: rendered by
   `{X Y : Scheme.{u}} (r : X ⟶ Y)`. PASS: no field, base, finiteness, separation,
   Noetherian, or nonemptiness assumption has entered the signature.
2. Every base change of r is a homeomorphism: rendered by
   `(hr : (topologically IsHomeomorph).universally r)`. PASS: I read
   MorphismProperty.universally in Mathlib/CategoryTheory/MorphismProperty/Limits.lean,
   topologically in AlgebraicGeometry/Morphisms/Constructors.lean, and IsHomeomorph
   in Topology/Homeomorph/Defs.lean. They quantify over every pullback square of
   schemes and assert a continuous, open, bijective underlying map. This is exactly
   def-weil-universal-homeomorphism, including Tag 04DF's equivalent source hypothesis.
3. Compatible small pro-etale sites: rendered by `ProEt.topology X` and
   `ProEt.topology Y` on `X.ProEt` and `Y.ProEt`. PASS: I read the recorded
   proEtaleDerivedCategory declaration and Mathlib's Sites/Proetale.lean definitions.
   ProEt is the category of weakly etale schemes over the base, with all base
   morphisms, and its precoverage is the weakly-etale fpqc precoverage pulled back
   along the forgetful functor. No derived category or coefficient-module category
   replaces the site or its set sheaves here.
4. The induced inverse/direct image adjunction: rendered by
   `proEtaleSheafInverseImage r (Type (u + 1))`,
   `proEtaleSheafDirectImage r (Type (u + 1))`, and
   `proEtaleSheafAdjunction r (Type (u + 1))`. PASS: I read all three definitions
   in ProEtaleInverseImage.lean, proEtaleBaseChange, the upstream lowerStar body,
   and Mathlib's sheafPullbackConstruction definitions in Sites/Pullback.lean.
   Base change is the chosen fibre product (variable factor first); direct image
   is precomposition, inverse image is left Kan extension followed by sheafification,
   and the adjunction is constructed from those functors. The recorded
   SfIntrinsicRealizationTransport module publicly reexports this interface through
   its dependency chain; its own finite-module adjunction is not used instead.
5. These functors are quasi-inverse equivalences: rendered by the first and second
   conjuncts, respectively their `IsEquivalence` assertions. PASS: together with the
   specified adjunction and its invertible components below, these are precisely the
   quasi-inverse pair in the node, with no arbitrary equivalence supplied as input.
6. For every set sheaf F on Y, the specified unit F to r_* r^{-1} F is invertible:
   rendered by the third conjunct, `∀ F : Sheaf (ProEt.topology Y) (Type (u + 1)),
   IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).unit.app F)`. PASS: the domain,
   codomain, quantifier, and actual unit all agree with the node.
7. For every set sheaf G on X, the specified counit r^{-1} r_* G to G is invertible:
   rendered by the fourth conjunct, with `G : Sheaf (ProEt.topology X)
   (Type (u + 1))` and `.counit.app G`. PASS: orientation and quantifier agree.
   The two universal quantifications are independent, as in the node; the given
   adjunction already supplies naturality and both triangle identities.

Edge cases: X and Y may be empty (a universal homeomorphism makes them empty
simultaneously); the site's empty covers are retained, with no inhabited hypothesis.
The identity is covered with its constructed adjunction. Nilpotent thickenings,
purely inseparable field extensions in arbitrary characteristic, and integral
universal homeomorphisms that are not finite are covered. No n, index set, coefficient
ring, or zero module is introduced by this theorem, so no n=0 or zero-ring case is
excluded. The empty basis cover in proof step 5 is explicitly retained. The scheme
universe u is arbitrary; site objects are in u+1 and morphisms in u, and set values
are in u+1, exactly the recorded compatible-size convention. There is no independent
smaller test universe or imposed equality of object and morphism universes.

Independent H4 searches, using different wording from the first reader:

- `msearch.py leanfinder`: "Integral radicial surjective scheme morphism induces
  equivalence of sheaves of sets on the pro-etale sites" returned eight etale-site
  and formally-unramified ingredients, no matching statement.
- `msearch.py loogle`: `"ProEt", "IsEquivalence"` returned zero hits.
- `msearch.py leansearch`: "The direct image and inverse image on sheaves of sets
  for an integral radicial surjective morphism are equivalences on the proetale
  topos" returned eight generic sheaf-equivalence/local-surjectivity results,
  including DenseSubsite and sheafCongr; no scheme-specific invariance theorem.
- Independent `rg` searches for pro-etale invariance/equivalence in upstream
  WeilConjectures, the exact shared lean/WeilConjectures framework, lean/Sheaf,
  and Mathlib's AlgebraicGeometry and CategoryTheory/Sites directories located the
  upstream TopologicalInvariance theorem and the project's isomorphism-only
  ProEtaleIsomorphismInverseImage statements. I opened the upstream declarations:
  isEquivalence_lowerStar_of_isUniversalHomeomorphism and its upperStar corollary
  require `[Abelian A] [IsGrothendieckAbelian A]`, excluding sets. The latter project
  statements require `[IsIso f]`, excluding general universal homeomorphisms.
  Neither is an exact existing match. Searching the proposed declaration and the
  blueprint ID in dag/lean_names_upstream.json, lean/Sheaf, and upstream
  WeilConjectures found no duplicate.

H5-H9: this delivery has no definitions and exactly one postponed named theorem,
whose proof remains `sorry`. Its module and theorem docstrings cite Tags 09AB/04DF
and this blueprint ID. I compared the eight proof paragraphs with the DAG proof:
all steps and their named inputs are carried over, including preservation/reflection
of arbitrary basis covering families and localization of the actual adjunction maps.
The imports include the recorded statement modules and the available proof modules;
proof-only imports are not public. There is no file-local notation, private copy,
local instance, hidden let/show binder, or unbound universe/variable. The namespace
and topic path follow the contract; the longest Lean line has 96 characters.

Mismatches found: none. Changes: only this independent second-reading report;
the Lean statement, definitions, dependencies, and natural statement were correct
and were left intact. The node's lean.statement is verbatim equal to the theorem
signature before `:= by`.

Validation: the prescribed scompile.py invocation with the absolute sandbox file
passed both its sandbox check (1.7 seconds) and library-path check (1.9 seconds),
with no errors or warnings, under the wrapper's normal 60-second limits. No direct
Git command, live-source modification, Lake build, or prohibited local preflight
was run. The required deliver2.py server preflight and delivery follow this reading.
