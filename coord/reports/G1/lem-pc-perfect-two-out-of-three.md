## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectTwoOutOfThree` states
`AlgebraicGeometry.Scheme.isPerfect_two_out_of_three`, with its sole proof `sorry`.
The node is unchanged except for its Lean record. No missing notions, dependency modules,
or statement correction are needed.

Hypothesis and clause correspondence:

- A scheme X: `(X : Scheme.{u})`, with no quasi-compactness, separation, Noetherian,
  characteristic or affine restriction.
- K, L, M in D(O_X): `(T : Triangle (schemeDerivedCategory X))` has `T.obj₁`,
  `T.obj₂`, and `T.obj₃` as its three objects. The bundled triangle also supplies all
  three arrows, including the arrow from its third object to its first shifted by 1.
  These are objects of the derived category of all module sheaves, not its QCoh subcategory.
- Distinguished triangle: `(hT : T ∈ distTriang _)` uses the canonical derived-category
  distinguished triangles, including precisely the given arrows.
- K and L perfect implies M perfect: the first conjunct
  `IsPerfect X T.obj₁ → IsPerfect X T.obj₂ → IsPerfect X T.obj₃`.
- L and M perfect implies K perfect: the second conjunct
  `IsPerfect X T.obj₂ → IsPerfect X T.obj₃ → IsPerfect X T.obj₁`.
- K and M perfect implies L perfect: the third conjunct
  `IsPerfect X T.obj₁ → IsPerfect X T.obj₃ → IsPerfect X T.obj₂`.
  The conjunction expresses every case of two out of three, including when all three
  are already perfect; it does not require exactly two to be perfect.
- The global and per-open `HasDerivedCategory.{w}` binders are the localization
  structures already required by the recorded definitions, not geometric hypotheses.
  Universes u and w are explicitly declared; no automatically bound variables are used.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (and its recorded
  morphism structure `AlgebraicGeometry.Scheme.Hom` was read).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`;
  its full definition and `IsStrictlyPerfect` were read. This module is the sole import
  and brings the derived category and its triangulated structure transitively.

Edge cases checked before writing: on the empty scheme the pointwise perfectness
condition is vacuous and all three conclusions hold. Zero terms and zero triangles
remain included, as do split triangles and any coinciding terms. Bounded complexes
with zero-length or empty support are allowed by the dependency definition. The three
positions are all included, and no boundedness or quasi-coherence is imposed separately
on the remaining object. The theorem works for arbitrary schemes and the same
universe-parametric module-sheaf carriers and localization structures as its dependencies.

Source checked: the local Stacks cohomology.tex is absent on this machine, so the
actual [Stacks Tag 08CR](https://stacks.math.columbia.edu/tag/08CR) was opened.
Lemma 20.49.7 states two out of three for ringed spaces, hence in particular schemes;
its second proof is the local strictly-perfect mapping-cone argument. The node's
scheme specialization is faithful. The docstring records all three DAG proof steps,
including affine reduction, cone construction and rotations, and local conclusion.

Searches made (2026-10-11):

- msearch.py leanfinder: `perfect complexes of sheaves on a scheme satisfy two out of
  three in distinguished triangles`: eight generic derived-category/triangulated hits,
  including `DerivedCategory.mem_distTriang_iff`; none states this scheme-level result.
- msearch.py loogle: `isPerfect_obj₂_of_distTriang, IsPerfect`: no hits,
  unknown identifier `isPerfect_obj₂_of_distTriang` in Mathlib.
- msearch.py leansearch: `perfect complexes two out of three distinguished triangle`:
  service unavailable, Internal Server Error; no mathematical verdict from this service.
- msearch.py grep: `IsPerfect.*distTriang|distTriang.*IsPerfect`: no Mathlib hits.
- rg on `lean/Sheaf`, Mathlib, and the source library for perfectness and distinguished
  triangles found no scheme-level closure declaration. The source has
  `DerivedCategory.isPerfect_obj₂_of_distTriang` in
  `WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean`; its docstring and full
  signature were read. It concerns `DerivedCategory (ModuleCat R)`, not sheaves on an
  arbitrary scheme, and only directly states the first-and-third case, so is no exact match.
- rg of source `WeilConjectures` for `lem-pc-perfect-two-out-of-three`: no hits.
- rg of `dag/lean_names_upstream.json`, Mathlib, source AlgebraicGeometry, and project
  AlgebraicGeometry for `isPerfect_two_out_of_three` and perfect/distTriang combinations:
  no declaration name collision or exact match.

No STATEMENT-DISPUTED issue was found.

## Second reading by G1

Independent second reader, 2026-10-11. Read the item node, all three
statement-dependency nodes, and their recorded declarations and definitions.
No mismatch was found, so the Lean and node record are preserved.

Object, hypothesis, and conclusion checklist (H3):

1. Scheme X: `(X : Scheme.{u})` uses Mathlib's locally affine locally ringed
   space `AlgebraicGeometry.Scheme`; its declaration and `Scheme.Hom` were opened
   in Mathlib/AlgebraicGeometry/Scheme.lean. PASS: arbitrary scheme, no affine,
   quasi-compact, separated, Noetherian, or field assumption.
2. Three objects K, L, M of D(O_X): `T : Triangle (schemeDerivedCategory X)`
   supplies `T.obj₁`, `T.obj₂`, `T.obj₃`. The dependency's abbreviation is exactly
   `DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))`, with
   Mathlib's shared abelian/category structure. PASS: all module sheaves, with
   no QCoh restriction and no boundedness imposed on the third term.
3. Three arrows K -> L -> M -> K[1]: the bundled `Triangle` supplies them,
   including the connecting morphism and shift. `hT : T ∈ distTriang _`
   requires this very triangle to be distinguished in the canonical derived
   pretriangulated structure (read in DerivedCategory/Basic.lean). PASS:
   bundling quantifies over every choice of objects and arrows.
4. Perfectness: `IsPerfect X` is the recorded Scheme predicate, not the
   different ring-module predicate `DerivedCategory.IsPerfect`. Opened the
   complete definitions in Sheaf/AlgebraicGeometry/PerfectComplex.lean:
   each point has an open neighbourhood with a derived isomorphism to a
   bounded complex whose terms are retracts of finite free module sheaves.
   Its restriction functor is the recorded `SheafOfModules.overFunctor`
   derived functor. PASS: the local definition is the node's open-cover
   definition, including the empty scheme.
5. K and L perfect imply M perfect: first conjunct
   `IsPerfect X T.obj₁ → IsPerfect X T.obj₂ → IsPerfect X T.obj₃`. PASS.
6. L and M perfect imply K perfect: second conjunct
   `IsPerfect X T.obj₂ → IsPerfect X T.obj₃ → IsPerfect X T.obj₁`. PASS.
7. K and M perfect imply L perfect: third conjunct
   `IsPerfect X T.obj₁ → IsPerfect X T.obj₃ → IsPerfect X T.obj₂`. PASS.
8. No other mathematical hypotheses: the two `HasDerivedCategory.{w}`
   binders are exactly those of the dependency definitions, globally and
   for every open. Basic.lean defines this as a chosen localization and
   supplies `HasDerivedCategory.standard` in a sufficiently large universe.
   PASS: these structures select D(O_X) and D(O_U); no extra geometry.
   `u w` are explicitly declared and every term variable is bound.

Source verification: local cohomology.tex is absent. Read the actual Stacks
TeX from https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex
at `lemma-two-out-of-three-perfect`, and the rendered Tag 08CR at
https://stacks.math.columbia.edu/tag/08CR. The source introduces an arbitrary
ringed space and a distinguished triangle, with no additional ambient
hypotheses. The node is its stated scheme specialization. The second proof
uses local strictly perfect representatives, a locally represented chain
map, and its strictly perfect cone. The delivered docstring follows all
three DAG steps: common affine refinement and exact restriction; lifting
and representing the arrow, cone and TR3/triangle-isomorphism comparison,
all three cases through rotations and shifts; local conclusion. The named
sources and blueprint tags are present on both module and theorem.

Edge cases: empty X makes IsPerfect vacuous; an empty open cover therefore
causes no excluded case. Zero objects, zero or split triangles, coincident
terms, all three already perfect, and complexes with empty support remain
allowed. The definition's finite-free rank `m : ℕ` permits m = 0; the
integer bounds permit zero-length support and impose no positive-degree
restriction. There is no index-set binder or characteristic assumption.
Universe u is arbitrary and w is the same localization universe as in both
dependencies; no independently small test-object universe is introduced.

Independent searches (different wording from the first reader):

- msearch LeanSearch: `perfect objects form a triangulated subcategory of
  sheaves of modules`: unavailable, Internal Server Error. Recorded the
  service failure, not a mathematical absence verdict.
- msearch LeanFinder: `cone of a morphism between perfect sheaf complexes
  is perfect`: eight generic cone/homotopy/derived-category hits, including
  DerivedCategory.mem_distTriang_iff; no scheme-perfect closure theorem.
- msearch Loogle: `"perfect", "triangle"`: zero hits.
- msearch grep: `perfect.*cone|cone.*perfect`: only three convex-dual-cone
  comments, unrelated to complexes.
- Direct rg for IsPerfect/isPerfect and perfect/triangle combinations in
  Mathlib Algebra/Homology, AlgebraicGeometry, CategoryTheory, all source
  WeilConjectures, and project lean/Sheaf: no exact existing theorem.
  Opened the source DerivedCategory/Perfect.lean definition and full
  `isPerfect_obj₂_of_distTriang` signature. It is for modules over one
  commutative ring R, not module sheaves over an arbitrary scheme, so it
  cannot replace this item. Other source IsPerfect occurrences concern
  trace-cup pairings, a different notion. Project Scheme.IsPerfect is
  exactly the shared dependency used here.

H4/H5/H6/H9/H12/H13: no duplicate notion, no definitions introduced, no
hollow data, exactly one named theorem with sole proof `sorry`, one needed
import, no new nodes or dependency modules, and no statement correction.
The node's lean.statement was checked byte-for-byte against the theorem
signature before `:= by`; all Lean lines are at most 100 characters.
No mathematical or Lean repair was needed. Added this independent review
and source/search evidence to the report only. Compilation and delivery
preflight are performed using scompile.py and deliver2.py as prescribed.
