## Worker report

The module `Sheaf.AlgebraicGeometry.PseudoCoherentPointFibreLine` states
`AlgebraicGeometry.AlgebraicSpace.pseudoCoherent_pointFibre_line`, with `sorry`.
No definition, axiom or extra postponed theorem is introduced. The module docstring
and theorem docstring record Tags 0BYP, 0BCC and 08J5 and the five DAG proof steps.
The source statement of `lemma-lift-bounded-pseudo-coherent-to-perfect` was read in
`literature/stacks-project/more-algebra.tex`: its bounded-below hypothesis and the
residue-rank conclusion are retained.

Hypotheses and conclusions, clause by clause:

* An algebraic space over any scheme is `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
  There is no nonemptiness, separation, quasi-compactness or Noetherian assumption.
* The given object of the unbounded derived module category is `E : X.DerivedModules`.
  This is `DerivedCategory X.SmallModules` on the already published equivalent small
  affine etale model, with the actual regular-functions structure sheaf. The equivalence
  `X.smallModuleEquivalence` identifies this with the original small etale module topos.
  `[HasDerivedCategory.{w} X.SmallModules]` selects its localization morphism universe.
* Pseudo-coherence is `hpc : X.IsPseudoCoherent E`, using the existing space predicate,
  not another predicate with the same intended meaning. Its local bounded-above
  finite-free models are exactly the chartwise characterization in the node. On an
  affine chart they are the termwise small-etale realizations of the finite-free ring
  models of `DerivedCategory.IsPseudoCoherent`; etale refinements are allowed by
  "sufficiently small". The original ring definition is publicly imported as well.
* Local boundedness below is `hbelow`: on each small-model object V a covering sieve R
  exists; on each member U there exists an integer a such that `H^n(E)|_U` is zero
  for n<a. Both the cover and a may vary. Slice restriction is the exact
  `SheafOfModules.overFunctor`, applied to `DerivedCategory.homologyFunctor`.
  Refining together the covers in hpc and hbelow gives precisely the simultaneous
  chart condition in the node; no global bound is imposed.
* The integer m is unrestricted: `(m : ℤ)`.
* Every geometric point is quantified by `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`,
  its base map `b : Spec (.of Ω) ⟶ S`, and a morphism
  `x : schemeSpace (Over.mk b) ⟶ X`. Full faithfulness of the Yoneda sheaf identifies
  this with the usual Spec Ω to X point. `hfibre` asserts an isomorphism between
  `(derivedTensorPullback x).obj E` and the point's `derivedStructure⟦m⟧`.
  At an algebraically closed field the small etale module category is Ω-Mod;
  its structure module is Ω. Thus this is exactly Ω[m] in D(Ω), expressed in the
  equivalent ringed-site category without choosing an unnormalized equivalence.
  It is derived tensor pullback, not a fibre of the cohomology sheaf. The point
  localization universe wPoint is independent of w; no universe equality is imposed.
* L is the actual `homologyFunctor ... (-m)` value of E. Transporting it back through
  `X.smallModuleEquivalence.inverse`, the first conclusion is the existing
  `X.IsLineModule`. That predicate requires local structure-module isomorphisms on
  covering sieves of the original small etale site.
* The second conclusion is `Nonempty (E ≅ (singleFunctor ... 0).obj L⟦m⟧)` with
  the small-model L written out, rather than an arbitrary existential line module.
  The shift convention puts its cohomology in degree -m.
* The final conclusion records canonicity rather than just an unspecified isomorphism.
  For every cochain representative P isomorphic to E it asserts invertibility of
  `Q.map (P.ιTruncLE (-m))` and existence of the unique projection j from the
  upper truncation to its single cohomology complex. Its degree -m component is
  prescribed, after `singleObjXSelf`, as `truncLEXIsoCycles.hom ≫ homologyπ`.
  `Q.map j` is invertible. Consequently `(asIso (Q.map inclusion)).symm ≪≫
  asIso (Q.map j)` is exactly the canonical truncation comparison; transporting
  along the representative and the standard homology/single/shift identifications
  gives the preceding isomorphism. This records the two arrows of proof step 5.
  Uniqueness of this chain projection follows because maps to a single complex
  are determined by the indicated component. It imposes no extra hypothesis or
  mathematical conclusion beyond the node's canonical comparison.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, `etalePullback`, `IsLineModule`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the exact alias of `SheafOfModules`, with inherited Mathlib category structures.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`; the existing independent localization-size convention.
* `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent` (bounded-above finite-free representative).
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `SmallEtaleModel`, `smallEtaleModelTopology`, `smallStructureRings`,
  `SmallModules`, `smallModuleEquivalence`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`:
  `DerivedModules`, `derivedStructure`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex`: `IsPseudoCoherent`.
* `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`: `derivedTensorPullback`.
  This is the canonical total left derived functor of ordinary tensor pullback,
  with its universal counit, and has independent source/target localization sizes.
* `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace` uses the actual
  representable fppf sheaf, with only its algebraic-space-property proof postponed.

The five added stmt_deps are all already landed definition nodes: the small ringed
model, derived-module calculus, space pseudo-coherence, derived tensor pullback,
representable scheme space. No new node or dependency replacement is required.
All stated proof-dependency modules are imported without public visibility.
The Mathlib proof matches use `Functor.homologyFunctorIso` and
`DerivedCategory.isIso_iff`, with the appropriate Mathlib modules imported.
`lem-sfb-scheme-etale-module-exact-finiteness-comparison` has no Lean record;
there is consequently no module to import for that proof-only dependency.
The canonical truncation theorem and affine equivalence were read at their
recorded source declarations, as were the residue-model and K-flat restriction
statements. No alternate canonical map is defined here.

Edge cases checked: on the empty space the point condition is vacuous, the module
topos is trivial, its zero module is locally the structure module, and both roof
arrows are invertible. On a nonempty space the zero object does not satisfy hfibre.
For m=0 the line is H^0 and the comparison has no shift. Negative and positive m
use degree -m consistently. Charts may have different lower bounds, and hbelow
allows refinements independently on every chart. No finite-rank assumption on
an unrelated global representative P is present. Arbitrary characteristics are
allowed, and algebraic closures of residue fields remain in the scheme universe u.
No `let`, `show`, private notation or auto-bound variables appear in the signature.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches (msearch.py, group NQ and this item):

* leanfinder: "A pseudo coherent complex locally bounded below with derived geometric
  fibres a shifted line is a shifted line bundle" returned eight hits, including
  `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE` and the IsGE/IsLE
  predicates. These assume concentration and do not recognize rank one from fibres.
* loogle: `DerivedCategory.IsPseudoCoherent, DerivedCategory.singleFunctor` returned
  zero hits (the project pseudo-coherence name is unknown to the Mathlib search).
* grep: `IsPseudoCoherent|IsLineModule` returned zero Mathlib hits.
* leansearch: "pseudo coherent complex geometric fibres shifted line bundle" returned
  eight hits about quasicoherent finite presentation and shifts of complexes, no
  fibre recognition theorem.
* rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `pseudoCoherent_pointFibre_line`, pseudo-coherent/line combinations and the
  exact item id found no existing statement. The broader space searches found the
  pseudo-coherence and derived tensor pullback modules used above. Exact item-id
  `grep -rn` in `lean/WeilConjectures` found no hit.
* Direct Mathlib searches for truncation/single/homology declarations found the
  existing single-complex API; the recorded truncation theorem prescribes precisely
  the cycles-to-cohomology component used here.

Validation: the initial complete statement passed scompile.py (sandbox 12.7 s,
module 2.5 s). The final explicit dependency-import version also passed (sandbox 2.8 s, module
2.5 s), with no warnings or errors. All delivered proofs remain `sorry` as
required in stage 2.

## Second reading by NQ

The dispatch brief forbids starting other agents and states that the maintainer
will independently review this delivery. This section records a separate in-thread
rereading of the node and final signature, not an invented independent worker.

The base S, arbitrary algebraic space X, actual derived module object E, local
pseudo-coherence and local lower bound, all geometric points, and unrestricted m
are present. The two local hypotheses can be put on a common refinement, matching
"sufficiently small etale affine charts". The field's derived module category is
represented by its equivalent small etale ringed model, not by abelian sheaves or
Zariski modules on X. Its regular rank-one structure module is Ω. The degree in
both the line and the projection is -m, while the displayed shift is +m.
The line predicate is applied after the actual inverse module equivalence and is
therefore on the original etale site. The specified truncation projection retains
the quotient from cycles and makes the comparison canonical. Added direct public
imports of all statement-dependency modules after this rereading, so no proof-only
private import supplies a statement dependency accidentally. No missing hypothesis,
strengthened geometric assumption, discarded empty case or weakened conclusion
was found. No new nodes or dependency repair modules occur.
