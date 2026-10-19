## Worker report

Recovery note: the dispatched sandbox contained only `.brief*` and `.check` markers.
There was no retained Lean module, node copy, report, or second-reading section to
preserve. The previous attempt reported the same missing files. This delivery
reconstructs the statement and records the source comparison explicitly; it does
not claim a missing first-worker artifact was independently read.

The module `Sheaf.AlgebraicGeometry.LisseSplitHomFlatConstructible` states
`AlgebraicGeometry.Scheme.hom_isFlat_constructible_of_etaleLocallySplit`.
Its only theorem proof is `sorry`, as required at stage 2. The helper definition
`etaleConstantCommRingComparison` supplies a canonical coefficient-ring map by
the sheafification adjunction, with real data and no postponed proof. No axiom,
helper theorem, or independent mathematical assumption is introduced. It is a
comparison between existing notions, authorized as an owning-module helper by
the human's missing-canonical-map rule; no independent definition node is needed.
The natural statement and proof of the DAG item are unchanged. The statement
dependency list gains the already landed
`lem-weil-pbc-etale-constant-ring-module-equivalence`, whose concrete restriction
functor transports the existing constructibility predicate to ringed-site modules.

Source read: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-rem-sf-matrix/det-rem-sf-matrix-hom-devissage.proof.md`, Steps 1 and 2.
Step 1 provides locally finite projective terms, Step 2 uses their termwise Hom.
The item's own statement retains precisely a finite commutative coefficient ring
and a Noetherian scheme. No separatedness, finite-type base field, invertibility,
constant-rank, global splitting, or freeness hypothesis is added.
The Stacks sources read for the notions are `sites-modules.tex`,
`definition-flat` (03ER, item 3), and `etale-cohomology.tex`,
`definition-finite-locally-constant` (03RU, module clause),
`definition-constructible` (095E, item 3 and its introductory convention), and
`remark-constant-locally-constant-maps` (03P5). Finite A is Noetherian and its
finite-type modules are finite as sets; U is quasi-compact and quasi-separated,
so the global finite constructible stratification matches the source convention.

The hypotheses and conclusions are matched item by item in the second-reading
section below. The theorem docstring follows all four DAG proof steps, including
the constant matrix refinement, tensor-exactness descent, the original strata
of G, and the image presentation rather than general Hom/pullback commutation.

Dependency declarations read:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology`, `Scheme.ofArrows_mem_smallEtaleTopology_iff`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf` and
  `sheafificationAdjunction` and `toSheafify` (which construct the specified
  coefficient-ring comparison). `constantCommuteCompose` was also read, but the
  final construction does not require its general sheafification-preservation instance.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, a transparent
  abbreviation for Mathlib's actual `SheafOfModules`, not a new category.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`:
  `SheafOfModules.siteSheafTensorRight`, sheafified sectionwise tensor, with
  independent site and coefficient/module universes.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of that tensor functor.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`, using finite strata and finite constant
  module values after etale pullback. Current source read with `scompile.py --source`.
- `WeilConjectures.ConstructibleSheaf.Defs`: `Scheme.Stratification`; and
  `WeilConjectures.Topology.Stratification`: `Topology.Stratification`, including
  `isConstructible_stratum` and no closure-incidence axiom. Reading the inherited
  field resolved an initial concern about the recorded constructibility interface;
  no dependency repair is needed or delivered.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, the actual sheaf of local module-linear maps.
- `WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`:
  `etaleConstantModuleRestriction`, `etaleConstantModuleRestrictionFunctor`,
  `etaleConstantModuleUnitIso`, `etaleConstantModuleCounitIso`, and
  `etaleConstantModuleFunctor_isEquivalence`. Current source, obtained with
  `scompile.py --source`, has `[Ring Λ]` and retains the abelian presheaf.
  Restriction along `etaleConstantCommRingComparison` converts a module over the
  underlying ring sheaf of the constant commutative sheaf to a module over the
  constant ring sheaf expected by this existing functor. The helper is exactly
  the adjoint transpose of the commutative-ring sheafification unit after
  forgetting commutativity. By the adjunction equation, precomposing with the
  constant-ring unit gives the original constant-scalar map. Thus the existing
  restriction recovers precisely the original A-action; neither map is arbitrary.
- Mathlib `SheafOfModules.free` and `SheafOfModules.over` give the finite free
  sheaf and restriction to the localized site. Over an etale V this slice is
  equivalent to the small etale site of V.

Proof-only imports retain the recorded constant-section formula, ringed-topos
flat pullback, exact constant-coefficient inverse image, and conservative
geometric stalks. The geometric-stalk exactness node is a Mathlib leaf, whose
Point.Basic/Skyscraper exactness instances were read in its source record.

Searches performed in this recovery:

1. LeanFinder, via msearch.py: "Internal Hom of an etale locally finite projective
   sheaf with a flat constructible sheaf is flat and constructible". Returned
   condensed internal-projectivity/tensor conditions and `SheafOfModules.isFinitePresentation`;
   none is the etale flat/constructible Hom statement.
2. LeanSearch, via msearch.py: "A sheaf Hom from an etale locally direct summand
   of a finite free constant ring module preserves flatness and constructibility".
   Returned scheme module Hom, ring-map flatness, ordinary module direct-sum
   flatness, and SheafOfModules.Hom constructors; no match.
3. rg in Mathlib's CategoryTheory and Algebra/Category/ModuleCat, the upstream
   WeilConjectures tree, and project lean/Sheaf: `flat.*homObj|homObj.*flat`,
   `constructible.*Hom|Hom.*constructible`, plus "locally projective", "locally
   split", and the intended declaration name. No matching theorem. The generic
   `homObj` construction is used, not redefined. No matching full declaration
   in `dag/lean_names_upstream.json`.
4. Read the nearby DAG candidates `lem-sf-hom-finite-projective`,
   `lem-pc-finite-projective-internal-hom-evaluation`, `thm-sf-hom-ctf`,
   `lem-weil-pbc-flc-dual-stalk`, `lem-sfb-finite-field-internal-hom-finiteness`,
   and `lem-per-dual-lisse-tensor`. They concern evaluation isomorphisms,
   derived categories, dual stalks, or different sites/coefficient fields;
   none states this underived etale flat-constructibility assertion.
5. The helper name `etaleConstantCommRingComparison` was searched by rg in
   Mathlib, the upstream source and lean/Sheaf; no declaration exists. The
   generic `constantCommuteCompose` has an additional sheafification-preservation
   typeclass interface; the direct adjoint transpose supplies only the map needed
   here, using the existing universal property and existing scalar restriction.
   It neither redefines sheaf Hom nor creates another module-sheaf category.

## Second reading by Q53

This section records a fresh node/source/signature check after recovery of the
missing delivery. No earlier review text existed to preserve. The following is
the complete object/hypothesis/conclusion list read from the node, with the Lean
rendering and verdict for each.

1. Finite commutative ring A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
   Exact. This allows the zero ring, products of finite rings, non-fields,
   nilpotents and every characteristic; no Nontrivial or Field instance.
2. Noetherian U, meaning locally Noetherian and quasi-compact:
   `(U : Scheme.{u}) [IsNoetherian U]`. Exact: Mathlib's class extends
   `IsLocallyNoetherian U` and `CompactSpace U`. No separatedness is imposed.
3. Small etale site: `U.smallEtaleTopology` on `U.Etale`. Exact category and
   topology from the recorded dependency, including jointly surjective covers.
4. Constant commutative ring sheaf A_U:
   `(constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)`;
   `sheafCompose ... (forget₂ CommRingCat RingCat)` forgets commutativity so that
   the recorded ringed-site module category can be used. Exact same ring sheaf.
5. E and G sheaves of A_U-modules: the `(E G : SheafOfModules.{u + 1} ...)` binder.
   Exact: this is the Mathlib category recorded by the dependency, with compatible
   scalar restriction maps and module-linear morphisms. The module universe is explicitly u+1.
6. Existence of an etale cover: `_hE : ∃ 𝒰 : Cover.{u} etalePrecoverage U, ...`.
   Exact mathematical condition. It is existential, not a fixed global splitting.
   A cover indexed by a larger set may be reduced to one chosen member per point
   of U, giving an index of size u; existing splitting data restrict to that
   subfamily. Thus the size convention loses no cover, including the empty case.
7. On every cover member V, a possibly varying finite integer t ≥ 0:
   `∀ α : 𝒰.I₀, ∃ t : ℕ`. Exact quantifier order. No positivity or fixed rank.
8. E|V is isomorphic to a direct summand of A_V^t: `E.over (...)`,
   `SheafOfModules.free (R := A_U.over (...)) (ULift.{u + 1} (Fin t))`,
   maps i and p, and `i ≫ p = 𝟙 _`. Exact: a split inclusion/retraction is
   precisely the direct-summand condition in this abelian category. The index
   lift changes only universe, not rank. A_U restricted to V is A_V canonically.
   The equation uses Lean's composition order, so it is p after i, as required.
9. G is flat in the tensor-exactness sense: `_hflat : SheafOfModules.IsFlatOnSite
   (R := ...) G`. Exact dependency, not sectionwise ring-module flatness and
   not a flatness assumption on the scheme.
10. G is constructible: `_hconstructible : IsConstructibleEtaleModuleSheaf ...`.
    Exact existing predicate, applied after the specified canonical coefficient
    restriction. `etaleConstantCommRingComparison U A` has direction from the
    constant RingCat sheaf to the underlying constant CommRingCat sheaf;
    `SheafOfModules.restrictScalars` thus takes G to the correct RingCat sheaf.
    `etaleConstantModuleRestriction U A` then gives its fixed-A-module sheaf.
    These transports preserve the underlying additive sheaf and its A-action.
11. The conclusion concerns the actual internal sheaf Hom:
    `SheafOfModules.homObj E G`. Exact recorded local-linear-map construction,
    not global morphisms, an arbitrary functor or a chosen dual.
12. Flatness of that Hom: first conjunct `SheafOfModules.IsFlatOnSite ...
    (SheafOfModules.homObj E G)`. Exact.
13. Constructibility of that same Hom: second conjunct
    `IsConstructibleEtaleModuleSheaf (etaleConstantModuleRestriction U A
    ((SheafOfModules.restrictScalars ...).obj (SheafOfModules.homObj E G)))`.
    Exact, using the identical canonical coefficient transport as in hypothesis 10.
    The two properties are conjoined, with no omitted or extra conclusion.

Edge cases checked against both source and type: t=0 gives a retraction into
zero and hence E|V=0; E=0 and G=0 give zero Hom; the empty scheme permits an
empty cover and the vacuous finite-stratum condition; the zero ring forces
zero modules and is not excluded. Nonconstant local ranks are permitted.
A product ring such as F_2 × F_2 with its nonfree projective summand is included;
G=Z/2 over Z/4 is correctly excluded when it is nonflat. No characteristic
invertibility is required. No integer n or coefficient level occurs in this
node, so no positive-level constraint is introduced.

Universes: U lives in Scheme.{u}, its small etale site has objects of universe
u+1 and morphisms u, and coefficients/modules have universe u+1. Internal Hom's
output has universe max (u+1) u (u+1) = u+1; no equality of site object and
morphism universes is required. Finite coefficient rings can be lifted to this
universe, with the canonical coefficient action. There is no independent small
universe on an algebra test or a limit index.

H4/H5/H6/H8/H9: searches above exclude an existing exact theorem. All mathematical
notions come from recorded dependency declarations or Mathlib. No new notion,
hollow data, local notation, private abbreviation, local instance, or proved
statement is delivered. The one named theorem has its node's four proof steps
and source/blueprint docstrings. No source-based natural-statement correction
is necessary; no unit statement or citer changes.

Mismatches repaired: the retained sandbox had no deliverable at all. The module,
item node binding and report were reconstructed. The initial Noetherian import
was corrected to `Mathlib.AlgebraicGeometry.Noetherian`. Coefficient and module universes and the sites in flatness/internal Hom were
made explicit to prevent unresolved-site typeclass searches during elaboration.
The existing
constant-ring module equivalence was added to stmt_deps to account explicitly
for the canonical encoding transport. The general `constantCommuteCompose`
instance search still exceeded 60 seconds. It was replaced by the direct
adjoint-transpose comparison definition, with source and blueprint docstrings
and a lean.declarations entry. No mathematical hypothesis was changed.
An initial suspicion about missing
constructible strata in the dependency was resolved by reading the inherited
`Topology.Stratification.isConstructible_stratum`; its recorded interface is
retained, and the redundant project copy is not imported or delivered.

Validation: the final delivered module compiled through scompile.py with exit 0,
no warnings or errors: sandbox 5.4 s, library 4.9 s, each within the unchanged
60-second limit. Diagnostic scratch probes are outside the delivered lean tree.
The node signature is copied verbatim from the final theorem; only lean and the
addition of the landed scalar-equivalence node to stmt_deps differ from the base.
Maximum Lean line width is 95 characters. No variables or universes are unbound.
Server validation: deliver2.py --no-push exited 0 and printed OK; the staged
module compiled and the delivery passed the maintainer preflight. The dry-run
commit was fc589a14f4; nothing was pushed by that check.
