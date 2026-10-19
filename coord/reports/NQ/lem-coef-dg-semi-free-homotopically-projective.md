## Worker report

Item: `lem-coef-dg-semi-free-homotopically-projective` (NQ, stage 2).
Module: `Sheaf.CategoryTheory.SemiFreeDGModule`.
Main declaration:
`CategoryTheory.IntegralDGCategory.RightModule.isHomotopicallyProjective_of_isSemiFree`.

The module states exactly that every semi-free right dg module over a small dg category
 over the integers is homotopically projective. Its only theorem has proof `sorry`.
The auxiliary structures and definitions implement the conventions introduced in the
node's own statement; they do not state another DAG node. Every definition has real data.
All declarations are listed in `lean.declarations` and have source/blueprint docstrings.
There are no new nodes, dependency modules, or statement corrections.

Source reading: Drinfeld, *DG quotients of DG categories*, arXiv:math/0210114,
§14.8 (printed pp. 36–37), together with §§13.1–13.2(iii), and the right-module
conventions of §14.1. Read the PDF, including the extension-of-homotopies proof in
§13.2(iii). Also read `literature/stacks-project/dga.tex`, section P-resolutions,
labels `lemma-property-P-sequence` and `lemma-property-P-K-projective` (Tag 09KM).
The theorem docstring gives the induction on the filtration in every Hom degree,
including compatibility of the primitives and passage to the exhaustive union.

Hypothesis and clause correspondence:

- Size convention: explicit universes `u v w`; `B.Obj : Type u`, mapping complexes
  in `AddCommGrpCat.{v}`, module values in `AddCommGrpCat.{w}`. Test modules have the
  same fixed coefficient universe as `P`; this is the enlarged module universe of
  the node. Cell sets live in `Type (max u v w)`, so are arbitrary sets in the common
  chosen bound, including empty and infinite sets. No object/morphism/module
  universe equality, smallness hypothesis, or boundedness hypothesis is imposed.
- A small dg category over integers: `IntegralDGCategory.Obj`, `.hom`, `.comp`,
  `.unit`, `.d_unit`, `.unit_comp`, `.comp_unit`, `.assoc`, and `.d_comp`.
  Two nested additive homomorphisms implement a Z-bilinear tensor-product map;
  the last field is precisely its chain-map (Leibniz) equation with Koszul sign.
  `HEq` in the unit/associativity laws only identifies equal integer degrees;
  it does not discard any equation on elements.
- Cochain differential of degree one and square zero: each complex is Mathlib's
  `CochainComplex AddCommGrpCat ℤ`, i.e. `HomologicalComplex` with shape `up ℤ`.
  Its existing shape and `d_comp_d` axioms give precisely these requirements.
- Right module values and unital associative chain-map actions: `RightModule.val`,
  `.act`, `.act_unit`, `.act_assoc`, and `.d_act`. The tensor factors are in the
  stated order, module element first. No sign is inserted in the right action.
- Cohomology `ker d / im d`: the existing `HomologicalComplex.homology` of these
  abelian-group complexes. No competing construction of ordinary cohomology is
  introduced. `RightModule.IsAcyclic` is `∀ U, (N.val U).Acyclic`, using Mathlib's
  `HomologicalComplex.Acyclic`, equivalently exactness in every degree or zero
  cohomology. This is the usual every-cycle-is-a-boundary condition for groups.
- Objectwise quasi-isomorphism: `RightModule.IsObjectwiseQuasiIso` uses Mathlib's
  `QuasiIso` at every object. A dg module map is a closed degree-zero `GradedMap`;
  `HomComplex.Cocycle.mk` and `.homOf` supply its canonical objectwise chain maps.
  Mathlib's `QuasiIso` is isomorphism on all cohomology groups, with no finite-degree
  restriction. This introductory convention is supplied even though not needed
  in the theorem's final implication.
- Representables with composition action: `IntegralDGCategory.representable B T`
  has values `B.hom U T`, action `B.comp`, and exactly the supplied composition laws.
- Shift convention: `cellMap` has the degree-r source
  `⨁ j, (B.hom U (T j)).X (r + n j)`; its j-th generator has degree `-n j`.
  This is exactly `B(-,T j)[n j]^r = B(U,T j)^(r+n j)`.
  The action is the unchanged graded action. The requirement that generator
  differentials lie in the previous stage, together with `.d_act`, gives on the
  quotient `d(x_j a) = (-1)^(-n_j) x_j d(a) = (-1)^(n_j) x_j d(a)`.
  Thus this is the stated shifted differential, including negative and odd shifts.
- Degree-r maps of graded right modules: `GradedMap.val` is a family of Mathlib
  `HomComplex.Cochain` values, and `.action` imposes exactly `f(ma)=f(m)a`.
  `AddEquiv.cast` only transports the equality `(p+r)+q = (p+q)+r`.
- Hom differential: the existing `HomComplex.δ r (r+1)` is used directly.
  Its `δ_v` formula is `d_N f + (-1)^(r+1) f d_P`, hence the stated
  `d_N f - (-1)^r f d_P`. This preserves the displayed graded-action compatibility.
- Homotopical projectivity: `IsHomotopicallyProjective` quantifies over every
  objectwise acyclic `N`, every `r : ℤ`, and every compatible graded map `f`.
  If its Hom differential vanishes, a compatible degree `r-1` map `g` exists
  with `δ g = f` at every object. This is acyclicity of the module-map Hom complex
  in every degree, rather than just degree-zero null-homotopy. The Hom complex is
  specified by its actual cochains and differential, without a second choice of
  ordinary Hom-complex construction or cohomology object.
- Filtration by dg submodules: `DGSubmodule.carrier` is a family of actual
  `AddSubgroup`s of `P` with `.d_mem` and `.act_mem`, and `IsSemiFree` quantifies
  over `F : ℕ → P.DGSubmodule`.
- Starts at zero: its first conjunct is `(F 0).carrier U r = ⊥` for every `U,r`.
- Successive inclusions: the next conjunct is pointwise subgroup inclusion
  `(F i).carrier U r ≤ (F (i+1)).carrier U r`.
- Exhaustiveness: every element of every degree of every `P(U)` lies in some stage.
- Each inclusion is split as a graded module map: `GradedRetraction (F i) (F (i+1))`
  supplies additive component retractions, the left-inverse equation, and the
  graded-action equation. It deliberately requires no chain-map equation.
- Each quotient is dg-isomorphic to an arbitrary coproduct of shifted representables:
  the last conjunct supplies a set `J`, representing objects `T j`, shifts `n j`,
  and lifts `x j` of the free generators in `F_(i+1)`, with differential in `F_i`.
  `cellMap` is the canonical direct-sum map `a ↦ x_j a` with the degree transport.
  Its image is in `F_(i+1)`; every element there is its value modulo `F_i`; and a
  direct-sum element whose value lies in `F_i` is zero. These are exactly the image
  and kernel assertions that its induced map into `F_(i+1)/F_i` is bijective.
  This induced graded map respects actions by associativity and differentials by
  the preceding generator-differential condition, so is a dg-module isomorphism.
  Conversely, given the node's quotient isomorphism, lift the identity generator
  of each representable to obtain these `x j`; its chain-map equation gives their
  differential condition. Therefore the generator presentation adds no assumption
  to semi-freeness. It is not an arbitrary comparison map or a bare chosen object.
- The conclusion: the theorem takes exactly `P` and `hP : P.IsSemiFree` and concludes
  `P.IsHomotopicallyProjective`. No condition of flatness, ordinary projectivity,
  boundedness, finite generation, or nonemptiness appears.

Dependency declarations read and used:

- `def-weil-size-convention` is recorded as `lean.convention = true`, with null
  module and declaration. Its full note says to realize the convention by explicit
  universes. Consequently there is no dependency module to import or missing
  prerequisite to repair. No site, skeleton, or derived category is needed here.
- `Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`: `HomComplex.Cochain`,
  `Cochain.v`, `HomComplex.δ`, `δ_v`, `Cocycle.mk`, `Cocycle.homOf`.
- `Mathlib.Algebra.DirectSum.Basic`: `DirectSum.toAddMonoid`, the direct sum
  of an arbitrarily indexed family of additive groups, not a product.
- `Mathlib.Algebra.Category.Grp.Abelian`: `AddCommGrpCat`'s existing abelian
  structure and hence its canonical cohomology objects.
- `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.
- Existing transitive dependencies include `HomologicalComplex.Acyclic`, `ExactAt`,
  `homology`, `exactAt_iff_isZero_homology`, `AddSubgroup`, `AddEquiv.cast`, and
  `Int.negOnePow`. Their actual source definitions/signatures were inspected.

Edge cases checked mathematically before finalizing:

- `P = 0`: constant zero filtration and empty cell sets satisfy the presentation;
  there are only zero source cochains, so the conclusion is the expected one.
- Empty object set: every objectwise condition is vacuous and the assertion remains
  the correct assertion about the unique empty module.
- `J = ∅`, including an unchanged stage: the direct sum is zero and the image/kernel
  conditions say exactly `F_(i+1) = F_i`.
- Infinite cell sets: finite support in the direct sum implements coproducts, and
  arbitrary component primitives assemble without a finite-generation assumption.
- `r = 0`, positive/negative r, and positive/negative/odd/zero shifts: Hom primitives
  always have degree `r-1`; `Int.negOnePow` handles all integral sign exponents.
- The category's mapping complexes may be unbounded and have torsion or nonprojective
  terms. The proof uses representability and objectwise acyclicity, not projectivity
  of the underlying abelian groups.
- The filtration is indexed by all natural numbers with an arbitrary set of cells at
  each stage. Exhaustiveness is pointwise, so there is no uniform bound on stages.

Searches made, with the prescribed `msearch.py` wrapper (logs in `searches.jsonl`):

- LeanFinder: `Every semi-free right differential graded module over a small dg category
  is homotopically projective` — eight hits, including
  `CochainComplex.IsKProjective`, `HomotopyEquiv.isKProjective`, and ordinary projective
  resolutions; no dg-category actions or semi-free dg modules.
- Loogle: `"CochainComplex.IsKProjective"` — twelve hits about ordinary K-projective
  cochain complexes and their shifts/opposites, no matching theorem.
- Mathlib grep: `semi.?free|homotopically.?projective|[Dd][Gg][Mm]odule|[Dd][Gg][Cc]ategory`
  — zero hits.
- LeanSearch: `Differential graded category right modules semi free filtration representable`
  — eight hits, chiefly `IsModuleFiltration`, ordinary ideal filtrations and filtered
  categories; none carries this notion or theorem.
- `rg` over the upstream `WeilConjectures` source and the project's `lean/Sheaf` and
  `lean/WeilConjectures` using `SemiFree|semi.?free|homotopically.?projective|DGModule|
  DgModule|dgModule|DGCategory|DgCategory` — no hits. The required item-id search in
  upstream `WeilConjectures` also returned no hits.
- Searched `dag/lean_names_upstream.json` and the local Lean trees for the chosen
  declaration names; no collision. Parsed all DAG definition nodes for dg-category,
  dg-module and semi-free notions: none supplies these definitions (the only broad
  incidental match was the unrelated Koszul complex).
- Read Mathlib's `CochainComplex.IsKProjective` signature and docstring: it treats
  ordinary complexes in an abelian category, so cannot serve as this statement.
  Read `CategoryTheory.EnrichedCategory` and `HomologicalComplex.monoidalCategory`:
  the former is the general monoidal enrichment interface, not an existing
  integer dg-category/right-module implementation. The available monoidal structure
  on `AddCommGrpCat` is cartesian, which does not give dg tensor composition.
  The module therefore implements the node's explicit bilinear degreewise convention,
  while reusing the existing complex, additive-group, and Hom-differential definitions.

Validation: `scompile.py NQ lem-coef-dg-semi-free-homotopically-projective` compiled
this file cleanly as a sandbox module and under its final library module name, each
within the unchanged 60-second limit. Final successful run: 46.7 s and 16.4 s,
with no warnings. `autoImplicit` is explicitly false. The bundled dg-category
structure locally disables only `linter.checkUnivs`: its object and morphism universe
parameters necessarily occur under `max` in the type of the bundled structure;
its fields retain the independent levels. No unused-variable linter is disabled.
The text/signature checks also pass, and every line is at most 100 characters.
The required `deliver2.py --no-push` dry run is the last worker check; the independent
second reader writes their own second-reading section and performs delivery.

## Second reading by NQ

I read `dag/nodes/sec-six-functors/lem-coef-dg-semi-free-homotopically-projective.json`
against `Sheaf/CategoryTheory/SemiFreeDGModule.lean` and Drinfeld §14.8 (with
§§13.1–13.2(iii)); the Stacks Tag 09KM statement was also checked. The item is
unchanged and has no statement correction.

The node's objects and hypotheses render as follows, with the verdict after each
item. The universe convention is `universe u v w`,
`IntegralDGCategory.{u,v}`, and `RightModule.{u,v,w}`; `J` is explicitly
`Type (max u v w)`, so the empty, finite, and infinite index cases are retained.

* A small dg category over `ℤ` is `CategoryTheory.IntegralDGCategory`: `Obj`,
  `hom : Obj → Obj → CochainComplex AddCommGrpCat.{v} ℤ`, additive graded
  composition, units, unit laws, associativity, and `d_comp` with the signed
  Leibniz rule. Verdict: exact object and hypotheses; no smallness, boundedness,
  torsion-freeness, or universe equality was added.
* Degree-one cochain differentials and square-zero laws are supplied by each
  `CochainComplex AddCommGrpCat ℤ`; its `ComplexShape.up ℤ` and Mathlib
  `d_comp_d` provide exactly the stated convention. Verdict: exact.
* A right dg module is `IntegralDGCategory.RightModule`, with objectwise `val`,
  action `act` in the order `M(V)` then `B(U,V)`, `act_unit`, `act_assoc`, and
  the signed chain-map equation `d_act`. Verdict: exact right-module direction,
  with no action sign or extra hypothesis.
* Cohomology and acyclicity are represented by Mathlib's homology and
  `RightModule.IsAcyclic := ∀ U, (N.val U).Acyclic`. Verdict: this is precisely
  vanishing of `ker d / im d` in every object and degree.
* Objectwise quasi-isomorphisms are `IsObjectwiseQuasiIso`: a closed degree-zero
  `GradedMap`, converted by `HomComplex.Cocycle.mk` and `Cocycle.homOf`, and
  required to be `QuasiIso` at every object. Verdict: exact introductory clause;
  it is intentionally auxiliary and is not added to the theorem hypotheses.
* The representable `B(-,T)` is `IntegralDGCategory.representable B T`, with
  values `B.hom U T`, composition action, and the supplied unit, associativity,
  and chain-map fields. Verdict: exact representable and action.
* The shift convention is rendered by `cellMap`: its degree-`r` summand is
  `(B.hom U (T j)).X (r + n j)` and the generator is in degree `-n j`.
  `d_act` and the generator condition give the node's `(-1)^n d` quotient
  differential, while the action is unchanged. Verdict: exact, including all
  integer and odd shifts.
* Degree-`r` graded module maps are `RightModule.GradedMap`; `val` is a family
  of `HomComplex.Cochain`s and `action` is exactly `f (ma) = f(m) a`, with only
  the canonical degree cast. Verdict: exact.
* The Hom differential and homotopical projectivity are encoded degreewise by
  `IsHomotopicallyProjective`: for every `N` with `N.IsAcyclic`, every integer
  `r`, and every compatible `f`, a cycle for `HomComplex.δ r (r+1)` has a
  compatible degree `r-1` primitive `g` with `δ g = f`. Verdict: equivalent
  formulation of acyclicity of the displayed graded-action Hom complex, with the
  same quantifier order and no boundedness or projectivity assumption.
* A filtration subobject is `DGSubmodule`, with actual degreewise `AddSubgroup`s,
  differential closure, and action closure. Verdict: exact dg-submodule data.
* A graded split inclusion is `GradedRetraction`: additive retractions on every
  object and degree, left inverse on the smaller submodule, and graded action
  compatibility, with no chain-map requirement. Verdict: exact.
* `IsSemiFree` supplies `F : ℕ → P.DGSubmodule`, `F 0 = ⊥`, successive
  inclusions, pointwise exhaustiveness, graded retractions, and for every stage
  a set `J`, objects `T`, shifts `n`, and generators `x`. The final four clauses
  say the canonical `cellMap` lands in `F (i+1)`, generators have differential in
  `F i`, it is surjective modulo `F i`, and its kernel modulo `F i` is zero.
  Verdict: these are exactly the dg-isomorphism-to-a-coproduct-of-shifted-
  representables clauses in the node; equality of consecutive stages and
  `J = ∅` remain allowed as the node's non-strict inclusions permit.
* The conclusion is the theorem
  `isHomotopicallyProjective_of_isSemiFree {B} (P) (hP : P.IsSemiFree) :
  P.IsHomotopicallyProjective`. Verdict: exactly the node's final implication;
  no condition of flatness, finite generation, boundedness, or nonemptiness is
  present.

The edge cases were checked independently: the zero module has the constant zero
filtration; an empty object type makes objectwise conditions vacuous; an empty cell
set gives an unchanged quotient stage; arbitrary infinite cell sets use finite-support
direct sums; all positive, negative, zero, and odd integer degrees are covered by
`ℤ` and `Int.negOnePow`; and no characteristic, Noetherian, or projectivity
assumption is present. The three universe levels remain independent, and the common
`max` bound for cell indices does not exclude any node case.

The prescribed searches found no existing notion or theorem: LeanFinder semantic
searches, Loogle searches for `CochainComplex.IsKProjective`, LeanSearch, grep of
Mathlib, grep of the upstream `WeilConjectures` tree and project `lean/Sheaf`, and
the DAG/upstream-name searches. Mathlib's `CochainComplex.IsKProjective` was read
and rejected because it concerns ordinary complexes in an abelian category and has
no dg-category action or semi-free filtration. The dependency
`def-weil-size-convention` is a convention node with no Lean declaration to import.

No mismatch was found, so no source, statement, dependency, or module change was
needed. The only deliberate encoding choice is to express the Hom-complex
acyclicity degree by degree rather than bundle a second complex of module maps;
the `δ` equations and quantifiers are definitionally the node's condition. The
module compiles cleanly with the mandated `scompile.py` check and has only the
expected theorem `sorry`.
