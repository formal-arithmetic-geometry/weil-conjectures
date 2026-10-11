## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent` states
`AlgebraicGeometry.existsUnique_open_of_etale_fpqc_baseChange`, with only `sorry` as proof.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypotheses and conclusion, clause by clause:
- Schemes S, V and the family T_i: `{S V : Scheme.{u}}`, `{I : Type v}` and
  `(T : I → Scheme.{u})`; the scheme universe and index universe are independent.
- Morphisms g_i:T_i→S: `(g : ∀ i, T i ⟶ S)`.
- Fpqc covering: `hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S`.
  This is exactly the dependency's recorded Mathlib notion, not membership in the
  generated Grothendieck topology. It requires flat arrows and quasi-compact joint coverage.
- Etale V→S: `(f : V ⟶ S) [Etale f]`. The etale hypothesis is retained even though
  compatible-open descent also holds for arbitrary f.
- Opens W_i in T_i×_S V: `W : ∀ i, (pullback (g i) f).Opens`.
- Equal pullbacks for every i,j: `hcompat : ∀ i j, ... = ...`, with inverse images
  along `pullback.fst` and `pullback.snd` of the maps `pullback.snd (g i) f` to V.
  The domain is `(T_i×_S V)×_V(T_j×_S V)`, canonically the node's
  `T_i×_S T_j×_S V`. Both projections give precisely its maps to T_i×_S V and T_j×_S V.
  Using this parenthesization avoids inserting any auxiliary choices or hypotheses.
- Existence and uniqueness of an open of V: `∃! U : V.Opens, ...`.
- Its pullback is W_i for every i: `∀ i, (pullback.snd (g i) f) ⁻¹ᵁ U = W i`.
  Equality is equality of open subsets, as required, rather than a weaker inclusion
  or an isomorphism of unspecified subschemes.

Dependency declarations read and used:
- def-pc-scheme: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme (structure and docstrings read).
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback. The Scheme pullback
  instance is supplied by the imports. Full signatures and docstrings read.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale (class signature and docstring read).
- def-weil-pbc-fpqc-covering: `AlgebraicGeometry.Scheme.fpqcPrecoverage`,
  Mathlib.AlgebraicGeometry.Sites.Fpqc (definition and docstring read), together with
  QuasiCompactCover in Mathlib.AlgebraicGeometry.Cover.QuasiCompact.
These nodes are Mathlib leaves with mathlib_match, so no lean records are required.

Source check: local literature/stacks-project/descent.tex is absent on this machine.
Read https://stacks.math.columbia.edu/tag/03N0 (statement and proof) and
https://stacks.math.columbia.edu/tag/09XN (application to the triple products).
03N0 provides unique compatible-open descent; 09XN applies it to the base change to V.
The theorem docstring records both proof steps and their DAG dependencies.

Edge cases checked: an empty I can only cover an empty S, and a morphism V→empty S
forces V empty; there is then exactly one open, so the conclusion is valid. Empty
components or empty V are allowed. The empty and full opens satisfy the expected
compatibility. No finiteness of I, no nonemptiness, no affine assumption, and no
quasi-compactness of individual g_i is imposed. No disputed statement or node fault found.

Searches performed on 2026-10-11:
- msearch.py leanfinder: "Compatible open subsets on an fpqc covering of schemes descend
  uniquely to an open of the base". Eight hits about gluing and affine transition
  limits, none giving fpqc descent of compatible opens.
- msearch.py loogle: "AlgebraicGeometry.Scheme.fpqcPrecoverage". Eight hits identifying
  the precoverage, its stability instances, and singleton/fppf comparisons; no exact theorem.
- msearch.py grep: "descent.*open|open.*fpqc", AlgebraicGeometry. Three hits on descent
  of universal openness and open immersions in FlatDescent/FlatMono; neither constructs
  the descended open for an arbitrary fpqc family.
- msearch.py leansearch: "fpqc descent of compatible open subsets of schemes".
  Service unavailable (Internal Server Error); no result available.
- rg in WeilConjectures and lean/Sheaf: fpqc, descent.*open, open.*descent and narrowed
  open.*descend|descend.*open. Hits on morphism-property descent, modules and closed
  subschemes, and limit-stage descent of quasi-compact opens; no exact statement.
- rg for the item id in WeilConjectures and dag/lean_names_upstream.json: no hits.
  The chosen declaration name is fresh in Mathlib, WeilConjectures, and lean/Sheaf.

Validation: scompile.py F1 lem-weil-pbc-etale-open-fpqc-descent compiled the module
on the server in 1.8 seconds, with no errors or warnings. All universes and variables
are explicitly bound. Independent second reading is left to the designated second reader.

## Second reading by F1

Independent second reading on 2026-10-11. I opened the node copy, the delivered
module, all four statement-dependency nodes and their Mathlib declarations.
There are no new definition nodes, dependency modules, or statement corrections.

Source: the local Stacks checkout is absent. I read the actual Stacks .tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/descent.tex,
label `lemma-open-fpqc-covering` (Tag 03N0), and etale-cohomology.tex at the
reference `descent-lemma-open-fpqc-covering` (Tag 09XN). I also read the official
pages https://stacks.math.columbia.edu/tag/03N0,
https://stacks.math.columbia.edu/tag/09XN and
https://stacks.math.columbia.edu/tag/022B. Tag 03N0 assumes arbitrary schemes and
an fpqc covering, with no field, characteristic, Noetherian, separation or
finiteness assumption. Tag 09XN applies it to the base change to an etale V.

Object, hypothesis and conclusion checklist, written from the node and then
matched to the signature:

- Base scheme S and scheme V: `{S V : Scheme.{u}}`. PASS: arbitrary schemes,
  using `Scheme`, its `Hom` and `Opens` in Mathlib.AlgebraicGeometry.Scheme.
- Arbitrary index set I, schemes T_i and morphisms g_i:T_i -> S:
  `{I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)`. PASS: no finite or
  nonempty instance; index and scheme universes are independent.
- The family is fpqc: `hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S`.
  PASS: `fpqcPrecoverage` is `propQCPrecoverage @Flat`, and the latter is
  `qcPrecoverage ⊓ Scheme.precoverage @Flat`. I read Sites/QuasiCompact.lean,
  Cover/QuasiCompact.lean and the affine-open finite-refinement lemma
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact`. This is precisely
  the recorded dependency's flat, jointly covering, finite-affine-refinement
  condition (Tag 022B), including repeated indices and n=0. It does not impose
  quasi-compactness on each g_i or replace a covering by a generated sieve.
- The given map V -> S is etale: `(f : V ⟶ S) [Etale f]`. PASS: the Etale class
  in Morphisms/Etale.lean and its `iff_flat_and_formallyUnramified` match the
  dependency's locally finitely presented, flat, unramified notion. The class
  binder retains the node's hypothesis, although descent itself is more general.
- Opens W_i in T_i x_S V: `(W : ∀ i, (pullback (g i) f).Opens)`. PASS:
  `pullback`, `fst`, `snd` and `lift` were read in Pullback/HasPullback.lean;
  the Scheme `HasPullbacks` instance is in AlgebraicGeometry/Pullbacks.lean.
  No additional existence instance is imposed on the caller.
- Compatibility for every ordered pair i,j: `hcompat : ∀ i j, ... = ...`.
  PASS: put p_i = `pullback.snd (g i) f`. Its overlap is
  `pullback p_i p_j`, and the two inverse images are along
  `pullback.fst p_i p_j` and `pullback.snd p_i p_j`. By the fibre-product
  universal property this overlap represents triples (t_i,t_j,v) with equal
  images in S, hence is canonically T_i x_S T_j x_S V, with the required
  projections. Equality of opens is preserved and reflected by this canonical
  isomorphism. This changes no hypothesis or quantifier.
- Existence of an open W of V: `∃! U : V.Opens, ...`. PASS: an actual open
  subset, with no additional affine or quasi-compact requirement.
- Pullback recovers every W_i: `∀ i, (pullback.snd (g i) f) ⁻¹ᵁ U = W i`.
  PASS: the projection targets V, and the equality is exactly inverse-image
  equality of opens. The direction of equality is immaterial.
- Uniqueness of that same open satisfying all equalities: `∃! U` binds U
  before the universal i. PASS: no choice of a separate U for each i and no
  weakening to uniqueness up to an unspecified isomorphism.

Edge cases: empty I is allowed; fpqc coverage then forces S empty and the map
V -> S forces V empty, whose lattice of opens has one element. Empty V,
empty components T_i, and bottom/top W_i are allowed. The finite refinement
condition permits n=0 over the empty affine open. There is no scalar ring,
field, dimension parameter or characteristic restriction. Arbitrarily large
set-indexed families are covered by v; schemes of varying initial sizes can
be taken in any common enlarged universe u. Every universe and variable is
explicitly bound, and there are no hidden caller instances beyond Etale f.

Independent searches (2026-10-11), using different wording from the worker:

- msearch.py leanfinder: "A compatible family of open subsets under faithfully
  flat covering maps is the inverse image of a unique open subset". Eight hits:
  topological open-cover sheaf equivalences, OpenCover.ext_elem and an
  affine-transition-limit construction. None states this scheme-open descent.
- msearch.py leansearch: "Open subsets glue uniquely along a quasi compact flat
  covering of schemes". UNAVAILABLE, Internal Server Error; no verdict is
  inferred from the unavailable service.
- msearch.py grep: `existsUnique.*[Oo]pen|[Oo]pen.*[Dd]escent|[Dd]escent.*[Oo]pen`.
  Hits concern clopens/idempotents, sheaf sections, and morphism-property descent;
  none is the required existence and uniqueness of a descended open.
- Independent rg over Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf:
  `open.*descen|descen.*open|[Ii]s[Ss]heaf.*[Oo]pen|[Oo]pen.*[Ii]s[Ss]heaf`
  and the delivered declaration name. I opened FlatDescent's
  `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`,
  Sheaf/AlgebraicGeometry/Morphisms/FpqcOpenImmersionDescent.lean and the upstream
  EtaleTopologicalInvariance/Descent.lean candidate. These descend a morphism
  property or construct a quasi-affine etale scheme with additional hypotheses;
  they do not give this compatible-open theorem. No exact existing declaration
  or collision with the new declaration name was found.

H5/H6/H8/H9: no definitions, hollow data, auxiliary proofs or private notions.
The only theorem has `by sorry`. Both docstrings identify the node and source;
its proof first base-changes the fpqc cover (Tag 022D), then applies the general
compatible-open theorem (Tag 03N0), with the overlap identification explained.
The node proof informally calls the maps to V "first projections"; for its
written ordering T_i x_S V these are second projections, which the Lean and
its docstring already name correctly. This is only a projection-label slip
in the existing prose, not a fault in the statement or delivered module.
The imports each supply a notion actually used; namespace and topic are correct.
All lines are at most 100 characters. A direct string comparison confirms
`lean.statement` equals the signature verbatim, ending just before `:= by`.

Mismatches and changes: no mismatch in the mathematical statement, dependencies
or delivered Lean was found. No Lean or node repair was needed; only this
independent second-reading section was appended, preserving the Worker report.
Remote scompile.py compilation passed, exit code 0, in 1.7 seconds, with no
errors or warnings.
