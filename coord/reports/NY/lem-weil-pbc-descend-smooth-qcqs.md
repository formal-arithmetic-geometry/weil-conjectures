## Worker report

The module `Sheaf.AlgebraicGeometry.DescendSmoothQcqs` states
`AlgebraicGeometry.exists_eventually_smooth_of_isLimit_qcqs`, with its only proof `sorry`.
It is the full qcqs descent statement, including smoothness at all later stages.
No node correction, new definition or dependency module is needed.

Source read: `literature/stacks-project/limits.tex`, lines 1738–1747
(Situation 081D) and 1930–1947 (Tag 0C0C, lemma-descend-smooth).
The situation explicitly assumes S₀, X₀, Y₀ quasi-compact and quasi-separated;
the lemma assumes only local finite presentation of f₀ and smoothness of its limit
base change. Its eventual persistence is the smooth base-change clause of Tag 01VB,
as recorded in the item's seventh proof step.

Clause-by-clause rendering:

- The nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. A preorder admits every directed partially
  ordered set, with no countability or linear-order restriction.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. The affine-transition instance quantifies
  over every arrow `a : i ⟶ j`. Index and scheme universes agree with the established
  limit declaration and the project's index-universe rule.
- `c : Cone D` and `_hc : IsLimit c` express S = lim Sᵢ with all its projections;
  S is `c.pt`. This is arbitrary limiting data, rather than a distinguished limit.
- `i₀ : I` is the fixed original stage. `CompactSpace (D.obj (op i₀))` and
  `QuasiSeparatedSpace (D.obj (op i₀))` give exactly its two topological properties.
- `X₀ Y₀ : Over (D.obj (op i₀))` are schemes with specified structure maps to S₀.
  `f₀ : X₀ ⟶ Y₀` includes precisely the equation of an S₀-morphism.
- `CompactSpace X₀.left`, `QuasiSeparatedSpace X₀.left`, and the corresponding
  two instances for Y₀ are quasi-compactness and quasi-separatedness of the schemes
  themselves, as in Situation 081D; these are not finite type conditions on their
  structure maps.
- `LocallyOfFinitePresentation f₀.left` is the stipulated local finite presentation.
- `_hf : Smooth (((Over.pullback (c.π.app (op i₀))).map f₀).left)` is smoothness of
  the base change f over S. The functor's objects are the chosen fibre products
  X₀ ×[S₀] S and Y₀ ×[S₀] S, and its map is their canonical induced morphism.
- `∃ (i : I) (hi : i₀ ≤ i)` expresses the eventual stage above i₀.
  `∀ (j : I) (hij : i ≤ j), Smooth ...` asserts smoothness at every later j,
  including j = i. `D.map (homOfLE (hi.trans hij)).op` is Sⱼ → S₀, so the
  displayed `Over.pullback` map is exactly fⱼ.
- There is no Noetherian, affineness-of-stages, surjectivity, nonempty-scheme,
  characteristic or extra finite presentation hypothesis.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (Scheme.lean:36–44, 73–75).
- `def-weil-pbc-scheme-conventions` has a convention-only record with no module.
  Its relevant notions are Mathlib `CompactSpace` and `QuasiSeparatedSpace`,
  as also fixed by the quasi-compact-scheme proof dependency.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom` (Affine.lean:44–48).
- `lem-weil-pbc-limit-affine-transition`: `Sheaf.AlgebraicGeometry.LimitAffineTransition`,
  `AlgebraicGeometry.exists_limit_affine_transition`; the complete module and
  signature were read. Its cone/IsLimit form is used here without introducing a
  second inverse-limit construction or assuming Noetherian stages.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation` (FinitePresentation.lean:41–48).
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.map` (lines 89–128, 260–275).
  The existing `CategoryTheory.Over.pullback` in
  `Mathlib.CategoryTheory.Comma.Over.Pullback` (lines 59–70) packages these fibre
  products and their induced map, with no substitute definition.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` (Smooth.lean:59–68). The dependency record is usable:
  it names Smooth, and its note gives the equivalence with the node's formal
  smoothness definition via Stacks 02H6. Search services use the deprecated IsSmooth
  name; the actual pinned source uses Smooth.

All recorded proof-dependency modules are imported: the existing ring-pushout descent
module, Proper for proper base change, Smooth for smooth restrictions/locality/affine
criterion, Limits for finite affine coproducts, OpenImmersion for factorization,
Smooth.Basic for smooth-algebra base change, Filter for compactness, and
LimitAffineTransition for the limit. AffineScheme, Pullbacks, FinitePresentation,
Basic, RingHomProperties and Affine are already transitively imported by the public
statement imports. The seven-step natural-language proof is included in the theorem
docstring, naming every node used by the original proof.

Edge cases checked against the statement and source: X₀ empty (the finite affine
cover can be empty, with i₀ retained in the common-upper-bound set); Y₀ or S₀ empty
(the Over data then impose only the legitimate maps from the empty schemes);
a singleton directed set (the conclusion includes the original index); j = i;
unbounded/infinite directed systems; non-Noetherian qcqs stages; zero rings/empty
affine charts. No intersection of affine opens is assumed affine.

Searches actually run:

- msearch leanfinder: "Smoothness descends to a stage of an inverse limit of quasi
  compact quasi separated schemes with affine transition maps": eight smoothness
  definition/chart results, no matching descent theorem.
- msearch loogle: "AlgebraicGeometry.Smooth, CategoryTheory.Limits.IsLimit": zero hits.
- msearch grep: "smooth.*(limit|stage)|descend.*smooth" in AlgebraicGeometry:
  only two LocalFlatDescent instances (flat surjective descent), not limit descent.
- msearch leansearch: "Smoothness descends along inverse limits of qcqs schemes with
  affine transition morphisms": unavailable, service Internal Server Error.
- rg on the project's `lean/Sheaf/AlgebraicGeometry` and upstream
  `WeilConjectures` for `descend.*[Ss]mooth|[Ss]mooth.*(descend|limit)`:
  inspected AffineDiagramSmoothStage and AffineLimitSmoothStage in full. The former
  requires affine stages and affine original source/target; the latter assumes all
  stages Noetherian and treats a map to the base. Neither gives this arbitrary-qcqs
  statement. Upstream hits are flat/surjective or field-extension descent and
  smooth base-change cohomology, not this statement.
- rg for the item id in upstream WeilConjectures, project Lean and
  `dag/lean_names_upstream.json`: no match. rg for the chosen declaration name in
  Mathlib, upstream WeilConjectures and project Lean: no match.

Validation: server compilation and delivery preflight are run with the prescribed
`scompile.py` and `deliver2.py --no-push`; the second reader supplies the independent
reading and delivery. No local Lean compilation or library build is used.

## Second reading by NY

Independent reading against the original node, the delivered file, Stacks
limits.tex Situation 081D (situation-descent-property), Tag 0C0C
(lemma-descend-smooth), and morphisms.tex Tag 01VB
(lemma-base-change-smooth). The source situation imposes qcqs on S₀, X₀ and Y₀;
the lemma imposes local finite presentation of f₀ and smoothness after limit
base change. Base-change stability gives exactly the all-later strengthening
already stated in this node. No node correction is necessary.

Object/hypothesis/conclusion checklist (each verdict: matches):

1. A nonempty directed indexing set: `{I : Type u} [Preorder I]
   [IsDirected I (· ≤ ·)] [Nonempty I]`. Preorders include directed posets and
   do not impose linearity, finiteness, countability or a top element.
2. An inverse system of schemes: `(D : Iᵒᵖ ⥤ Scheme.{u})`.
   The instance `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`
   says every transition is affine, not that every stage is affine.
3. The scheme limit with its projections: `(c : Cone D) (_hc : IsLimit c)`;
   S is c.pt and S → S₀ is c.π.app (op i₀). This is the categorical limit
   in the dependency, with arbitrary choice of limiting cone allowed.
4. The original index: `(i₀ : I)`; the instances
   `[CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]`
   state exactly that S₀ is qcqs, not Noetherian.
5. Two schemes over S₀: `(X₀ Y₀ : Over (D.obj (op i₀)))` includes both
   structure maps. `(f₀ : X₀ ⟶ Y₀)` includes their required compatibility.
6. X₀ qcqs: `[CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]`.
   Y₀ qcqs: `[CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]`.
   These properties concern the schemes themselves, as in Situation 081D.
7. Local finite presentation: `[LocallyOfFinitePresentation f₀.left]`.
   No stronger finite-type or global-presentation assumption is inserted.
8. Limit base change f is smooth:
   `_hf : Smooth (((Over.pullback (c.π.app (op i₀))).map f₀).left)`.
   Reading Over.pullback shows its objects are pullback.snd g.hom f and
   its map is the universal pullback.lift induced by the original map.
   Thus this is the actual morphism X₀ ×[S₀] S → Y₀ ×[S₀] S.
9. A sufficiently late index: `∃ (i : I) (hi : i₀ ≤ i)`.
10. Every later base change is smooth: `∀ (j : I) (hij : i ≤ j),
    Smooth (((Over.pullback (D.map (homOfLE (hi.trans hij)).op)).map f₀).left)`.
    Here homOfLE (hi.trans hij) goes i₀ → j, its opposite goes op j → op i₀,
    and D.map is Sⱼ → S₀. The quantifier order is exactly the node's;
    j = i is included. No extra clause or identity is appended.

Dependency signatures actually opened: Mathlib Scheme and Scheme.Hom;
IsAffineHom (affine inverse images); LocallyOfFinitePresentation
(finite presentation on affine chart ring maps); Smooth (smooth chart ring
maps); pullback, pullback.fst and pullback.snd; Over.pullback (its obj and map
implementations); and the complete existing LimitAffineTransition module,
including exists_limit_affine_transition and its cone/IsLimit signature.
The scheme-conventions dependency fixes no extra object. QuasiSeparatedSpace
is the quasi-separated topology of a scheme (the affine-intersection criterion
and terminal-morphism equivalence are in Morphisms.QuasiSeparated), and
CompactSpace is quasi-compactness without a Hausdorff assumption. Smooth is
the dependency's recorded notion by the Stacks 02H6 equivalence. These
signatures require no missing auxiliary definition or additional instance.

Edge cases: I empty is intentionally excluded by both source and node;
Nonempty I introduces no restriction beyond them (i₀ already witnesses it).
Singleton systems and j = i are included. Empty X₀ is allowed and the proof's
finite chart family may be empty; keeping i₀ in the upper-bound set handles it.
Empty Y₀ or S₀ impose only the genuine restrictions from the structure maps.
The zero ring and empty affine charts are permitted. There is no characteristic,
field, dimension n, nonzero-object, surjectivity or nonempty-scheme assumption.
Arbitrary universe u is bound explicitly; I and Scheme use the same u as the
recorded inverse-limit declaration and the project's limit-index convention.
There is no independent smaller test-scheme universe and no unbound variable.

Independent searches:

- msearch leanfinder: "A locally finitely presented map between quasi compact
  quasi separated schemes becomes smooth after pullback to an inverse limit,
  hence is smooth at some finite stage". Eight hits, all smoothness definitions
  and chart criteria, no matching limit-descent theorem.
- msearch loogle: `AlgebraicGeometry.Smooth, CategoryTheory.Over.pullback`:
  zero hits.
- msearch grep: `eventually.*[Ss]mooth|[Ss]mooth.*isLimit|exists_smooth_stage`:
  only unrelated analysis hits in its index. This was supplemented by direct rg.
- Direct rg using `smooth.*(islimit|eventually|inverse.limit)` and
  `(descent|descend|limit).*smooth`, case insensitive, on pinned Mathlib
  AlgebraicGeometry, upstream WeilConjectures, and project lean/Sheaf.
  Read AffineDiagramSmoothStage, AffineSourceLimitSmoothStage,
  AffineLimitSmoothStage, and NoetherianApproximationSmoothStage, not just names:
  the first requires affine stages and affine original source and target;
  the others require Noetherian stages or a NoetherianApproximation and treat
  morphisms to that base. None is this arbitrary-qcqs statement for a morphism
  between two models. Mathlib LocalFlatDescent is flat-surjective descent,
  not inverse-limit descent. No exact existing declaration was found.

H4/H12/H13: one existing definition per notion; no new definitions, new nodes,
or dependency modules in this delivery, and no missing notion found. H5/H6:
the module has no data definitions or private copies and its single theorem
has exactly the permitted sorry proof. H8: both docstrings identify the source
and blueprint; the theorem docstring follows all seven node proof steps with
their dependency ids, including empty covers and later-stage persistence.
H9: imports cover the statement and recorded proof dependencies, namespace
AlgebraicGeometry is upstream-compatible, every line is at most 100 characters.
The node's lean.statement was checked programmatically to be verbatim equal to
the file signature; all other node fields equal the repository node.

Mismatches found: none. Changes: only this independent second-reading report;
the correct Lean module and node record are retained without rewriting.

Validation: prescribed scompile.py on the server succeeded, 1.4 seconds,
nice 19, two threads, 60-second per-file limit, with no errors or warnings.
There is exactly one delivered Lean file and it was compiled. Delivery dry run
and final delivery are performed after this reading.
