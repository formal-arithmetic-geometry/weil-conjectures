## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.SpaceFirstOrderRingedDescription`.
Its sole declaration is
`AlgebraicGeometry.AlgebraicSpace.space_first_order_ringed_description`;
its whole proof is `sorry`. There are no new definitions or postponed helper theorems.
The natural-language statement and accepted proof split are unchanged. The only additional
statement dependency is the already landed `def-sfb-space-square-zero-extension-data`,
whose existing interface is used, not copied.

Sources read: Stacks `spaces-more-morphisms.tex`, Section Thickenings, its fundamental
equivalence, Tags 05ZS, 05ZT and 05ZN (including their proofs). The current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images proof
were also read; this is an inherited supporting lemma, not that unit's own statement.
No repair note exists for this item. The example CompactObject module has been withdrawn;
its node now points to the upstream WeilConjectures module, so the header follows the active data
and realization modules instead.

Hypothesis and clause correspondence:

- The base scheme and all spaces are `{S : Scheme.{u}}` and `AlgebraicSpace S`.
  These are precisely the recorded fppf-sheaf algebraic spaces, not arbitrary ringed
  topoi or scheme-only replacements. All universes are explicit; the small etale site's
  object universe remains `u+1`, its morphisms and the section rings are in `u`, as in
  the dependency declarations. The size-convention node is metatheoretic and has no
  declaration to import.
- A first-order thickening is `IsSpaceFirstOrderThickening i`. Its definition is
  `IsRepresentableWith (fun _ _ p => IsFirstOrderThickening p.left) i.hom.hom`.
  It tests every scheme base change. The reused scheme predicate is a closed immersion
  with `i.ker ^ 2 = ⊥`. Square-zero ideals are nilpotent, so this already forces the
  underlying closed subset to be the whole space; no separate surjectivity assumption
  is omitted. No atlas, nonemptiness or finiteness assumption is added.
- The first conjunct quantifies over every such `i`, and includes compatible structure
  maps `f`, `q` with `i ≫ q = f` so that it also records the canonical base action.
  This parametrization covers the unbased forward assertion: take `B = X'`, `q = 𝟙 X'`
  and `f = i`. It does not require existence of any extra structure on a thickening.
- Its `T : ThickeningOverModel f i q` contains an equivalence
  `X'.EtaleSite ≌ X.EtaleSite`, continuity in both directions, natural reduction
  arrows exhibiting actual scheme pullback squares, and the quotient induced on
  regular functions by these arrows. Thus the equivalence is specifically restriction
  through the thickening. It is not an arbitrary equivalence of categories.
- The forward kernel is `G : X.QCoh`. `A : SpaceSquareZeroExtension f G.obj`
  asserts a commutative ring sheaf, an additive kernel inclusion natural on the site,
  sectionwise injectivity, equality of its image with the quotient kernel, and LOCAL
  surjectivity of the quotient. Thus it is the exact sequence of sheaves specified
  in the node; sectionwise surjectivity, which would be too strong, is not imposed.
  `A.square_zero` gives the zero products of kernel sections. `A.scalar` gives the
  quotient `O_X`-action, and `X.QCoh` is the recorded local-presentation predicate.
- The isomorphism `γ : T.toThickeningSiteModel.rings ≅ A.algebra.obj` identifies this
  extension algebra with the actual transported `O_X'`. The equation
  `γ.hom ≫ A.quotient = T.quotient` identifies its kernel with the ideal of `i`.
  Together with the normalized site model, these are ring SHEAVES on the common site;
  using their underlying presheaf isomorphism does not weaken a sheaf isomorphism.
- In both the forward and converse clauses, the displayed equation for every
  `U`, `V`, `a`, `ha` says the isomorphism respects the `f^{-1}O_B`-algebra action.
  `ChartRingMap` expresses inverse-image ring maps on all compatible pairs of scheme
  charts, natural in both variables. `SpaceSquareZeroExtension.base_quotient` says
  the quotient is an algebra map and reduces to the canonical regular-function map.
  The commutative-algebra convention is exactly the convention of Stacks 05ZT and
  the already reviewed stage-1 proof, not a new restriction of its intended statement.
- The second conjunct takes every morphism `f`, every quasi-coherent kernel `G`, and
  every exact square-zero extension `A`. It concludes existence of `X'`, `i`, `q`,
  the first-order property, `i ≫ q = f`, and the compatible normalized ring isomorphism.
  No algebra splitting, trivial extension, or chosen inverse-image presentation is assumed.
- The third conjunct takes arbitrary two first-order thickenings `i`, `j` of the
  SAME `X`, both over `B`, with their normalized site models `T`, `W`. The input
  `α : W.toThickeningSiteModel.rings ⟶ T.toThickeningSiteModel.rings` is every
  ring-presheaf natural transformation, equivalently every map of their ring sheaves
  on `X_et`. There is no extra locality assumption on `α`.
- `α ≫ T.quotient = W.quotient` is precisely the identity after reduction to `O_X`.
  The quantified base equation is precisely compatibility with the inverse-image base
  algebra structure. Neither kernel is assumed separately quasi-coherent in this clause.
- `∃! g' : X' ⟶ Y'` gives existence AND uniqueness in the opposite direction to `α`.
  `i ≫ g' = j` is restriction to the identity on `X`; `g' ≫ r = q` is being over `B`.
  The final `∀ U, ∃ a'` asserts that every equal reduced chart has a map between its
  two lifted schemes, over `g'`, commuting with reduction, whose regular-function
  pullback equals `α.app (op U)`. These equations say the space morphism induces the
  specified ring map, not merely that some space morphism exists.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `EtaleSite`, `structurePresheaf`,
  `structureSheaf`, `Modules`; full signatures/docstrings read in the source.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; used through the recorded scheme thickening.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent Mathlib `SheafOfModules` specialization. The underlying module
  sheaf and morphism signatures were read in Mathlib as well.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, using
  `SheafOfModules.isQuasicoherent` / `SheafOfModules.IsQuasicoherent` unchanged.
- `Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData`:
  `IsSpaceFirstOrderThickening`, `ThickeningSiteModel`, `ThickeningSiteModel.rings`,
  `ThickeningOverModel`, `SpaceSquareZeroExtension`; the complete module, including
  `ChartRingMap` and all normalization predicates, was read.
- `WeilConjectures.AlgebraicGeometry.Thickening`:
  `AlgebraicGeometry.IsFirstOrderThickening`, through the space thickening predicate.
- Plain proof import: `Sheaf.AlgebraicGeometry.SpaceSquareZeroRingedRealization`,
  `AlgebraicGeometry.AlgebraicSpace.space_square_zero_ringed_realization`.
  Its full signature/docstring were read. It gives realization and general maps, but
  does NOT state the forward quasi-coherent kernel assertion, so is not an exact
  existing match for this item. The other proof dependency,
  `lem-sfb-space-closed-immersion-quasi-coherent-modules`, currently has no `lean`
  record and thus no module to import; its natural-language use remains in the
  proof docstring and the DAG proof dependency, unchanged.

Edge cases checked before writing:

- Identity thickening: the ideal is zero, the site model can be identity, and the
  forward extension has zero kernel; the map clause then forces the identity.
- Empty reduced space: a first-order thickening has the same underlying space, hence
  is empty. Nothing requires a nonempty space or a nonempty family of charts.
- Zero kernel: the formulation allows it; no positive rank or nontrivial ideal is required.
- Affine square-zero quotient `A -> A/I`: the usual module `I`, with `I^2=0`, has
  precisely the quotient action imposed by `scalar`, and all ring-map directions agree.
- Non-affine charts: local quotient surjectivity is retained, avoiding the false global
  sections surjectivity requirement. No characteristic, noetherian or properness
  hypothesis is inserted. Final maps need not be isomorphisms.

Searches (all with the prescribed `batch2/msearch.py Q30 <item>` wrapper):

- LeanFinder: "First order algebraic space thickenings are equivalent to square zero
  extensions of etale structure sheaves with quasi coherent kernels". Eight hits,
  including `Algebra.FormallyEtale.iff_comp_bijective`, scheme etale categories and
  standard-etale lifting. None is the algebraic-space ring-sheaf statement.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, CategoryTheory.Equivalence`.
  One hit: `IsClosedImmersion.overEquivIdealSheafData`, about closed subschemes,
  not this algebraic-space extension theorem.
- Mathlib grep: `AlgebraicSpace|first.order.thickening`, subdirectory AlgebraicGeometry.
  Zero hits.
- LeanSearch: "First order thickenings of algebraic spaces correspond to square zero
  ring sheaf extensions with quasi coherent kernels". Eight hits, principally
  `Algebra.Extension.infinitesimal`, `TrivSqZeroExt` and derivations/lifts. No match.
- Direct `rg` on `lean/WeilConjectures`, `lean/Sheaf` for the item id, candidate theorem
  name, `IsSpaceFirstOrderThickening` and `SpaceSquareZeroExtension`: found the existing
  extension-data module and realization theorem, and a reference in SplitModuleDeformationExt.
  No declaration states this entire theorem. The item/name search of
  `dag/lean_names_upstream.json` and upstream sources has no match.

Validation: `scompile.py Q30 lem-sfb-space-first-order-ringed-description <file>`
accepted the sandbox probe and library module (1.9s and 2.0s), with no errors or warnings.
All lines are at most 100 characters; `autoImplicit` is disabled.
No STATEMENT-DISPUTED issue or statement correction is needed.

## Second reading by Q30

This was a separate rereading in the same worker session: the dispatcher explicitly
forbids starting other agents, and the maintainer performs the independent delivery review.
I reopened the node and the finished module and checked the three conjuncts against
its forward, converse and maps paragraphs. The forward existential now explicitly
contains `G : X.QCoh` and a full `SpaceSquareZeroExtension`, so the kernel assertion
is not lost by merely reusing the realization theorem. The converse includes both
quotient and base equations. In the maps clause I chose an actual ring-sheaf natural
transformation on the common site, rather than only a chart-map encoding, and checked
that `∃!` includes equality of its induced ring map on every lifted chart. The domain
of `α` is `O_Y'` and the unique morphism has domain `X'`, as required by contravariance.
The compatible base maps in the forward clause are a parametrization of the same
unbased result, since every thickening is over its own target. No source assumption,
edge case or conclusion is omitted, and no dependency definition is duplicated.

Delivery dry run: `deliver2.py Q30 lem-sfb-space-first-order-ringed-description --no-push`
printed OK: the preflight and per-file compile passed; nothing was pushed.
