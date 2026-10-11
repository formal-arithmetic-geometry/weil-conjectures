## Worker report

The module `lean/Sheaf/AlgebraicGeometry/PicardH1MultipleLocus.lean` states
`AlgebraicGeometry.Scheme.picard_h1_multiple_locus`, with its sole proof `sorry`.
The node's statement, proof, and proof dependencies are unchanged. Its statement dependencies
only gain `def-sc-joint-injective-structure-h1`. No statement correction or dispute was needed.
The source read was the complete statement and proof of Stacks Tag 0BF2,
https://stacks.math.columbia.edu/tag/0BF2 (Lemma H1-O-multiple-picard-flat-proper).
The local literature checkout does not contain more-morphisms.tex, so the official page was read.

Hypotheses and clauses, individually:

- `X S : Scheme`, `f : X ⟶ S`, `Xi : Fin n → Scheme`, and `fi : ∀ i, Xi i ⟶ S`
  introduce precisely the schemes and structure morphisms; `Fin n` indexes the finite family.
  The single arbitrary universe includes arbitrary scheme sizes; n may be zero.
- `[Flat f]`, `[IsProper f]`, and `[LocallyOfFinitePresentation f]`, and the corresponding
  three instance families for `fi`, render flatness, properness, and finite presentation.
  Properness supplies quasi-compactness and separatedness, hence quasi-separatedness;
  consequently locally finite presentation here is equivalent to finite presentation.
- `ui` and `hui : ∀ i, ui i ≫ f = fi i` render the morphisms over S and their commutative
  triangles. Explicit structure morphisms are appropriate because the node names f and fi.
- `hO` and `hOi` quantify over EVERY `g : T ⟶ S`. Their `IsIso` hypotheses concern
  `SheafOfModules.unitToPushforwardObjUnit (pullback.snd ...).toRingCatSheafHom`.
  This is exactly the canonical map O_T → (f_T)_* O_X_T: the Mathlib declaration's
  section formula is g^sharp, with source and target the actual unit modules.
  It is not an unspecified adjunction unit into the pushforward of an unidentified module.
- `L : X.Modules` and `[L.IsInvertible]` render the invertible module.
  `((Modules.tensorPullback (ui i)).obj L)` is L_i, without an extra independent family
  of line bundles or an arbitrary choice of their identification.
- `Z, j, [IsImmersion j]` and `Zi, ji, [∀ i, IsImmersion (ji i)]` are the locally closed
  subschemes. `hZ` and `hZi` give their universal properties for all scheme-valued points:
  factorization through the corresponding immersion is equivalent to the base-change
  module being tensor pullback of an invertible base module N. All isomorphisms are
  expressed by `Nonempty`, so no choice of trivialization is imposed.
  The dependency lemma allows finite locally free N; in the invertible-module case N must
  have rank one since the universal O-pushforward property makes f faithfully flat.
  Thus the displayed invertible-N universal property is precisely the line-bundle locus.
- `hsub` says every map through Z factors through every Z_i. For immersions, which are
  monomorphisms, this is containment in their scheme-theoretic intersection (one can
  test with T = Z); it says nothing merely about underlying sets.
- `s : S`, `hs : s ∈ Set.range j` say the point lies in Z. No rationality, closedness,
  or algebraic closure of its residue field is assumed.
- `hH` uses `JointInjectiveStructureH1` on `pullback (fi i) (S.fromSpecResidueField s)`
  and the morphisms obtained by applying `Over.pullback` to the commutative triangles.
  The common target is `pullback f (S.fromSpecResidueField s)`.
  These are exactly X_i,s, X_s, and the maps u_i,s in the node.
- The conclusion supplies `U : S.Opens` with `s ∈ U`. Its equivalence for EVERY map
  `T ⟶ U.toScheme` says that a map factors through Z precisely when it factors through
  every Z_i. This is equality of the represented subfunctors, hence equality of the
  subschemes over U by Yoneda. It includes nonreduced test schemes and therefore captures
  scheme-theoretic equality, not a weakened equality of underlying sets. This formulation
  avoids selecting an iterated fibre product for the finite intersection.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed`,
  `AlgebraicGeometry.Scheme.picard_diagonal_locally_closed`: read its full signature and
  proof docstring; the two explicit universal properties use its representation interface.
  The repository's recorded signature still names the old module pullback, but the actual
  source was already fixed to tensorPullback and its canonical adjunction. The usable
  declaration is imported, and no replacement dependency module is needed.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`: local rank-one trivializations.
- `Sheaf.AlgebraicGeometry.TensorPullback`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`: full functor signature/body and
  docstring read; used for all module pullbacks in the statement.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`,
  its affine-section definition and stalk equivalence.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`:
  separated, universally closed, locally finite type.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`: affine-section finite presentation.
- `Mathlib.AlgebraicGeometry.Over`, `AlgebraicGeometry.Scheme.Over`, `.Hom.IsOver`:
  the recorded definitions read; explicit morphisms and commuting triangles supply this data.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`,
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChange` and its sibling conventions:
  read the full module; its docstring explicitly directs users to `Limits.pullback`,
  `pullback.fst`, `pullback.snd`, and `Over.pullback` for scheme and morphism base change.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`,
  `SheafOfModules.unitToPushforwardObjUnit` (lines 57–65): canonical structure-unit map.

Edge cases checked before writing: n = 0 (the target product is the singleton group,
so injectivity is H¹ = 0 and the intersection is S); zero H¹ (the minor argument is
vacuous); repeated morphisms and repeated loci; identity morphisms; arbitrary residue
fields and characteristics; nonreduced bases and test schemes. If S is empty there is
no point s, so the statement is vacuous. Over a nonempty base the empty X is excluded
by the actual universal pushforward hypothesis, not an added nonemptiness assumption.

Searches actually run (logged by msearch.py in this item's sandbox):

- LeanSearch, `Injectivity on H1 of fibers makes Picard triviality loci equal locally`:
  HTTP Internal Server Error, recorded unavailable, not a negative match.
- LeanFinder, the same query: eight unrelated local-injectivity and representability hits;
  none states the Picard-locus result.
- Loogle, `AlgebraicGeometry, "picard"`: rejected unknown identifier AlgebraicGeometry;
  no useful match. This rejected query was not treated as evidence of absence.
- Mathlib grep via msearch.py, `picard|Picard|H1`, AlgebraicGeometry:
  elliptic-curve Picard comments and unrelated local variable h1 matches, no theorem.
- Direct rg of project Picard modules for H1, multiple, injectivity and triviality:
  no multiple-locus theorem; relative Picard injectivity results concern other maps.
- Direct rg of WeilConjectures and dag/lean_names_upstream.json for the item id: no hit.
- Direct rg of lean/Sheaf and the source tree for the final declaration names: no hit.
- Further searches for the new notion are described below. Existing site-cohomology
  pullback node `lem-weil-pbc-site-cohomology-pullback` was read: it is a general statement
  about maps for morphisms of sites, not the joint structure-sheaf H¹ condition.

The new definition compiled cleanly on the server. The two delivery modules were then
compiled together in dependency order, with explicit universes and no auto-bound variables.
The main theorem docstring contains all five DAG proof steps with their cited nodes.

## New nodes

`def-sc-joint-injective-structure-h1` defines
`AlgebraicGeometry.Scheme.JointInjectiveStructureH1` in
`lean/Sheaf/AlgebraicGeometry/JointInjectiveStructureH1.lean`. It is exactly the H¹
injectivity condition appearing in Tag 0BF2, for a finite family of scheme morphisms.
It uses the existing Ext definition `CategoryTheory.Sheaf.H`, the existing exact-functor
map `Sheaf.H.mapFunctor`, the exact inverse image of abelian sheaves, and the adjoint
of the underlying additive structure-sheaf map. No data or proof in this definition is sorry.
The finite direct sum is expressed by the equivalent product.

The definition existentially quantifies auxiliary isomorphisms from the constant integer
sheaf to its inverse image. These exist because topological inverse image preserves
constant sheaves (check on stalks, or compose the constant-sheaf and inverse-image
adjunctions). This is auxiliary data, not an extra geometric hypothesis. Relative to the
canonical identification, another such isomorphism multiplies the constant generator by
locally constant signs on each X_i. It therefore changes the i-th output by an invertible
endomorphism induced by those signs on O_X_i; joint injectivity is unchanged. This explains
why the condition is equivalent to injectivity of the canonical maps even though an
arbitrary constant-sheaf identification may be used in its formula.

Searches: LeanSearch for `canonical map on Zariski cohomology of structure sheaves induced
by a scheme morphism` was unavailable (HTTP 500); LeanFinder returned eight structure-sheaf
morphism declarations, including `Scheme.Hom.toRingCatSheafHom`, but no cohomology map.
Mathlib grep for `structureSheafCohomologyPullback|mapFunctor|cohomologyPullback` returned
only unrelated mapFunctor names; a more targeted grep for
`structureSheafCohomologyPullback|cohomologyPullback|JointInjectiveStructureH1` in
CategoryTheory/Sites returned zero hits. Direct rg in WeilConjectures and lean/Sheaf
found no specialized condition. DAG search found the general site pullback theorem
mentioned above, but no definition of this condition. blueprint_refs.py searches for
`structure sheaf cohomology pullback`, `joint injectivity H1`, `H1-O-multiple`, and
`injectivity on cohomology` each found zero imported blueprint nodes. Its ancestor was
computed as `thm-sc-theorem-of-cube`; the new node records that ancestor, the exact H¹
hypothesis served, and the item's via path with the item prepended.

## Second reading by C1

I independently read the item node, both proposed modules and the proposed new node,
all statement-dependency node records, and the actual dependency declarations. I read
Stacks Tag 0BF2 and its referenced Tag 0BDP on the official site, then fetched the official
more-morphisms.tex into scratchpad and read both labelled lemmas, their context and the
0BF2 proof. The source assumes precisely flat proper finite-presentation morphisms and
universally canonical structure pushforward isomorphisms; no field or Noetherian base.
There is no statement correction: the node agrees with the source.

Object/hypothesis/conclusion checklist, checked against the final Lean:

- Schemes X, S and the finite family X_i: `{X S : Scheme.{v}}`, `Xi : Fin n → Scheme.{v}`.
  Verdict: exact, with arbitrary universe and natural n including zero.
- Structure maps f and f_i: `f : X ⟶ S`, `fi : ∀ i, Xi i ⟶ S`. Verdict: exact.
- Flat, proper, finite presentation: the three instances for f and each fi.
  Verdict: exact; proper supplies quasi-compact and quasi-separated, so local finite
  presentation gives finite presentation. I read the Mathlib class definitions.
- Maps u_i over S: `ui` and `hui : ∀ i, ui i ≫ f = fi i`. Verdict: exact commuting triangles;
  `Over.homMk` uses precisely those equations, with no extra over-base instance.
- Universal O-pushforward: `hO`, `hOi`, for every scheme T and map g. Verdict: exact.
  The actual `unitToPushforwardObjUnit` section formula is the ringed-space structure map,
  with source the unit O_T and target pushforward of the unit O_X_T. No arbitrary adjunction
  or unrelated object is substituted.
- Invertible L: `L : X.Modules`, `[L.IsInvertible]`. Verdict: exact recorded scheme-module
  notion, whose signature I read in Modules/Invertible. L_i is literally
  `(Modules.tensorPullback (ui i)).obj L`, not an independently chosen bundle.
- Locally closed subschemes Z, Z_i: `Z`, `j`, `Zi`, `ji`, and immersion instances.
  Verdict: exact. Their universal properties `hZ`, `hZi` test all scheme-valued points and
  use the recorded tensor pullback along both base-change projections.
- Being pulled back from the base: `∃ N : T.Modules, N.IsInvertible ∧ Nonempty (...)`.
  Verdict: exact for line bundles. Tag 0BDP permits finite locally free N; universal
  O-pushforward makes all fibres nonempty, so a finite locally free N pulling back to
  an invertible module has rank one at every point. Conversely invertible N is finite
  locally free. Thus this interface neither adds nor drops a geometric hypothesis.
- Containment in the intersection: `hsub` for every T and g. Verdict: exact scheme
  containment, since taking T = Z and g = j gives factorization of j through every ji.
- Point s in Z: `s : S`, `hs : s ∈ Set.range j`. Verdict: exact, arbitrary residue field.
- Joint H¹ injectivity: final `hH : Function.Injective (fun x ↦ fun i ↦ ...)` uses the
  landed `structureSheafCohomologyPullback` on the fibre morphisms from `Over.pullback`.
  Verdict: exact canonical maps from H¹(X_s,O) to H¹(X_i,s,O). I read the full existing
  definition: exact abelian inverse image, canonical constant-Z comparison, and the
  adjoint of the additive structure-sheaf map. Finite product equals finite direct sum.
- Open neighbourhood: `∃ U : S.Opens, s ∈ U ∧ ...`. Verdict: exact.
- Scheme-theoretic equality over U: for every T and g into U, factorization through Z
  iff factorization through all Z_i. Verdict: exact equality of represented subfunctors,
  hence of the immersed subschemes, including nilpotents; not merely equality of sets.

Edge cases: n = 0 is allowed; the empty product is a singleton, hH asserts H¹ = 0,
and the universal right side of the conclusion is True (intersection S). Zero cohomology
and repeated family members cause no restriction. Empty S has no s and is vacuous;
empty fibres over nonempty T fail the canonical O-pushforward hypothesis itself.
Nonreduced schemes and test schemes are included. No characteristic, algebraic closure,
rational-point, finite-type-base or Noetherian restriction is present. All objects and
universes are explicitly bound; any finite collection of scheme sizes fits a common v.

Independent searches: LeanFinder query `line bundle pulled back from base locus intersection
first cohomology injective` returned eight unrelated cotangent/group-cohomology and local
scheme-injectivity hits; none states this lemma. Loogle `"picard"` returned twelve ODE
Picard iteration hits, no algebraic-geometric locus theorem. The worker's LeanSearch HTTP
500 is unavailability, not absence. My rg searched Mathlib AlgebraicGeometry, all
WeilConjectures and lean/Sheaf for multiple_locus, joint injectivity, Picard/locus and
cohomology/pullback variants. The specialized theorem was absent. The last search DID find
`Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback` and its landed DAG node
`def-sc-structure-sheaf-cohomology-pullback`; I opened both in full. This is the canonical
map required here. The same existing map is already used by PicardH1ProductInjective.
DAG and upstream-name searches found no existing multiple-locus theorem.

Mismatch repaired (H4/H12): the proposed new JointInjectiveStructureH1 module reimplemented
existing cohomology pullback using existentially chosen constant-sheaf identifications.
I removed that module and its new definition node, imported the landed canonical-map module,
wrote hH directly using its declaration, and replaced the proposed new statement dependency
with the landed canonical-map node. The statement's other binders and conclusion were right
and were preserved. The earlier Worker report and New nodes section above describe the
original delivery; this section supersedes their claims about the final H¹ implementation
and the existence of a new node. The final delivery contains no new or dependency modules.

I read PicardDiagonalLocallyClosed, TensorPullback and BaseChangeConventions as well as their
node records: tensorPullback is used throughout, and base changes use the prescribed chosen
pullbacks and Over.pullback. The imported diagonal theorem's abstract adjunction-unit hO
is not used as this statement's pushforward interface; this theorem correctly uses the
canonical structure map. No replacement dependency module is required to state this item.
The final theorem has only a sorry proof; it states no new proved result or hollow definition.
Its source/blueprint docstring contains all five DAG proof steps and cited dependencies.
The node lean.statement was regenerated verbatim from the revised signature. The final
single module compiled on the server without errors or warnings (4.7 seconds).

## Reviewer fix (R-phm1408)

Two forms were aligned with the landed Picard-locus family (C1 47e8207f5+5c16b296f, H1 5c287130a)
without changing the mathematics: `hO`/`hOi` now state the universal O-pushforward condition as
`IsIso` of the unit of `Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd _ g))`
at `SheafOfModules.unit T.ringCatSheaf` (not `SheafOfModules.unitToPushforwardObjUnit`), and the
locus universal properties `hZ`/`hZi` use `∃ (N : T.Modules) (_ : N.IsFiniteLocallyFree)` exactly
as in lem-sc-picard-diagonal-locally-closed, which is the node's cited source of Z and Z_i
(not `N.IsInvertible`). The unused import of `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`
was removed. The claims above about `unitToPushforwardObjUnit` and invertible N are superseded.
