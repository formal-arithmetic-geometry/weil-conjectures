## Worker report

The delivery states `CategoryTheory.DgAlgebra.exists_finite_subcell_factorization`
in `Sheaf.CategoryTheory.DgCompactMapFiniteSubcell`, with its proof postponed by
`sorry`. It introduces one definition node,
`def-sfb-dg-finite-semi-free-filtration`, to record the given filtration and its
specified layer coordinates. The item's statement, proof and proof dependencies
are unchanged. Its statement dependencies gain this new definition and the already
landed `def-sfb-dg-derived-category`. No statement correction or dispute is needed.

I read the item's entire statement, proof and source (Stacks dga.tex,
lemma-factor-through-nicer, Tag 09R2, lines 6216–6278), its two original statement
dependencies and their complete recorded declarations/docstrings. The prescribed
Sheaf CompactObject example is now withdrawn; its node explicitly directs callers
to the identical upstream WeilConjectures.CategoryTheory.CompactObject, which is
used here. The current blueprint direct-images statement and proof at
literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/
were read. This auxiliary 09R2 statement does not change that blueprint unit.

Hypothesis and clause correspondence:

- The size convention is metatheoretic, as its recorded convention explains.
  Explicit `universe u`, `Algebra.{u}`, `Type u` layer indices and
  `IsCompactObject.{u}` consistently allow coproducts of the module universe.
  There are no auto-bound variables.
- The associative unital graded ring with differential and the right dg modules
  are the existing `Algebra` and `RightModule A`. `Algebra` is a monoid in integer
  cochain complexes of modules over `ULift ℤ`; its chain-map multiplication gives
  exactly the signed Leibniz rule. `RightModule` uses the reversed tensor category,
  so the action is right multiplication, with precisely the node's sign.
  No commutativity, degree bounds, flatness or countability is required.
- `Derived A` and `Q A` are the actual quasi-isomorphism localization and its
  canonical functor. As the recorded definition explains, this is equivalently
  localization of the homotopy category, since localization identifies homotopies.
  `[DerivedStructure A]` supplies its standard additive/coproduct/triangulated
  structures, with the exact shift and cone comparisons in the dependency, rather
  than assuming generation or a finite-cell factorization.
- `E : Derived A` and `hE : IsCompactObject.{u} E` give exactly the compact source
  for small coproducts. This uses the recorded upstream compactness definition,
  namely bijectivity of the canonical direct-sum Hom map, not a replacement notion.
- `n : ℕ` includes `n = 0`. `F : FiniteSemiFreeFiltration A T n` is a specified
  filtration of `T : RightModule A`. Its terms have indices `Fin (n+2)`:
  term 0 represents the node's F_(-1), term i.succ represents its F_i, and the
  last term represents F_n = T. `inclusion` is degreewise injective, `initial`
  is degreewise zero, `final` is degreewise surjective, and `compatibility`
  identifies the step maps with the inclusions into T. Thus every term is a
  dg submodule and the filtration is increasing. Equality at the endpoints is
  expressed by their canonical zero/final isomorphisms, without changing objects.
- The specified layer quotient is `F.layer i`: `F.projection i` is surjective
  in every degree and its kernel is the image of `F.step i` by `F.exact i`.
  This is the actual quotient F_i/F_(i-1), including layer 0. Each `F.shift i j`
  is the existing `ShiftComparison` with the regular module. It fixes the
  differential sign (-1)^k and the unchanged right action. `F.coprojection` and
  `F.isColimit` specify the dg coproduct coordinates, equivalently the node's
  specified isomorphism with the sum of these shifts.
- `f : E ⟶ (Q A).obj T` is an arbitrary derived map.
- The existential `U : RightModule A` with `ι : U ⟶ T` and degreewise injectivity
  represents the actual dg submodule T' of T by its injective inclusion. Its image
  is a dg submodule since ι is an action-preserving chain map. This representation
  is equivalent to using a literal subset; no arbitrary non-injective map is used.
- `S : ∀ i : Fin (n+1), Finset (F.index i)` selects the finite subsets J'_i of the
  originally specified J_i. Every layer, including the bottom layer, is quantified.
- `g : E ⟶ (Q A).obj U` and `f = g ≫ (Q A).map ι` give precisely the required
  derived factorization through that dg inclusion.
- For every layer i, degree p and homogeneous layer element z, the left side of
  the concluding equivalence says z is the projection of x in F_i whose image in
  T is also the image of y in U. This is exactly the image of F_i intersect U
  under the layer quotient map. Its kernel is F_(i-1) intersect U by F.exact and
  the injective inclusions. Hence it is also the image of the canonical injection
  (F_i intersect U)/(F_(i-1) intersect U) into F_i/F_(i-1).
- The right side says z is a finite sum over exactly `S i` of the specified
  coprojections, with arbitrary coefficients in the corresponding shifted
  regular-module components. It is precisely the coordinate subsum on J'_i.
  Quantification of the coefficient tuple over all J_i is harmless: every tuple
  on S extends by zero, including when S or J_i is empty. Equality of these
  degreewise images, and the inherited dg actions/differentials, identifies the
  successive dg quotients with the selected finite sums. This renders the
  node's final 'in particular' without an additional choice of isomorphism.

Dependency declarations used:

- `WeilConjectures.CategoryTheory.CompactObject`, `CategoryTheory.IsCompactObject`
  (the original recorded dependency def-pc-compact-object).
- `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`,
  `CategoryTheory.DgAlgebra.Algebra`, `RightModule`, `underlying`, `regular`,
  `Derived`, `Q`, `ShiftComparison`, `DerivedStructure`
  (landed definition node def-sfb-dg-derived-category, read in full).
- The new module `Sheaf.CategoryTheory.DgFiniteSemiFreeFiltration`,
  `CategoryTheory.DgAlgebra.FiniteSemiFreeFiltration`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` is a proof import for
  lem-weil-pbc-hom-into-triangle-exact. I read the recorded Mathlib declarations
  comp_distTriang_mor_zero₁₂, Triangle.coyoneda_exact₂ and Triangle.coyoneda_exact₁.
  The dg admissible-triangles proof prerequisite presently has no Lean record or
  Mathlib match, so it has no module to import. It is not a statement prerequisite
  and is retained verbatim in the item's proof plan and theorem proof docstring.

Edge cases checked by reading the signatures and the coordinate-image condition:
`n = 0` has two terms and one layer, so it retains F_0/F_(-1); all J_i empty
forces every layer to be zero but excludes no filtration; T=0 admits the zero
factorization and empty selections; A=0 is not excluded; S_i empty gives exactly
the zero image because the displayed sum is zero. Negative shifts and unbounded
noncommutative dg algebras are allowed by the existing cochain/module definitions.
An upper generator whose differential meets layer 0 remains covered, since no
splitting compatible with differentials is assumed in the filtration. This is not
an assertion about an ordinary ring concentrated in degree zero.

Searches for the statement: msearch leanfinder, query 'A map from a compact derived
dg module into a finite filtered semi free module factors through a finite cell dg
submodule', returned eight ordinary derived-complex/flat-module candidates, none
about finite dg cells. msearch loogle `"IsCompactObject", "Differential"` returned
zero hits. msearch grep `semi.free|Semifree|finite.cell` returned seven ordinary CW
complex hits. Searches in WeilConjectures and Sheaf for semi-free, finite-cell,
submodule and filtration interfaces found the existing dg framework and the
ordinary-ring DerivedModuleCellularFiltration, not this statement. Searching the
item id in WeilConjectures found nothing. The prospective declaration names were
also searched in dag/lean_names_upstream.json and both source trees: no matches.

Both delivered files compiled separately in dependency order using only
`/home/ubuntu/weil-launcher-all/batch2/scompile.py Q133
lem-sfb-dg-compact-map-finite-subcell <filtration.lean> <theorem.lean>`.
The wrapper reported clean sandbox and library-mode compiles for each file, with
roughly 1.1–1.4 seconds per compile. No extra warnings or errors were reported.
All data in the definition are structure fields; the only postponed proof is
the item's named theorem with the complete six-step natural-language proof.

## New nodes

`def-sfb-dg-finite-semi-free-filtration` defines the specified n+1-layer finite
filtration with injective dg inclusions, quotient projections, signed regular
shifts and specified coproduct cocones. Its source is Stacks Tag 09R2's given
filtration. It depends only on the size convention and the existing dg-derived
framework; it does not duplicate algebras, modules, shifts or derived categories.
Searches are recorded verbatim from searches.jsonl in its mathlib_searches.
LeanSearch for finite dg filtrations returned ordinary IsModuleFiltration and
Ideal.Filtration; their signatures concern filtered ordinary rings/modules and
have no differential or free-shift layer coordinates. LeanFinder for specified
free-shift quotient coordinates returned those same ordinary notions. Mathlib
grep `SemiFree|semi.free|FiniteSemiFreeFiltration|DGSubmodule` returned no hits;
project grep found only unrelated comments and the retired module name in a
header. `tools/blueprint_refs.py search 'finite semi free'` found zero blueprint
nodes. DAG search found statement nodes describing the relevant filtrations
inline but no definition node for this notion. The ancestor command prints
`blueprint.from.node = None`; the new node retains that null ancestor, the full
inherited source place, and the item's via chain prefixed by this item.

## Second reading by Q133

Author's second reading, not a claim of independent review: this dispatcher brief
forbids starting other agents; the maintainer supplies the independent reading.
I reopened both files against the item's full statement and the new definition.
The n+2 terms and n+1 layers were checked explicitly at n=0. The quotient
exactness uses step into term i.succ and projection out of that same term; the
intersection formula uses that very inclusion, not the previous term. The final
condition states coordinate equality of images, rather than merely abstract
finite generation or a finite free isomorphism type. ShiftComparison uses the
node's k, not -k; its standard free generator consequently lies in degree -k.
The factorization equation has the derived image of the actual injective module
map. No endpoint, empty selection, coefficient structure or original compactness
clause is lost. No mismatches were found in this second reading.
