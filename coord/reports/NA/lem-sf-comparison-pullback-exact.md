## Worker report

The module `Sheaf.Paper.ComparisonPullbackExact` states
`AlgebraicGeometry.comparisonPullbackExact`.  It uses the recorded comparison
functor `AlgebraicGeometry.ProEtale.comparisonUpperStar` and the recorded
constant sheaf and site declarations.  The binders `(T : Scheme.{u})`,
`(Λ : Type (u + 1))`, `[CommRing Λ]`, and `[Finite Λ]` render the scheme and
finite discrete commutative coefficient ring hypotheses.

The first conjunct is the nonempty ring-sheaf isomorphism between the inverse
image of the etale constant sheaf and the pro-etale constant sheaf.  The next
three functor clauses render additivity and preservation of finite limits and
finite colimits of the module inverse image, which is the exact flat module
pullback.  The cochain-complex clause gives, for every integer degree, a
natural comparison of the homology object of the termwise mapped complex with
the mapped homology object.  The following clause states preservation of
quasi-isomorphisms, and the last clause states preservation of vanishing below
an arbitrary integer bound.  All proofs are postponed with `sorry`.

Dependencies used are `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
(`AlgebraicGeometry.Scheme.proEtaleSiteComparison` and
`AlgebraicGeometry.ProEtale.comparisonUpperStar`),
`Mathlib.CategoryTheory.Sites.ConstantSheaf` (`CategoryTheory.constantSheaf`),
`Mathlib.Algebra.Homology.HomologicalComplex` (`CochainComplex` and
`HomologicalComplex.quasiIso`), and the project derived-category modules.
The exact-functor homology interface is the recorded
`AlgebraicGeometry.ProEtale.preservesHomology_comparisonUpperStar` instance.

Edge cases checked: arbitrary schemes including the empty scheme; arbitrary
finite rings including the zero ring; arbitrary integer degrees, including
negative degrees and degree zero; empty and zero complexes; and the case of a
bound below every degree.

Searches made: `rg` over the project and source for comparison pullback,
`msearch.py leanfinder` for exact inverse image and cohomology, `msearch.py
loogle` for `Functor.PreservesHomology`, and grep over Mathlib and the source
for `comparisonUpperStar`, `PreservesFiniteLimits`, constant sheaves and
quasi-isomorphisms.  These found only the recorded general comparison APIs;
none states the complete theorem in this node.

## Earlier second reading (a previous round; superseded)

The node and file were read together.  The scheme and coefficient hypotheses
are explicit.  Clause 1 is rendered by the constant-ring sheaf isomorphism
and the exact module-functor preservation clauses.  Clause 2 is rendered by
`Additive`, `PreservesFiniteLimits`, and `PreservesFiniteColimits`.  Clause 3
is rendered by the homology isomorphism for every `i`, quasi-isomorphism
preservation, and the arbitrary lower-bound implication.  No extra hypotheses
or special boundedness assumptions were introduced.

## Second reading by NA

I independently read the mathematical node, its six proof steps, the source
places, the dependency nodes and their actual Lean declarations, and the module.
The worker report above describes the original submission; this section records
the repaired delivery. The node's mathematical statement is correct and is
unchanged. There is no `statement_change`, new node or dependency module.

Source check: Stacks `sites-modules.tex`, Tags 03D2 and 03D7 (module pullback
and adjunction), the definition of flat morphism immediately before Tag 04JC,
Tag 04JC (exactness), and Tag 03DA (module kernels/cokernels); `proetale.tex`,
section-comparison (099R) and lemma-describe-pullback-from-etale (0GLZ);
`sites.tex`, Tags 00YV and 0H7J (algebraic structures and constant sheaves);
and `homology.tex`, Tag 010N. The available Stacks checkout is under
`/home/ubuntu/weil-launcher-nt/literature/stacks-project/`. These source places
impose no noetherian, separated, characteristic, nonzero-ring or boundedness
condition on this application. Ringed module pullback is tensor extension of
inverse image, and flatness is exactness of that tensor extension.

Object/hypothesis/conclusion checklist, in the node's order:

1. An arbitrary scheme T: `(T : Scheme.{u})`. Correct, including the empty
   scheme; no extra geometric property or morphism is supplied.
2. A finite discrete commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ]
   [Finite Λ]`. Correct; constants encode discrete coefficients, so an extra
   topology instance is neither required nor appropriate. The zero ring is
   included, as are all characteristics.
3. The small etale and pro-etale sites: `T.smallEtaleTopology` and
   `Scheme.ProEt.topology T`, using `Scheme.Etale`, respectively `Scheme.ProEt`.
   Correct. I checked the recorded site definitions and the actual framework
   declarations, not the big-site topology on schemes. Pro-etale objects are
   in `Type (u + 1)` and morphisms in `Type u`; both sizes are retained.
4. The constant ring sheaves: `constantSheaf` valued in `CommRingCat.{u + 1}`
   on those two sites, evaluated at `CommRingCat.of Λ`. Correct. This is
   Mathlib's sheafification of the constant presheaf, not the presheaf itself.
5. The comparison and its inverse image: the ring pullback is
   `Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)`;
   the module pullback is `ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T`.
   Correct. I opened `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and
   `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`: they use precisely
   the recorded comparison inclusion and the same sheaf-pullback construction,
   with induced operations and constant scalar endomorphisms. This is not
   scheme-morphism pullback of structure-sheaf modules.
6. Clause 1, canonical ring identification: originally just `Nonempty` of a
   ring-sheaf isomorphism. Repaired to `∃ c, c.hom = comparisonConstantRingMap
   T Λ ∧ ...`. The helper is real data: the inverse of the existing ring
   sheaf adjunction's `homEquiv` applied to the constant-sheaf-adjunction map
   induced by the scalar sections at `op (Scheme.ProEt.mk (𝟙 T))`.
   It has no `sorry`, arbitrary choice, extra hypothesis or private notation.
   Correct: this fixes the canonical scalar comparison, rather than allowing
   an unrelated ring automorphism.
7. Clause 1, flatness and tensor identification with the induced module:
   **missing in the original signature**, whose later exactness conjuncts
   did not specify the ringed tensor pullback. Repaired by quantifying over
   every `SheafOfModules.{u + 1}` M over the pulled-back constant ring and
   specifying an isomorphism from the underlying abelian sheaf of
   `SheafOfModules.changeOfRingsOfUniverses c.hom M` to that of M. Its map
   sends the sheafification image of `b ⊗ₜ[_, (c.hom.hom.app W).hom] m`
   to `c.inv.hom.app W b • m` for every site object W and all b,m.
   Correct: this is the node's tensor identification, with tensor factors in
   the dependency API's order. It specifies the transported scalar action;
   taking M to be the induced inverse image gives the stated module inverse
   image. On all M it identifies scalar extension with the same underlying
   abelian sheaf and therefore expresses flatness (exact scalar extension).
   The inverse is m mapped to 1 tensor m, as explained in the proof docstring.
   Naturality follows from the specified formula on local pure tensors.
   The formula has exactly the existing tensor/sheafification construction:
   no second tensor product, module category, or scalar-extension notion.
8. Clause 2, additivity and exactness: `.Additive`, `PreservesFiniteLimits`
   and `PreservesFiniteColimits` for the recorded module comparison functor.
   Correct and unchanged. Finite limits/colimits include the empty diagram
   and hence zero objects. No finiteness is imposed on a sheaf or its stalks.
9. Clause 3, cohomology: `∀ i : ℤ, Nonempty (...)` of a natural isomorphism
   from termwise pullback followed by `HomologicalComplex.homologyFunctor i`
   to the etale homology functor followed by module pullback. Correct and
   unchanged: it is natural in every complex, with the specified direction,
   and is sheaf cohomology objects, not cohomology of section presheaves.
   I checked `CochainComplex`, the actual homology-functor signatures and the
   derived-category dependency's cohomology interface.
10. Clause 3, quasi-isomorphisms: all complexes K,L and every map f are
    quantified before the implication on `HomologicalComplex.quasiIso`.
    Correct and unchanged, with the same termwise functor as above.
11. Clause 3, lower vanishing: `∀ a : ℤ` and every complex K, vanishing
    `IsZero (K.homology i)` for every `i < a` implies the corresponding
    vanishing for its termwise pullback. Correct and unchanged. No selected
    bound or restriction to nonnegative degrees is inserted.

Dependency review: besides the comparison and site interfaces above, I read
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, the constant-sheaf
adjunction in Mathlib, `Sheaf.CategoryTheory.RingedSiteModules` (the recorded
`ringedSiteModules`/`SheafOfModules` category), and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses` (actual
`changeOfRingsOfUniverses` and `changeOfRingsPresheafOfUniverses`). The latter
is sectionwise tensor followed by sheafification and permits independent
site, coefficient and module universes. I supplied its explicit universe
arguments `{u, u + 1, u + 1, u + 1}` because a `max` universe metavariable
was ambiguous; I imposed no new universe equality. The generic
`RingedToposMorphism` interface's equal object/morphism universes was not used.
I also read the ring-object lifting, algebraic-structure equivalence,
module-adjunction and abelian inverse-image exactness proof dependencies and
added their recorded imports. There are no new definition nodes or dependency
modules to review. The canonical map is a helper of this node, listed with
the theorem in `lean.declarations` under brief-stage2 section 1's helper rule.

Edge cases: arbitrary/empty schemes; zero ring and arbitrary characteristic;
zero sheaves, zero complexes and empty finite diagrams; degree zero, negative
and positive integer degrees; any integer lower bound; unbounded complexes;
no nonempty index-set assumption. The coefficient/module universe is the
recorded `u + 1` convention for this small-site framework, and the pro-etale
morphism universe remains u. There are no unbound variables or universes.

Independent searches: I ran `rg` on Mathlib, upstream `WeilConjectures` and
shared `lean/Sheaf` for `comparisonPullbackExact`, `comparisonUpperStar`,
constant-ring/sheaf pullback, change-of-rings isomorphisms, exactness and
homology. I opened the generic `Functor.constantSheafsheafPullbackIso`:
it is a general constant-sheaf comparison for a chosen pullback, not the
complete theorem or the particular construction in this item. Existing
`ProEtaleCanonicalTensorPullback` concerns a scheme morphism between two
pro-etale sites, not this site-comparison map. The constant-ring/module-sheaf
equivalence for lifted `ZMod` on the etale site is too specialized and is not
this theorem. No complete duplicate was found.

Prescribed search tools were also run with independent queries:
- LeanFinder: "inverse image between small etale and proetale sites preserves
  homology and constant coefficient rings" returned eight unrelated
  formally-etale/topology declarations, no match.
- Loogle: `CategoryTheory.Functor, "homology"` returned generic ShortComplex
  homology-functor declarations, not this comparison theorem.
- LeanSearch: "The inverse image along the etale to pro-etale comparison is
  exact and preserves constant ring sheaves" returned Internal Server Error;
  this is recorded as unavailable, not evidence of absence.
- `msearch.py ... grep` for
  `comparisonConstantRingMap|comparisonPullbackExact|constantSheafsheafPullbackIso`
  returned no hits. The explicit local `rg` search did find the generic
  constant-sheaf isomorphism mentioned above, which I inspected.

Repairs: restored the omitted tensor/induced-action content of clause 1;
fixed the canonical ring map; added its real-data helper and required imports;
expanded the theorem docstring to all six node proof steps, with source tags
and the proof dependencies; retained every correct exactness/cohomology
clause. The helper and theorem both carry source/blueprint docstrings. Only
the item's theorem is postponed with `sorry`; no statement was proved.
The node's `lean.statement` is verbatim the repaired theorem signature, and
all non-`lean` node fields remain unchanged. `scompile.py NA
lem-sf-comparison-pullback-exact lean/Sheaf/Paper/ComparisonPullbackExact.lean`
compiled the sandbox and module cleanly (11.8 s and 11.5 s respectively),
with no errors or non-sorry warnings. Final delivery preflight and compilation
are run below through `deliver2.py`.
