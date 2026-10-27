## Worker report

The module `Sheaf.CategoryTheory.RingedLocalBoundDirectImageTruncation` states
`CategoryTheory.ringedLocalBoundDirectImageTruncation`, with its proof postponed.
The natural-language item is unchanged. Read Stacks `sites-cohomology.tex`,
`situation-olsson-laszlo` (0D6R) and `lemma-olsson-laszlo-map-version-one` (0D6U),
including their proofs. No statement dispute or correction was needed.

Hypotheses and clauses, in order:

- The sites are `C D : Type u`, with `SmallCategory` structures, actual precoverages
  `J L`, and `J.IsSiteForCoverings`, `L.IsSiteForCoverings`. Their associated
  Grothendieck topologies define the sheaf categories. This uses the recorded
  site convention, retaining actual covering families rather than replacing
  cofinality by an assertion about saturated sieves.
- The ring sheaves are `O R : Sheaf … RingCat.{u}`; `_hO` and `_hR` say their
  multiplication is commutative, using the existing ring structures. Thus no
  alternate module category is introduced by conversion of coefficient encodings.
- `f : RingedToposMorphism O R` is the recorded arbitrary geometric morphism with
  structural ring map and induced additive module direct image `f.modules`.
  There is no site-functor, flatness, pullback exactness or equivalence assumption.
- `ringedSiteModules.{u,u,u,u}` is the recorded abbreviation for Mathlib
  `SheafOfModules`. Site objects, morphisms and coefficient sets lie in `u`;
  module sheaves themselves lie in the larger universe. The independent explicit
  `HasDerivedCategory.{w}` binders implement the chosen ordinary unbounded
  derived categories. `HasExt.{e}` specifies only the chosen size of ordinary
  abelian-sheaf cohomology; it exists at the standard larger universe.
- `P Q : ObjectProperty …` are the two classes. Each has `ContainsZero`,
  `IsClosedUnderIsomorphisms`, `IsClosedUnderKernels`, `IsClosedUnderCokernels`,
  and `IsClosedUnderExtensions`. These are precisely the expanded weak Serre
  hypotheses. Object properties represent full subcategories; isomorphism
  closure makes them strictly full. No subobject/quotient closure is assumed.
- `_hlocalO` and `_hlocalR` apply the new `HasRingedLocalBoundProperty` to the
  respective sites, coefficients and classes. In that definition, `V : Set C`
  is the covering basis, the first quantified presieve is a covering with all
  domains in `V`, and the second clause gives `d : ℤ` for each basis member.
  For every original covering `S`, it supplies a covering `T`, factorization of
  each `T` arrow through an `S` arrow, and the bound on all its domains, all
  sheaves in `P`, and all natural `p` with `d < p`. The collection of all such
  good covers is therefore cofinal, exactly as in the item. The converse is
  obtained by selecting a refining member of the given cofinal collection.
  `Sheaf.H'` is the recorded ordinary cohomology over an object, applied to
  `SheafOfModules.toSheaf`; `IsZero` expresses vanishing of this abelian group.
- `Rf` and `η` parameterize the total derived direct image. `_hderived` is its
  right-derived universal property for quasi-isomorphisms of complexes;
  `_hKI` says the resolution unit is invertible on K-injective complexes.
  This specifies the functor named in the item, rather than adding a condition
  on `f` or replacing its derived image by an arbitrary functor. This follows
  the already recorded resolution interface of the tower comparison. Any
  K-injective derived direct image satisfies it, and the interface determines
  the functor up to its unique compatible isomorphism.
- `N : ℤ` is unrestricted. `_himage` says, for every `P F` and `p : ℕ`, that
  `H^p(Rf(F[0]))` lies in `Q`; `_hvanish` says the same object is zero when
  `N < p`. This is exactly the higher-direct-image hypothesis, expressed via
  its definition on degree-zero objects. No bound in negative degrees is added.
- `K` is an arbitrary object of the unbounded source derived category and `_hK`
  says `P (H^j K)` for every integer `j`. No lower bound on K is imposed.
- The first conjunct says `Q (H^j (Rf K))` for every integer `j`, namely
  membership in `D_B`.
- The second conjunct quantifies `n : ℕ`, `j : ℤ` and `N - n ≤ j`, and asserts
  `IsIso` of `H^j.map (Rf.map (t.truncGEπ (-n)).app K)`. The actual canonical
  truncation projection is used, so the conclusion specifies the map as well
  as its source and target. It includes the boundary `j = N-n`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`:
  full structure, including its module-linear underlying adjunction clause.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: actual site covering axioms;
  Mathlib `Precoverage.toGrothendieck`, `Sheaf.H'` for the remaining components.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  transparent abbreviation of `SheafOfModules`, with inherited abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`; `HomologySequence`, `DerivedCategory.homologyFunctor`;
  `TStructure` and `Triangulated.TStructure.TruncLTGE` for the canonical truncation
  functors and `truncGEπ`.
- `def-weil-size-convention` is metatheoretic; it supplies no declaration.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` was read in full. Its
  module documentation identifies good truncations with the existing Mathlib
  standard t-structure, which is used directly. Its primary declaration
  `IsSequentialHomotopyColimit` is a separate clause not needed here.

Recorded proof-dependency imports are present for the lower-truncation step
triangle, triangulated right derived functors, long exact cohomology sequence,
shift identification, tower pushforward/limit comparison, K-injective resolutions,
and truncation hypercohomology. Their signatures and source docstrings were read.
The two local-bound reconstruction/stationary-limit nodes have no Lean records
or Mathlib matches at the time of writing, so their modules cannot be imported;
they are named in the proof docstring and remain in the unchanged DAG proof plan.
They are proof inputs, not notions missing from this statement.

Edge cases checked before writing: the zero object, empty site, empty covers when
allowed by the given site, `n=0`, negative N, and the equality `j=N-n` are retained.
Negative local bounds are retained (`d : ℤ`, `p : ℕ`), hence may force even sections
of the class to vanish. The class need not be closed under arbitrary subobjects
or infinite limits. K may be unbounded in both directions. No products-exactness
or uniform lower bound on the truncation tower is imposed.

Searches actually run: `msearch.py` LeanFinder query “Unbounded derived direct
image cohomology stabilizes on lower truncations under local cohomological dimension
bounds” returned eight standard derived-category support/truncation lemmas, no
match. Loogle `"rightDerivedFunctor", "truncGE"` returned zero hits. Mathlib grep
`rightDerivedFunctor.*truncGE|localBound|LocalBound` returned zero hits. LeanSearch,
LeanFinder and further grep for the missing local bound definition are recorded
verbatim in the new node. `rg` in `lean/WeilConjectures` and `lean/Sheaf` found no
Olsson–Laszlo/local-bound property; the only unrelated Laszlo hits were literature
citations. DAG search by 0D6R, “local bound property” and its source label found
only inline hypotheses in the present item, the two proof inputs, and two later
consumers; none owns a definition. `blueprint_refs.py search 'local bound'` gave
two unrelated local-boundary nodes; `'cofinal system'` gave no matches.

Validation uses the prescribed `scompile.py` for each module separately in
sibling dependency order, followed by `deliver2.py --no-push` and delivery.

## New nodes

`def-sfb-ringed-local-bound-property` owns
`Sheaf.CategoryTheory.RingedLocalBoundProperty` and the real Prop-valued definition
`CategoryTheory.HasRingedLocalBoundProperty`. It is the reusable local bound
hypothesis of Stacks 0D6R, needed on both sites in 0D6U. It uses existing module
sheaves, actual site coverings, refinement factorizations, and ordinary sheaf
cohomology. No data or proof is postponed inside the definition. Searches above
found no existing definition node or declaration. Its blueprint ancestor is null
because the item's own recorded nearest ancestor is null; the inherited via path
and precise source use are retained. The item gains only this statement dependency
and its Lean record.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
