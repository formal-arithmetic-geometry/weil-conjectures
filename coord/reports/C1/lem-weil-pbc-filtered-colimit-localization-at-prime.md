## Worker report

The module states `AlgebraicGeometry.filteredColimitLocalizationAtPrime` for a small filtered category `I`, a commutative-ring diagram `F`, its chosen colimit, and a prime ideal `p`. It introduces the coprojections `ι` and contracted primes `pᵢ`, asserts existence of a functor `D` whose values are the prime localizations, compatibility of the colimit coprojections, and a cocone with vertex the localization of the colimit together with the colimit universal property (`Nonempty (IsColimit c)`). The proof is `sorry` as required.

The hypotheses are rendered by `{I : Type u} [Category I] [IsFiltered I]`, `(F : I ⥤ CommRingCat.{v}) [HasColimit F]`, and `[hp : p.IsPrime]`. Clause (1) is represented by the functor `D` and its object equalities; clause (2) is represented by the cocone `c` and `Nonempty (IsColimit c)`. The dependency notions use Mathlib `CategoryTheory.Limits.colimit`, `CategoryTheory.IsFiltered`, and `Localization.AtPrime`.

Edge cases checked: filteredness supplies nonemptiness; the prime ideal may be any prime (including minimal or maximal); no domain, finiteness, or nonzero assumptions are added; universes are explicit.

Searches recorded in the node (LeanSearch, LeanFinder/Loogle, and Mathlib/source/project grep) found no existing theorem asserting localization commutes with filtered colimits.

## Earlier second reading (a previous round; superseded)

The node and module were read together. The binders match the node's filtered diagram, colimit, prime, and contracted primes. The conclusion records the localization-valued functor, compatible coprojections, and the universal colimit cocone. No statement correction or dependency module was needed.

## Second reading by C1

Read the node's statement and all five proof steps independently against the Lean.
The local Stacks .tex files are not present in this read-only clone, so I read the
upstream algebra.tex at https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
label lemma-colimit-normal-ring (Tag 037D), especially the first paragraph of its proof.
It asserts the localization-colimit identity for contracted primes in a directed
system. Normality is used after that identity, not as a hypothesis for the identity;
the node's filtered-category generalization is supported by its elementwise proof.
No node statement correction is needed.

Object/hypothesis/clause checklist and verdicts:

- Small filtered category I: `{I : Type u} [SmallCategory I] [IsFiltered I]`.
  Changed Category to SmallCategory to match the small-category convention; pass.
- Diagram of commutative rings: `F : I ⥤ CommRingCat.{v}`; pass.
- Chosen ring colimit R and coprojections: `[HasColimit F]`, `colimit F`,
  `ι i := colimit.ι F i`; pass. The HasColimit binder expresses the supplied
  colimit, not a further condition on a diagram without a supplied colimit.
- Prime p of R: `p : Ideal ...` and `[hp : p.IsPrime]`; pass.
- Contracted primes p_i: `pᵢ i := Ideal.comap (ι i).hom p` and the conclusion
  `∀ i, (pᵢ i).IsPrime`; the latter was missing and is now stated; pass.
- Clause (1), contraction under every arrow: `Ideal.comap (F.map a).hom
  (pᵢ j) = pᵢ i`; replaced the original unrelated coprojection identity; pass.
- Clause (1), localization objects: functor `D` and equalities `hD` to
  `CommRingCat.of (Localization.AtPrime (pᵢ i))`; pass.
- Clause (1), canonical fraction transition maps and functoriality: the equation
  involving `D.map a`, `F.map a`, the two localization algebraMaps, and
  `eqToHom (hD _).symm` makes the transition map extend the original ring map.
  A ring map out of a localization is determined by that restriction, since
  denominators are units: it sends x/s to F(a)(x)/F(a)(s). Functor laws are
  supplied by D. The old statement specified only objects and allowed unrelated
  transitions; repaired; pass.
- Clause (2), canonical coprojection fraction maps: `c : Cocone D`, vertex
  equality `hc`, and the equation from F.obj i through the localization into
  c.pt and through `eqToHom hc` equals `ι i` followed by the localization
  algebraMap. This determines precisely x/s ↦ ι_i(x)/ι_i(s). The old cocone
  had no such equation and could use unrelated legs; repaired; pass.
- Clause (2), colimit universal property: `Nonempty (IsColimit c)` for that
  same cocone; pass. This is existence of its universal-property structure,
  not a bare abstract isomorphism of colimit objects.

Dependency audit: opened both dependency nodes. def-weil-pbc-category-colimit
records Mathlib's colimit/Cocone/IsColimit/IsFiltered; those are used directly.
def-weil-pbc-localization-at-prime records Localization.AtPrime; opened
Mathlib/RingTheory/Localization/AtPrime/Basic.lean, whose abbreviation is
Localization p.primeCompl and whose algebraMap is the ring-to-fractions map.
No private notions, new nodes, or dependency modules are needed.

Edge cases: IsFiltered includes nonemptiness, so the empty category is correctly
excluded by the node. A zero colimit ring has no prime p, as in the node; no
Nontrivial or domain hypothesis was added. Zero stages are not separately
excluded. Arbitrary characteristic is allowed. Scheme emptiness and n = 0 are
inapplicable to this ring statement. Independent explicit universes u for the
small category and v for the ring carriers cover all diagram sizes for which
the supplied colimit lies in CommRingCat.{v}; there are no test-algebra universe
quantifiers and no unbound variables.

Independent searches: msearch loogle `Localization.AtPrime, IsColimit` returned
no hits (IsColimit was unknown to that search endpoint); leanfinder `prime
localization of a filtered ring diagram commutes with its direct limit` and
`commutative ring filtered colimit localized at the contraction of a prime ideal`
returned prime-localization maps, localization-of-localization lemmas and
CommRingCat.FilteredColimits.colimit, none this theorem. rg with
`isColimitAwayProdCocone|localization.*colimit|colimit.*localization` across
WeilConjectures and project lean/Sheaf located the upstream
CommRingCat.isColimitAwayProdCocone. Opened its signature: it concerns one
fixed ring localized away from finite products of denominators, not arbitrary
ring diagrams. Project module localization and categorical localization hits
are also different statements. The original node records LeanSearch and
Mathlib grep searches; independent Mathlib rg inspected the localization map
API and found no general localization/filtered-colimit theorem.

Other repairs: expanded the theorem docstring into all five actual proof steps
with their DAG dependencies and source label; added the conventional header,
placed the module docstring after imports, and synchronized lean.statement
verbatim with the signature. There is one theorem proof, `sorry`, no proved
helper and no hollow definition. Final single-file scompile passed cleanly
without warnings. The node's mathematical statement and dependencies are unchanged.
