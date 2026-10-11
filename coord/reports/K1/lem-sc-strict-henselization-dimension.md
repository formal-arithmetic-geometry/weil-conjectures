## Worker report

The module `Sheaf.RingTheory.StrictHenselizationDimension` states
`ringKrullDim_eq_of_isStrictHenselization`, with proof `sorry` only.
The original statement is unchanged; its statement dependencies gain the new
local-ring strict-henselization definition described below.

Hypothesis and clause correspondence:

- “R is a local commutative ring”: `(R : Type uR) [CommRing R] [IsLocalRing R]`.
- “with respect to a separable closure of its residue field”: `(K : Type uR)
  [Field K] [Algebra (IsLocalRing.ResidueField R) K]`, together with the
  `IsSepClosure (IsLocalRing.ResidueField R) K` conjunct in `hS`.
  An algebra structure on fields is precisely the specified field embedding.
- “S is its strict henselization”: `(S : Type vS) [CommRing S]` and
  `hS : IsStrictHenselization R K S`, the colimit-of-triples characterization
  of Stacks 04GW with the closed prime of the local ring. No Noetherian,
  domain, finite-dimensional, or characteristic assumption is added.
- “dim R = dim Rsh”: `ringKrullDim R = ringKrullDim S`.
  This is equality in `WithBot ℕ∞`, not equality of truncated natural dimensions.

Dependency declarations used: `ringKrullDim` from
`Mathlib.RingTheory.KrullDimension.Basic` (definition and docstring read);
`IsStrictHenselization` from the accompanying
`Sheaf.RingTheory.StrictHenselizationRing`.
The latter uses the existing notions `AlgebraicGeometry.Etale` and `Spec.map`
from `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Cocone` and `IsColimit`
from `Mathlib.CategoryTheory.Limits.HasLimits`, `IsSepClosure` and
`IsSepClosed` from `Mathlib.FieldTheory.IsSepClosed`, and the residue map
from `Mathlib.RingTheory.LocalRing.ResidueField.Basic`. These definitions
and docstrings were read, including the full Factorisation and full-subcategory
interfaces. `IsSepClosure` is the Mathlib combination of separably closed and
separable algebraic extension; this renders the separable-closure clause of
`def-kun-separably-closed`, whose recorded `IsSepClosed` alone is its first clause.
The new definition uses both clauses, with Mathlib's existing `IsSepClosure`.

Edge cases checked before writing: fields (dimension zero), separably closed
residue fields (the identity extension is allowed), rings with nilpotents,
non-Noetherian local rings, arbitrary positive characteristic, and infinite
Krull dimension are all included. The zero ring is excluded by the source's
local-ring convention: a local ring has a proper maximal ideal and a residue
field. No empty indexing category is substituted: R itself, with its residue
map to K, is an étale factorization. Universes are explicit: the indexing rings,
R, and K have a common arbitrary ambient universe u; S may be in an independent
universe v. No enumeration or countability of all étale algebras is assumed.
The predicate uses the universal property on the full large category rather
than asserting a small-diagram colimit instance for that category.

Source verification: the local literature checkout contains only index/list
files, so the actual sources were read at
https://stacks.math.columbia.edu/tag/06LK,
https://stacks.math.columbia.edu/tag/04GP and
https://stacks.math.columbia.edu/tag/04GW. Tag 06LK covers every local ring;
04GW supplies precisely the étale triples colimit. Maps A → K identify a prime
as their kernel and extend uniquely to the residue field at that prime, giving
exactly the same indexing category as triples. Its ring colimit is the strict
henselization. The ring is allowed to be any isomorphic copy: the conclusion
only depends on its ring structure.

Searches (all services called through msearch.py):

- LeanFinder, “strict henselization preserves Krull dimension of local rings”:
  eight quotient/localization dimension lemmas, no strict-henselization result.
- Loogle, “ringKrullDim, HenselianLocalRing”: zero hits.
- Mathlib grep, “StrictHens|strictHens|strict_hens|henselization”: zero hits.
- LeanSearch, “strict henselization local ring colimit etale algebras residue
  field separable closure”: unavailable, Internal Server Error.
- LeanFinder, “strict henselization ring construction colimit pointed etale
  algebras”: eight standard étale and henselian-ring declarations, no construction.
- rg of WeilConjectures and lean/Sheaf for strict henselization: prose only,
  apart from the existing strictly henselian predicate, which is not the
  strict-henselization construction. rg of the upstream declaration index and
  the source tree for the item id or the new names found no declaration.
- DAG search and blueprint_refs.py search “strict henselization”: the geometric
  pointed-neighbourhood limit definition exists but has no Lean declaration;
  the triples node is a theorem about the algebraic presentation, also with
  no declaration. Neither provides the ring construction used by this item.

No statement dispute or source correction is needed. Both modules compile
cleanly together on the server; the initial concatenated compile exposed a
repeated universe name, fixed by using uR/vS in the theorem module.

## Second reading by K1

I read the item node, its source places, the dependency signatures, and both
delivered modules independently. The node introduces a local commutative ring
`R`, a residue-field separable closure `K`, and a commutative ring `S` equipped
with the strict-henselization property. Lean renders these as `(R K : Type uR)`
with `[CommRing R] [IsLocalRing R] [Field K]`, the residue-field algebra
instance, and `(S : Type vS) [CommRing S]`; `hS : IsStrictHenselization R K S`
supplies exactly the separable-closure and colimit clauses. The conclusion is
the node's `ringKrullDim R = ringKrullDim S`, with the Mathlib `WithBot ℕ∞`
dimension. No Noetherian, domain, finite-type, characteristic, or finiteness
hypothesis is added, and no conclusion clause is omitted. The theorem's
docstring reproduces both proof steps from Tag 06LK and names their proof-node
inputs.

For the new definition, the Lean predicate has the same objects and hypotheses
as its node: `IsSepClosure (IsLocalRing.ResidueField R) K`, followed by a
universal cocone for the full subcategory of factorizations `R → A → K` whose
first scheme map is étale, and a ring isomorphism from the cocone point to `S`.
`Factorisation.Hom` enforces commutation with both structural maps, so this is
the triples category of Tag 04GW; `Cocone` and `IsColimit` give the universal
colimit property without selecting a small indexing category. The declaration
is data-free (no hollow `sorry`) and its docstring cites Tags 04GP/04GW and the
blueprint node.

Edge cases checked were fields (dimension zero), separably closed residue
fields (identity closure), nilpotents, non-Noetherian local rings, arbitrary
characteristic, infinite dimension, the zero-ring convention for local rings,
and the nonempty factorization supplied by `R` itself. The theorem permits an
independent universe `vS` for `S`; `R` and its residue-field closure share the
universe parameter required by Mathlib's `CommRingCat.of` factorization API.

I searched the pinned Mathlib and source trees for strict-henselization and
dimension declarations, and ran LeanFinder and Loogle searches for the
construction and dimension theorem; only generic henselian, localization, and
Krull-dimension results were found. LeanSearch was unavailable and is recorded
as such. The geometric pointed-neighbourhood limit and the filtered-triples
theorem are distinct DAG notions and provide no existing declaration of this
ring predicate. No mismatch with the node was found and no source or statement
change was required. Both delivery modules compile together cleanly with
`scompile.py` (no warnings other than permitted sorry declarations).

## New nodes

`def-sc-strict-henselization-ring` defines the algebraic strict-henselization
ring by Stacks 04GW's colimit universal property. It uses the existing étale,
separable-closure and categorical-colimit notions, with no sorry and no
unproved choice of colimit data. The functor is the existing
`Factorisation.forget` restricted by `ObjectProperty.ι` to the étale first maps.
The conjuncts are exactly `IsSepClosure` and the existence of a universal
cocone with a ring isomorphism from its point to S. Its indexing category is
allowed to be large: no unjustified application of small-colimit existence
is made. The geometric definition `def-weil-pbc-strict-henselization-limit`
constructs an affine scheme from pointed scheme neighbourhoods and would
require its many not-yet-stated dependencies; it supplies no algebraic ring
interface. The existing triples node proves filteredness, locality and
henselianity of this construction, rather than defining the ring predicate.
The generic ind-étale closed lift defines a different construction with a
variable ind-étale quotient algebra; it also has no usable declaration.
No private copy of any existing mathematical building block is introduced.
The new node's searches are copied from actual logged calls, with additional
source and Sheaf grep results recorded. Its dependencies are the existing
separably-closed/separable-closure, étale, and colimit definition nodes.

## Reviewer fix (R-shd1314)

The private `IsStrictHenselization` of `Sheaf.RingTheory.StrictHenselizationRing` and its node
def-sc-strict-henselization-ring duplicate the landed def-sc-ring-strict-henselization
(`Algebra.IsStrictHenselization`, F1 4f26cb852): both are the universal cocone over etale
algebras pointed in a separable closure of the residue field (Stacks 04GW), so the node and
the module are dropped (H4/H12). The theorem is restated on the landed predicate, as the
sibling `Algebra.isRegularLocalRing_iff_strictHenselization` (c5a517e5d):
`(R K C : Type u) [CommRing R] [IsLocalRing R] [Field K] [Algebra κ K] [IsSepClosure κ K]
[Algebra R K] [IsScalarTower R κ K] [CommRing C] [Algebra R C]
(hC : IsStrictHenselization R K C) : ringKrullDim R = ringKrullDim C`, declaration
`Algebra.ringKrullDim_eq_of_isStrictHenselization`. No Noetherian hypothesis: the node says
"local commutative ring". The common universe is forced by the landed definition.
