## Worker report

Module: `Sheaf.AlgebraicGeometry.ArtinMinimalDescentTransport`.
Main declaration:
`AlgebraicGeometry.ArtinDeformation.artin_minimal_descent_transport`.
The statement and all existing DAG fields are unchanged; only `lean` is set.

Source read: `literature/stacks-project/formal-defos.tex`, the whole paragraph
constructing S_x and f_* before `lemma-smallest-where-descends`, its minimality
paragraph, and both clauses and both proofs of that lemma (Tag 06T1).
The node is a supporting lemma, not a blueprint unit statement.

The definitions introduced explicitly in this node are supplied in its own module,
as permitted for helpers belonging to the same notion. No additional independent
notion, replacement dependency module, or new DAG node is needed.
`DescentData` uses actual `Subalgebra R (ring A)` objects. Its `valid` field says
that the restricted augmentation is a test algebra, and its `obj` and `arrow`
are the object and arrow over the literal inclusion. `descentOver` embeds these
objects into the over category of Mathlib's pseudofunctor Grothendieck construction.
`DescentCategory` induces exactly its commuting-triangle morphisms. It does not
replace literal subrings by arbitrary injective maps or by their isomorphism classes.

Hypotheses and clauses, in order:

| Node text | Lean rendering |
| --- | --- |
| Commutative base ring Lambda | `{R : Type u} [CommRing R]` |
| Noetherian and local Lambda | `[IsNoetherianRing R] [IsLocalRing R]` on the theorem |
| Field l with its Lambda-module structure | `{k : Type u} [Field k] [Algebra R k]` |
| l finite as a Lambda-module | `[Module.Finite R k]`; the finite-type instance needed by the dependency's canonical pullback is inferred from this hypothesis |
| Marked Artinian test category | The dependency's `TestCategory R k`, retaining its original residue markings and morphisms |
| Category cofibred in groupoids, with coherent transport | `F : CofibredGroupoids.{u, v, w} R k` |
| S1 for A1 -> A <- A2 with second leg surjective | `hS1 : IsSchlessingerOne F`; its quantifiers include all three test objects, both arrows, and `Function.Surjective (map f₂)` |
| Objects and a specified comparison isomorphism lift compatibly | `EssSurj` of the dependency's `comparison` to `CategoricalPullback`; its target objects retain the specified isomorphism and its target isomorphisms retain compatibility |
| S_x has objects x' -> x over test subalgebras | `DescentData` and `DescentCategory`, with the original test predicate, literal subalgebra, and arrow over `subalgebraInclusion` |
| Arrows are commuting triangles over x | Morphisms induced from `Over (totalObject F x)` |
| Minimal means every incoming arrow has the same subring | `IsMinimalDescent D := ∀ E, (E ⟶ D) → E.subring = D.subring` |
| Every object receives an arrow from a minimal object | First conjunct, for every `A`, `x`, `D`: `∃ M, IsMinimalDescent M ∧ Nonempty (M ⟶ D)` |
| Given u over f, transport from B' to f(B') then compose with u | `u : totalObject F y ⟶ totalObject F x`; `u.base` is f. `descentImageRing` is the actual range of f restricted to B'. `descentImageMap` is its range restriction, and `descentImage` applies `push` to that map, then uses composition constraints, the original descent arrow and `u.fiber` |
| This defines f_* as a functor | `descentImageFunctor u`; `descentImageHom` is the unique arrow characterized by the cocartesian square, with explicit identity and composition obligations |
| (1) Every minimal object maps to a minimal object | Second conjunct, for every u and D: `IsMinimalDescent D → IsMinimalDescent ((descentImageFunctor u).obj D)` |
| (2) f is surjective | The third conjunct assumes `Function.Surjective (map u.base)` |
| Every minimal object of S_x is isomorphic to the image of a minimal object of S_y | For each minimal `D`, the third conjunct supplies `E`, `IsMinimalDescent E`, and `e : (descentImageFunctor u).obj E ≅ D` |
| The resulting B' -> A' is surjective | `Function.Surjective (map (descentImageArrow u E ≫ e.hom.hom.left).base)` |
| The square of objects over u commutes | The concluding equality says that the resulting E-source -> D-source -> x equals E-source -> y -> u -> x |

The map in the final clause is fixed by the construction: it is the canonical
range transport arrow followed by the source arrow of e in S_x. Both the
surjectivity and the square refer to that same map, rather than to an independently
chosen map. `descentImageArrow` has exactly the range-restriction base map and
identity fibre component.

Every theorem has `sorry` as its entire proof. Their docstrings give the mathematical
proof and the source. The helper proof obligations are the ones intrinsic to the
image construction and functor already described in the node's proof steps 4 and 5:
image validity, residue compatibility, factorization, the commuting square, unique
induced arrow, and the identity/composition laws. They all belong to this same node
and are listed in `lean.declarations`. Definitions contain explicit data. The only
choice, in `descentImageHom`, is from an existence-and-uniqueness theorem specifying
a unique morphism by its square; no undetermined object is chosen from an existence
axiom. The main theorem's docstring covers all eight DAG proof steps, including
Nakayama, finite length under restriction, the least-length argument, the two S1
pullbacks, image functoriality, and the final square.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing` (the abbreviation and
  `isNoetherianRing_iff_ideal_fg`): exactly the base Noetherian hypothesis.
- `Mathlib.Algebra.Field.Defs.Field`: exactly the field structure; this is the
  `mathlib_match` of `def-weil-field`, which needs no separate Lean record.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`, namespace
  `AlgebraicGeometry.ArtinDeformation`: `IsTestAlgebra`, `TestCategory`, `ring`,
  `residue`, `map`, `CofibredGroupoids`, `fibre`, `push`, `compIso`,
  `fibreProductTest`, `fibreProductFst`, `fibreProductSnd`,
  `fibreProduct_condition`, and `comparison`. Its full module was read, including
  the pseudofunctor coherence and construction docstrings.
- `Mathlib.CategoryTheory.Bicategory.Grothendieck`:
  `CategoryTheory.Pseudofunctor.Grothendieck` and its category structure provide
  exactly the total arrows and coherent composition of the chosen presentation.
- `Mathlib.CategoryTheory.InducedCategory`: `InducedCategory` supplies the
  descent category's commuting triangles without another category-law interface.

Proof imports are `Sheaf.RingTheory.SemilocalRestrictionLength`
(`semilocal_restriction_length`, read with its full signature and proof docstring),
`Mathlib.RingTheory.Nakayama`, and `Mathlib.RingTheory.Length`.
The Artinian self-length dependency is publicly available through the test-category
module's `Mathlib.RingTheory.HopkinsLevitzki` import. The proof-only node
`lem-sfb-artin-local-test-algebra` has no recorded Lean declaration or Mathlib
match, so no nonexistent module is imported for it. The statement already uses
the canonical test-ring pullback and projection obligations supplied by the
recorded definition dependency. No statement dependency is omitted or replaced.

Edge cases checked before writing and again on rereading:

- The zero ring is excluded from the test category by its surjective marking to
  the nontrivial field k. It is not wrongly excluded by an additional assumption.
- Empty fibres of F are permitted. Existence is asserted below an existing D;
  no global nonemptiness, predeformation condition, RS, or S2 is assumed.
- Identity and isomorphism u are included. The pseudofunctor constraints retain
  their unit comparisons; the image construction also includes top subalgebras.
- A nonsurjective u is permitted in clause (1); only clause (2) assumes onto.
- Minimality means minimal rather than least: uniqueness of a minimal subring,
  or equality between all minimal descents, is never asserted.
- Finite residue extensions of arbitrary degree and every characteristic remain
  allowed. Module-finite is not replaced by the weaker finite-type hypothesis.
- The two fibre universes v and w remain independent of the ring universe u.
  All test rings use the dependency's universe convention, and subalgebra types
  remain in that universe. There is no new equality of universes or auto-implicit.
- The third clause retains actual objects and their automorphisms: its isomorphism
  is in S_x itself, before taking any quotient by isomorphism classes.

Searches for an existing statement or construction:

- `msearch.py leanfinder`, query: "Minimal Artinian rings of definition in a
  cofibered groupoid satisfying Schlessinger S1 are preserved by images and lift
  under surjections". Eight hits concerned Artinian images and formal smoothness
  of ring maps, including `Function.Surjective.isArtinianRing`,
  `isArtinianRing_range`, and `Algebra.FormallySmooth.of_comp_surjective`.
  None states this categorical descent statement.
- `msearch.py loogle`, query:
  `CategoryTheory.Pseudofunctor, Subalgebra.map, AlgHom.rangeRestrict`.
  Zero hits. Direct source reads subsequently found and reused the existing
  pseudofunctor Grothendieck construction and algebra range restriction.
- `msearch.py leansearch`, query: "Schlessinger condition minimal ring of
  definition cofibered groupoids Artinian local rings". Eight hits concerned
  Artinian rings, nilpotent maximal ideals and finite length, including
  `isArtinianRing_iff_isFiniteLength`; no categorical descent result.
- `msearch.py grep`, query: `Schlessinger|smallest.*descend|minimal.*descent`.
  The sole reported hit was the unrelated nilpotency class of a group.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for minimal descent,
  `IsSchlessingerOne`, S1/RS and the proposed declaration names, and the required
  `grep -rn` for the item id in `lean/WeilConjectures`. No existing declaration
  states this result or defines S_x for these Artinian subalgebras. Existing
  minimal complexes and scheme-descent data are different notions.
- Read `dag/lean_names_upstream.json` for the relevant names. No exact match.
  Searches of the Artin modules found and reused the recorded test-category API;
  their other Rim--Schlessinger definitions have different bases.

Validation: `scompile.py Q160 lem-sfb-artin-minimal-descent-transport` compiled
this file cleanly in both sandbox mode and its final library module name. The
initial compile exposed that canonical pullbacks require Noetherian/finite-type
instances. These were made explicit only on `IsSchlessingerOne`; the final theorem
infers finite type from its existing `Module.Finite` hypothesis. No mathematical
hypothesis or conclusion was changed. No statement dispute or correction.

## Second reading by Q160

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
