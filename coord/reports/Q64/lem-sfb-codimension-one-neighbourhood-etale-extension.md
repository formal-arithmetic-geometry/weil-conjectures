## Worker report

The module states `AlgebraicGeometry.Scheme.exists_finite_etale_model_of_codimension_one_neighbourhoods`.
Its only theorem has proof `sorry`; there are no definitions, helper axioms, new nodes,
dependency repairs, or statement corrections.

Hypothesis-by-hypothesis correspondence:

- `B : Type u`, `[CommRing B]`, `[IsDomain B]`, `[IsRegularRing B]` give exactly the
  Noetherian regular integral domain. `IsRegularRing` extends `IsNoetherianRing`;
  no second Noetherian assumption is necessary.
- `f : B`, `hf : f ≠ 0` give the specified nonzero element.
- `X` is written literally as `Spec (CommRingCat.of B)` throughout, and `N` as
  `Spec (CommRingCat.of C)`. The structural map is always
  `Spec.map (CommRingCat.ofHom (algebraMap B C))`, never an arbitrary map.
- `[CommRing C] [Algebra B C] [Module.Finite B C]` give exactly the finite B-algebra.
  Finiteness of its structural map is the standard affine finite-morphism criterion.
- `PrimeSpectrum.basicOpen f` is the open D(f) = Spec B[1/f], with the restricted
  scheme structure. This uses the existing canonical open-subscheme encoding, rather
  than a new definition. Mathlib's `Scheme.isOpenImmersion_SpecMap_localizationAway`
  and `Scheme.Hom.opensRange_localizationAway` identify its inclusion with the
  localization map on spectra. The use of D(f) does not replace U by a different open.
- `hU` says the restriction `q ∣_ D(f)` is etale. Morphism restriction is precisely the
  open inverse-image realization of the stated base change `N ×_X U → U`.
- `V` is indexed by source points z and a proof that their image prime has height one
  and contains f. `hV` says z lies in the selected neighbourhood; `hVet` says the
  composite of its inclusion with q is etale. This is equivalent to the node's indexing
  by a boundary height-one prime and each point above it: q(z) is that unique prime.
  Empty fibres require no neighbourhood choice. The family can be arbitrary among
  those satisfying the stated conditions. Mathlib's prime-ideal `Ideal.height = 1`
  agrees with the node's nonzero/no-intermediate-prime condition in a domain:
  zero is the unique height-zero prime, and prime height is the supremum of chain
  lengths below the prime (Height.lean:31-46, 253-266).
- `O` is an open of N and `hO` is precisely its equality with the preimage of D(f)
  joined with the supremum of all the chosen neighbourhoods. No larger open is substituted.

Conclusion, clause by clause:

- `∃ W : X.Opens` includes the assertion that W is open. The first conjunct gives
  its underlying set as the complement of `q '' Oᶜ`, exactly the displayed formula.
- `PrimeSpectrum.basicOpen f ≤ W` gives U contained in W; the next conjunct places
  every prime of height one in W, including primes whose fibre is empty.
- `IsFinite (q ∣_ W)` and `Etale (q ∣_ W)` give the finite etale base change to W.
- The existential `H : Scheme.{u}`, `p : H ⟶ X`, with `IsFinite p ∧ Etale p` gives
  a new finite etale model. Its two comparisons are actual scheme isomorphisms
  `pullback p j ≅ pullback q j`. Each has the displayed equation with `pullback.snd`,
  so each is an isomorphism over the relevant base, first W and then U. Both use
  the same H and p. There is no assertion identifying H with N.
- The final universal clause is over `x : Spec B` outside W and states
  `IsRegularLocalRing (X.presheaf.stalk x)` and `2 ≤ ringKrullDim (X.presheaf.stalk x)`.
  These are ambient stalks, not stalks of a closed complement.
- No normality of C or henselianity of B appears anywhere.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, lines 193-200.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: read its full definition and docstring.
  The node's ring clauses use `IsRegularRing` and `IsRegularLocalRing` from
  `Mathlib.RingTheory.RegularLocalRing.Defs`, lines 47-55 and 91-98, reexported by
  this recorded dependency module. The scheme predicate is not imposed on B.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, lines 469-480.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, lines 132-144;
  `Mathlib.RingTheory.Localization.Away.Basic`: `IsLocalization.Away`, lines 45-51.
  Their affine open encoding is supplied by `Mathlib.AlgebraicGeometry.OpenImmersion`,
  lines 329-346 (`isOpenImmersion_SpecMap_localizationAway`, `opensRange_localizationAway`).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, lines 34-39;
  open inclusions and restrictions are `Scheme.Opens.ι` and `Scheme.Hom.morphismRestrict`
  in `Mathlib.AlgebraicGeometry.Restrict`, lines 42-53 and 569 onwards.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, lines 35-42.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, lines 37-45.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, lines 94-118; the scheme instance is supplied by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, lines 27-32.

Proof-dependency imports include the published
`WeilConjectures.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension`,
whose full theorem and proof docstring were read. Its declaration
`Scheme.exists_finite_etale_extension_of_regular_codimension_two_boundary`
extends a finite etale cover over an open with precisely the ambient regular
stalk/dimension hypotheses this node establishes. The other stated proof inputs
are Mathlib etale composition, source-locality and base-change instances, finite
base-change, `Scheme.Hom.isClosedMap`, `Scheme.Hom.finite_preimage_singleton`,
`StructureSheaf.IsLocalization.to_stalk`, `functionField_isFractionRing_of_affine`,
and `Localization.AtPrime`. Their owning modules are imported publicly when
needed in the signature, and otherwise as proof imports. The seven-step
natural-language proof in the theorem docstring follows all seven DAG proof steps.

Sources read: `literature/stacks-project/pione.tex`, lines 5066-5080,
`lemma-local-purity` (0BMA), and lines 5303-5338, `lemma-extend-pure` (0EY7).
These give extension of the restricted cover, and do not require that the
original algebra C itself be normal. The Noetherian hypothesis required by 0EY7
holds for Spec B. The original finite cover is used only to construct W.

Edge cases checked before drafting:

- f a unit: D(f) = X, so O = N and W = X; H may be the original finite etale cover.
- B a field: every nonzero f is a unit, and the height-one neighbourhood family is empty.
- dimension B at most one: all points lie in W, so again the already etale cover suffices.
- C the zero ring: N is empty, the indexed family has no elements, and W = X;
  the empty finite etale model is permitted because no domain/nontriviality is imposed on C.
- Empty fibres over boundary primes impose no neighbourhood data and remain in W.
- A nonnormal finite C is permitted. For B = k[x,y], f = x and
  C = B × B/(x,y), all hypotheses hold, W excludes the origin, and its missing
  ambient stalk has dimension two. H = Spec B is a model of the restriction;
  H is not required to equal N. This checks the important ambient-stalk distinction.
- There is no dimension finiteness restriction or henselianity assumption. Rings
  and schemes use an arbitrary universe u, as do the published geometric APIs.

Searches actually run with the prescribed msearch.py logger:

1. LeanFinder: "A finite morphism over a regular Noetherian integral affine scheme which is
   etale on a principal open and on source neighbourhoods above all boundary height one points
   has a finite etale model on the whole base". Eight hits: local algebra etale-locus,
   standard-smooth and finite-presentation results; no exact statement.
2. Loogle: `AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite`. One hit,
   `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`; its etale neighbourhood
   of the target is different from this extension theorem and its exact W.
3. Grep: `(codimension|purity|height.one).*(etale|Etale)|(etale|Etale).*(codimension|purity)`.
   Zero Mathlib hits.
4. LeanSearch: "finite etale covers extend across codimension two regular scheme from source
   neighbourhoods above height one primes". Eight hits, including local etale-locus
   results and the etale scheme category; no exact statement.
5. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for codimension-one, codimension-two,
   purity, and this node id found the existing general codimension-two extension input
   and regular-integral-divisor results. Neither gives this precise open construction
   and source-neighbourhood hypothesis. Searching the exact node id and proposed theorem
   name in the upstream names table and source found no declaration of the item.

No disputed statement or node fault was found. The expected sole warning is that
this theorem uses `sorry`; compilation is performed only by scompile.py.

## Second reading by Q64

A separate in-thread rereading of the full node and final signature checked the
nonzero element, the finite B-algebra, the etale restriction, each boundary fibre,
the neighbourhood membership and etaleness, the exact union O, the exact formula
for W, both inclusions in W, finiteness and etaleness over W, both over-base
isomorphisms for one H, and ambient stalk regularity and dimension. No mathematical
hypothesis or clause was missing. No normality, henselianity or identification of
H with N was introduced. The first compile exposed that field notation `.ι` on
`PrimeSpectrum.basicOpen f` does not recover the ambient scheme; the final signature
uses explicit `Scheme.Opens.ι (X := Spec (CommRingCat.of B))` for these pullbacks.
This changes only elaboration, not the open or map. This is a self-check; the
maintainer supplies the independent review specified in the dispatcher's brief.
