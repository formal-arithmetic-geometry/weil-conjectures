## Worker report

The module states `AlgebraicGeometry.exists_containment_locus`, the affine-ideal
form of the closed containment locus lemma.  Its binders render a morphism
`f : X ⟶ S`, a degree `d`, an `S`-scheme `T`, a Hilbert subscheme ideal `I`
with `IsHilbertSubscheme f d T I`, and an arbitrary closed-subscheme ideal `J`.
The conclusion `∃ K` gives the closed ideal on `T`; the quantified `T'` and
`φ` render arbitrary base change, and the equivalence of ideal inclusions is
the factorization universal property.

Dependencies used: `WeilConjectures.AlgebraicGeometry.Hilbert.Curve`,
including `AlgebraicGeometry.IsHilbertSubscheme`,
`AlgebraicGeometry.Scheme.IdealSheafData`, `AlgebraicGeometry.baseChangeMap`,
and `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` through the
Hilbert-subscheme notion.  The scheme, base-change, finite locally free, and
closed-immersion notions are the recorded Mathlib/source declarations in the
node dependencies.

Edge cases checked: `d = 0` is allowed by `d : ℕ`; arbitrary universe `u`,
empty schemes, and arbitrary (including empty) base-change schemes `T'` are
not excluded.  No characteristic or nonemptiness assumptions are introduced.

Searches: `rg` over `WeilConjectures/` and `lean/Sheaf/` for containment-locus
and `IsHilbertSubscheme`; the source theorem
`AlgebraicGeometry.exists_idealSheafData_le_ker_iff_comap_le` was found in
`WeilConjectures/AlgebraicGeometry/Hilbert/Curve.lean` (around line 840) and
used as the exact formal shape.  `msearch.py leanfinder` and `loogle` searches
for a closed Hilbert containment locus found no Mathlib declaration.

## Earlier second reading (a previous round; superseded)

The node and module were read together.  The morphism, Hilbert ideal,
containment ideal, existential closed ideal, arbitrary base-change object and
morphism, and both directions of the universal equivalence each appear in the
Lean signature.  The source wording's closed subschemes are represented by
`IdealSheafData`; no hypotheses or clauses were added or dropped.

## Second reading by F1

Independent review of the node, the delivered module, its dependencies and the
source declaration. Verdict: the mathematical signature agrees with the node,
but the delivery violated H4 by restating an existing source theorem. Removed
`lean/Sheaf/AlgebraicGeometry/Hilbert/ContainmentLocus.lean` and recorded
`AlgebraicGeometry.exists_idealSheafData_le_ker_iff_comap_le` from
`WeilConjectures.AlgebraicGeometry.Hilbert.Curve` with `existing: true`, branch
`slopmaster2`. The Worker report above describes the original delivery, not the
final existing-declaration attachment. The existing theorem is still `sorry`;
this is a stage-2 statement attachment, not a claim that its proof is complete.

Source checked: the local Stacks source copy `/home/ubuntu/c1-stacks-review/pic.tex`,
lines 32–58 (standing definition of the Hilbert functor), and lines 123–166,
`lemma-hilb-d-of-closed`, Tag 0B97, specifically the claim in its proof. The claim
requires only a finite locally free Hilbert subscheme and a closed immersion.
Representability in the enclosing lemma is used after the claim, not in its
proof. No separatedness, Noetherian, field, characteristic, finite-presentation
condition on the ambient morphism, or representability hypothesis belongs here.
The node's arbitrary closed subscheme of X_T is covered by the same argument:
it uses only its inverse image in Z, a closed subscheme Spec(B/J). It does not
require that W descend from S.

Object/hypothesis/conclusion inventory, with the Lean rendering and verdict:

1. Arbitrary schemes X and S and morphism f: the source's section Relative
   has `variable {X S : Scheme.{u}} (f : X ⟶ S)` at Curve.lean:583.
   The theorem uses f, so all three become parameters. No other section
   variables or instances enter its type. Exact.
2. Degree d >= 0: `{d : ℕ}`. All nonnegative integral degrees, including
   zero, are included. Exact.
3. Scheme T over S: `{T : Over S}`, with underlying scheme `T.left` and
   structure morphism `T.hom`. This is the category of all S-schemes,
   not affine schemes or schemes with a selected extra property. Exact.
4. Ambient X_T: `pullback f T.hom`. The base-change node explicitly identifies
   this as X_T, `pullback.snd` as its map to T and `pullback.fst` as its map
   to X. Exact.
5. Closed immersion W into X_T: `J : (pullback f T.hom).IdealSheafData`.
   `J.subschemeι` is a closed immersion. Every closed immersion is represented
   by its kernel ideal up to isomorphism over X_T, by Mathlib's
   `AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData`
   (Morphisms/ClosedImmersion.lean:180). Thus this presentation loses no W
   and assumes no affine property of X_T. Exact.
6. Closed subscheme Z of X_T: `{I : (pullback f T.hom).IdealSheafData}`,
   likewise with closed immersion `I.subschemeι`. Exact.
7. Z -> T finite locally free of degree d: `hI : IsHilbertSubscheme f d T I`.
   Opened Hilbert/Defs.lean:78: this is precisely IsFinite, Flat,
   LocallyOfFinitePresentation for `I.subschemeι ≫ pullback.snd f T.hom`,
   together with `∀ t, ... .finrank t = d`. It does not ask for Cartier,
   smooth, integral or invertible subschemes. Opened the recorded dependency
   Morphisms/FiberDegree.lean:778–792: IsFiniteLocallyFree consists of the
   same three properties, and IsFiniteLocallyFreeOfDegree specifies fibre
   degree d. Mathlib FlatRank.lean defines finrank as the finite flat module
   rank; over residue fields this is the dimension of the fibre algebra,
   matching the node's degree. Exact, including over nonreduced bases.
8. Existence of a closed T_W in T: `∃ K : T.left.IdealSheafData`.
   Its associated `K.subschemeι` is the required closed immersion. Exact.
9. Every base change T' -> T over S, after choosing a single K:
   `∀ (T' : Over S) (φ : T' ⟶ T)`. No condition on φ; existential K precedes
   both universal binders. Exact.
10. T' -> T factors through T_W: `K ≤ φ.left.ker`. Opened Mathlib
    Morphisms/ClosedImmersion.lean:207 onwards, its lift universal property;
    kernel containment is exactly factorization through `K.subschemeι`.
    This is scheme-theoretic factorization, not set-theoretic containment.
    Exact.
11. Z_T' factors through W_T':
    `J.comap (baseChangeMap f φ) ≤ I.comap (baseChangeMap f φ)`.
    Ideal inclusion is reversed relative to subscheme containment. Opened
    IdealSheaf/Functorial.lean:39–55: comap cuts out the scheme-theoretic
    pullback, with `comapIso` identifying it with the fibre product. Opened
    PicardFunctor.lean:296–314: baseChangeMap is the induced map X_T' -> X_T
    and its square with the projections to T is cartesian. Exact.
12. Both directions: `↔` joins clauses 10 and 11. Exact.
13. Compatibility with arbitrary base change in T: already encoded by the
    universal quantification, not an extra choice of unrelated ideals. For
    ψ: T'' -> T, pull back K to `K.comap ψ.left`. A test map T' -> T''
    factors through this closed subscheme precisely when its composite with
    ψ factors through K. Applying the displayed equivalence to that composite
    gives containment of the twice-pulled-back Z and W. Comap and
    baseChangeMap respect composition. Hence the pulled-back K has the same
    universal property as the containment ideal over T'', and they coincide:
    testing each universal property on the other closed subscheme gives
    inclusions both ways. This is exactly the node's concluding Yoneda
    argument, not a weaker pointwise assertion. Exact.

Dependency signatures read: Mathlib Scheme.lean:42 and :74 (Scheme and Hom);
`def-pc-base-change` and its landed BaseChangeConventions.lean (the ambient and
iterated pullback conventions); `def-pc-finite-locally-free` and its source
classes cited above; `def-weil-closed-immersion` and Mathlib's IsClosedImmersion
(closed embedding and surjective stalk maps). No dependency module was needed:
the source Hilbert predicate is the already existing conjunction of these
properties, not a missing or specialized private notion. No new definition
nodes, dependency modules or statement correction occur in the delivery.

Edge cases: d = 0 gives the empty Hilbert subscheme and the entire base as its
containment locus (K = bottom ideal). W empty (unit ideal), W the whole ambient
(zero ideal), empty Z, empty X, empty T and empty test T' are all admitted.
There is no index-set binder or nonemptiness condition. A rank-d Hilbert
subscheme over a nonempty base excludes the zero object for d > 0 by its
actual degree hypothesis, not an extra Lean assumption. All characteristics
and general commutative affine coordinate rings are covered. The arbitrary
universe u is the usual ambient universe for schemes; any collection of these
objects fits in a common universe. No field or fixed-universe bound is added.

Independent searches (different descriptions from the first worker):

- `msearch.py ... leanfinder "closed subscheme locus where a finite locally
  free subscheme factors through a closed immersion"`: 8 hits, including
  IsClosedImmersion.lift, instSubschemeι and inclusion, no containment-locus
  theorem in Mathlib.
- `msearch.py ... loogle '"comap", "ker"'`: 12 algebra/group kernel hits,
  no scheme containment-locus theorem.
- `msearch.py ... leansearch "finite locally free closed subscheme containment
  universal closed locus"`: unavailable, Internal Server Error; no verdict
  inferred from this service failure.
- `rg` for `containment`, `le_ker_iff_comap_le`, and `IsHilbertSubscheme` in
  Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf: found the exact
  source theorem in Hilbert/Curve.lean:839–844, and its uses at :1002, :1004.
  Opened the theorem and section context instead of relying on its name.
  No separately defined containment notion or additional dependency needed.

Mismatches repaired: H4, duplicate theorem despite the Worker report itself
finding the existing signature, fixed by dropping the module and attaching
that exact source declaration. H8, the removed module's proof docstring only
summarized the three proof steps; no new declaration or docstring is delivered.
For the record the node's proof is: (1) work affine on T and use
lem-pc-affine-containment-ideal on the ideal of W in the finite projective
coordinate algebra of Z; (2) uniqueness on all quotient tests makes these
ideals localize compatibly, and
lem-weil-pbc-affine-ideals-closed-subscheme glues them; (3) on affine test
covers the coefficient vanishing criterion gives both factorizations using
lem-weil-pbc-closed-immersion-factor-ideal-inclusion and
lem-weil-pbc-closed-immersion-lift-ideal-kills-sections; the same universal
property after composition proves arbitrary-base-change compatibility by
uniqueness. No mathematical signature mismatch was found. The record's
lean.statement is copied verbatim from the existing source signature; its
section-bound X, S, f are explicitly checked in the scratch type ascription.

Validation: `scompile.py F1 lem-pc-hilb-containment-locus
scratchpad/CheckExisting.lean` compiled the explicit full type ascription of
the existing declaration on the server in 2.2 seconds, exit 0, with no warning.
The scratch file is not part of the delivery. There are no new modules to
compile, hollow definitions, new proofs or unbound variables in this delivery.
