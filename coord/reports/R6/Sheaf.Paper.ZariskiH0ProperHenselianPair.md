## What changed

Proved `AlgebraicGeometry.zariski_h0_proper_henselian_pair` in
`Sheaf.Paper.ZariskiH0ProperHenselianPair`, with its signature, original docstring,
and public imports unchanged. All work is in this item and its existing DAG node.
No source-library module, definition, public interface, or target was changed.

The proper henselian connectedness argument already exists as the proved theorem
`Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter` in
`WeilConjectures.AlgebraicGeometry.HenselianConnectedness`. Reuse that theorem for
spectrality and connected nonempty intersections. Mathlib's pullback range formula
and quotient-spectrum range formula identify the closed fibre's image.

Two proved private helpers supply the remaining categorical glue. The image
homeomorphism gives an equivalence of sheaf categories via `sheafCongr`; its
pushforward comparison is componentwise the identity. The existing
`isIso_inverseMate_of_equivalences` and Mathlib's `unit_mateEquiv_symm` express the
actual fibre-projection unit as the closed-image unit composed with two
isomorphisms. Apply `TopCat.spectral_closed_restriction` to the latter and compose
its bijection with the two isomorphism components. This preserves exactly the
Type u inverse-image adjunction unit appearing in the theorem.

The helpers specialize the image-transport construction of
`EmbeddingPushforwardTransport` and `ClosedEmbeddingRestrictionTransport` to
spaces and sheaves in the same universe. The existing public transport theorem
has Type (u + 1) coefficients and cannot directly be applied here. No new public
lemma or unfinished obligation was introduced for that specialization.

Updated the node's proof, proof_deps, and proof_origin to describe this assembly.
The closed-subscheme, integral Stein, henselian extension, and connected-fibre
route of Stacks 0A0B is retained inside the reused connectedness theorem; the
unit's statement and realized steps are preserved. The packaging lemma is a
proved tool from sk-thm-iff, using the same argument, not a replacement of the
unit-level route.

Validation: lcompile.py compiled the completed module cleanly in 3.5 seconds.
A further compile with `#print axioms` reported precisely
`[propext, Classical.choice, Quot.sound]` for the main theorem (9.3 seconds).
LeanFinder, Loogle, and grep searches ran through msearch.py; direct searches
also located and checked the relevant source declarations. Import-direction
checks for the two added WeilConjectures proof imports passed.

The construction includes empty schemes and empty images: the equivalence of
sheaf categories, unit equation, and spectral criterion require no chosen point.
No noetherianity or nontriviality assumption was added, and irreducibility of a
point closure supplies exactly the hypothesis needed by connectedness.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.zariski_h0_proper_henselian_pair`
(node `lem-weil-pbc-zariski-h0-proper-henselian-pair`).

Proved 1 of 1 sorries. Zero sorries remain in the item; zero were added elsewhere;
zero were split off. The theorem's transitive proof dependencies also introduce
no additional axioms, as verified by the axiom check above.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine`;
- `WeilConjectures.RingTheory.HenselianPairPrimeConnected`;
- `WeilConjectures.RingTheory.IntegralOverHenselianPair`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.

They are used inside the existing connectedness proof rather than applied again
in this module. No claim is made that any of these modules leaves the targets'
transitive import closure. No Lean module or declaration is withdrawn.

The following are the complete removed direct proof dependencies of this node:

- `def-weil-closed-immersion`;
- `def-weil-proper-morphism`;
- `lem-weil-pbc-qcqs-over-affine`;
- `lem-weil-pbc-qcqs-scheme-spectral`;
- `def-weil-connected-scheme`;
- `lem-weil-pbc-closed-subset-closed-subscheme`;
- `lem-weil-pbc-proper-fp-permanence`;
- `def-weil-pbc-stein-factorization`;
- `lem-weil-pbc-stein-factorization-affine`;
- `lem-weil-pbc-integral-over-henselian-pair`;
- `lem-weil-pbc-scheme-sober`;
- `lem-weil-pbc-henselian-pair-prime-connected`;
- `lem-weil-pbc-connected-fibres-quotient-preimage-connected`.

The connectedness packaging replaces their separate applications here; they
remain available and needed within its argument. The hand-written proof using
fibre-product points and a nonzero tensor product is unnecessary: Mathlib's
`Scheme.Pullback.range_fst` already gives the required image equality. Retain
the fibre-product-points dependency to record that exact mathematical fact.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's six-step proof is a valid mathematical
route, but most of its geometry has already been implemented and proved in
`HenselianConnectedness`. Reusing it avoids repeating that argument. The final
passage from the closed-image inclusion to the displayed fibre-projection unit
also requires a transport argument; the private proof supplies it explicitly,
without identifying the two units by definitional equality.

No change record is needed: all existing public statements, definitions and
public import visibility are unchanged. No new nodes or forced adaptations.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
