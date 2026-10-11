## Worker report

The module states the criterion from Stacks Algebra, Lemma 00TS, implication (2) => (4):
for a field `k` and commutative ring `S` equipped with an algebra structure, the hypotheses
`[IsAlgClosed k]` and `[Algebra.FiniteType k S]` express algebraic closedness and finite type.
The binder `m : Ideal S` with `hm : m.IsMaximal` is the maximal ideal. The hypothesis
casts the natural-number vector-space dimension
`Module.finrank m.ResidueField (TensorProduct S m.ResidueField (KaehlerDifferential k S))`
to `WithBot ℕ∞` and bounds it by `ringKrullDim (Localization.AtPrime m)`. The tensor
product is the fibre of the Kähler differential module over the residue field (the order
`m.ResidueField ⊗[S] Ω` is the Mathlib representation carrying the residue-field module
structure). The conclusion `∃ g : S, g ∉ m ∧ Algebra.Smooth k (Localization.Away g)`
expresses exactly that some element outside `m` gives a smooth principal localization.

Dependency declarations used: `Algebra.FiniteType` (Mathlib.RingTheory.FiniteType),
`Localization.AtPrime` and `Ideal.ResidueField` (Mathlib.RingTheory.Localization.AtPrime.Basic),
`KaehlerDifferential` (Mathlib.RingTheory.Kaehler.Basic), `ringKrullDim`
(Mathlib.RingTheory.KrullDimension.Basic), `Algebra.Smooth` (Mathlib.RingTheory.Smooth.Basic),
and `Algebra.IsSmoothAtPrime`/`Algebra.singularIdeal` (Sheaf.RingTheory.SingularIdeal,
though the conclusion is written in the explicit existential form required by the node).
The algebraically closed field notion is Mathlib's `IsAlgClosed`.

Edge cases checked from the source split: dimension zero (`d = 0`), zero equations in a
presentation (`c = 0`, whose Jacobian minor is the empty minor equal to 1), and the zero
ring (excluded because a maximal ideal cannot exist). The universes of `k` and `S` are
independent and the residue-field tensor product is formed over `S`.

Searches made: `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` for algebraic-closed,
Kähler, smooth-at-prime, and differential-dimension declarations; Mathlib search results
found only the general `Algebra.Smooth`, `IsAlgClosed`, `KaehlerDifferential`, and
`ringKrullDim`, with no theorem matching the differential bound. The project search found
`Algebra.IsSmoothAtPrime` in `Sheaf.RingTheory.SingularIdeal`, which is used conceptually;
no existing declaration states this theorem.

## Earlier second reading (a previous round; superseded)

The node and module were read together. Every node hypothesis is represented by one binder
or instance: algebraically closed field, finite-type algebra, maximal ideal, and the stated
fibre-dimension inequality. The conclusion has the same witness `g ∉ m` and smooth
localization `S_g`; no hypothesis or conclusion clause was added or omitted. The cast to
`WithBot ℕ∞` matches the node's comparison with Mathlib's Krull dimension codomain.

## Second reading by E1

Read the item's JSON, all seven statement dependency nodes and their recorded declarations,
the delivered module, Stacks algebra.tex at 00TR/00TS, and the tag map. The Stacks source is
available on this machine at /home/ubuntu/c1-stacks-review/algebra.tex (00TS at lines
38505–38607); no extra standing hypothesis occurs in this section.

Object/hypothesis/conclusion checklist, with verdicts:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`. Exact.
  The dependency's algebraically closed clause is `IsAlgClosed` (Basic.lean:62), rather
  than the stronger datum of a chosen algebraic closure of another field.
- Finite type k-algebra S: `(S : Type v) [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S]`. Exact. FiniteType.lean:39 is finite generation of the
  top subalgebra, equivalent to the dependency's finite polynomial presentation map.
- Maximal ideal m: `(m : Ideal S) (hm : m.IsMaximal)`. Exact. The class-valued
  explicit proof supplies primality for the localization and residue field; no extra
  prime or local-ring assumption is imposed.
- Local ring S_m: `Localization.AtPrime m`. Exact: localization at `m.primeCompl`
  (Localization/AtPrime/Basic.lean:57).
- Residue field κ(m): `m.ResidueField`. Exact: abbreviation for the residue field of
  `Localization.AtPrime m` (LocalRing/ResidueField/Ideal.lean:33). It is not an
  arbitrary field or a quotient with a different algebra action.
- Kähler module Ω[S/k]: `KaehlerDifferential k S`. Exact. Read Basic.lean:153,
  the universal derivation and `linearMapEquivDerivation` at line 327; its cotangent
  construction represents the dependency's universal module, without a private copy.
- Differential fibre and its κ-dimension: `Module.finrank m.ResidueField
  (TensorProduct S m.ResidueField (KaehlerDifferential k S))`. Exact. The factors
  are exchanged from the written node by the canonical tensor commutation equivalence,
  with the residue field first to carry its module structure. Finite type implies
  `KaehlerDifferential.finite` (Basic.lean:433); scalar extension remains finite, so
  finrank is the actual vector-space dimension, not the infinite-dimensional fallback 0.
- Krull dimension and bound: the hypothesis `h` casts this finite dimension to
  `WithBot ℕ∞` and compares it to `ringKrullDim (Localization.AtPrime m)`. Exact.
  KrullDimension/Basic.lean:30 is the dimension of PrimeSpectrum, with bottom and infinity.
- Smoothness conclusion: `∃ g : S, g ∉ m ∧ Algebra.Smooth k (Localization.Away g)`.
  Exact witness, nonmembership, and smooth principal localization in the same order.
  Read Smooth.Basic:540 (formal smoothness plus finite presentation, equivalent to the
  Stacks definition) and the dependency `Algebra.IsSmoothAtPrime` in SingularIdeal.lean:
  the existential here is exactly its defining body, as explicitly requested by the
  node. No second smoothness definition is introduced, and no unused import is needed.

No additional Noetherian, finite-dimensional, perfect-field, regularity, or finite
presentation hypothesis is present. These properties needed by the proof follow from
its stated hypotheses. There are no new nodes, dependency modules, or statement corrections.

Edge cases: zero S and empty Spec are excluded by maximality, exactly as in the source;
a zero differential fibre and local dimension d=0 remain included. Zero variables and
zero equations are allowed; the empty Jacobian minor is 1. There is no index-set binder
or characteristic restriction. Universes u and v are explicit and independent; every
ring and field size is covered, with no lower-universe test-object quantification.

Independent searches (also logged in searches.jsonl): LeanSearch query "cotangent space
dimension bounds smoothness at closed points of an affine algebra over an algebraically
closed field" returned Internal Server Error, so no mathematical verdict is inferred
from that unavailable service. Loogle `KaehlerDifferential, Module.finrank` returned no
hits. LeanFinder query "A bound on the dimension of the fibre of Kahler differentials
by the Krull dimension of a local ring gives a smooth principal neighbourhood of a
rational maximal ideal" returned eight related smooth-locus and standard-smooth results;
none has this dimension-bound hypothesis. The grep search `finrank|IsAlgClosed|krullDim`
in Mathlib/RingTheory/Smooth had no hits. Direct rg of the project, upstream Lean, and
upstream name map for `finrank.*(kaehler|differential)`,
`smooth.*(cotangent|krull|algclosed)`, and `differentials.*bound` found the general-prime
00TT theorem (different hypothesis: topological dimension at a point) and upstream
`Algebra.IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed` (assumes regularity, not the
bound). Opened both signatures; neither states this node. CartierEquality concerns
p-bases, not this criterion. The existing Smooth and Kähler notions are reused.

Mismatch found and repaired: H8, the original theorem docstring only named three proof
ideas rather than carrying the node's proof. Expanded it to all seven steps: residue
field identification/Noetherianity, exact cotangent sequence, regularity, local regular
sequence, global complete intersection, full-rank Jacobian minor (including C=0), and
combining principal localizations. The mathematical signature and node lean.statement
are unchanged and verbatim equal. No hollow definition or proof beyond the single named
sorry theorem is introduced; all variables and universes are bound explicitly.

Validation: scompile.py compiled the delivered module cleanly (exit 0, 1.4 s);
checked the signature against lean.statement byte for byte and all Lean lines ≤100 characters.
