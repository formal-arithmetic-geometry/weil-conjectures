## Worker report

The module `Sheaf.RingTheory.LocalRingHomTensorProductFieldExtensionFaithfullyFlat`
states `Localization.localRingHom_tensorProduct_fieldExtension_faithfullyFlat`, with
`sorry` as its only proof. It introduces no definitions and changes only the item's
`lean` record. No statement correction or disputed statement is needed.

Hypothesis and clause correspondence:

- The field `k` is `{k : Type u} [Field k]`.
- The field extension `K/k` is `{K : Type v} [Field K] [Algebra k K]`.
- The commutative `k`-algebra `A` is `{A : Type w} [CommRing A] [Algebra k A]`.
- The finitely presented `A`-algebra `B` is `{B : Type x} [CommRing B]
  [Algebra A B] [Algebra.FinitePresentation A B]`.
- `[Algebra k B] [IsScalarTower k A B]` expresses the induced `k`-algebra
  structure on the `A`-algebra `B`. This records composition of the given maps,
  rather than imposing a further restriction on `A` or `B`: every such algebra
  has this structure by composing `k → A → B`.
- A prime `q` of `B` is `(q : Ideal B) [q.IsPrime]`.
- `B_K = B ⊗_k K` is the existing Mathlib tensor product `B ⊗[k] K`.
- A prime `q_K` of that tensor product is
  `(qK : Ideal (B ⊗[k] K)) [qK.IsPrime]`.
- Its contraction is `q` precisely when
  `h : q = qK.comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[k] K)`.
  This inclusion sends `b` to `b ⊗ₜ[k] 1`.
- The canonical localized map is
  `Localization.localRingHom q qK Algebra.TensorProduct.includeLeftRingHom h`,
  with source `Localization.AtPrime q` and target `Localization.AtPrime qK`.
  Mathlib's `Localization.isLocalHom_localRingHom` already supplies its localness;
  no independent localness assumption is imposed.
- Faithful flatness of this exact map is the conclusion `.FaithfullyFlat`,
  namely Mathlib's `RingHom.FaithfullyFlat`.

Dependencies and declarations read:

- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`;
  its fields give the ring map defining the field extension.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`. The item uses the
  ring-level finite-presentation notion explicitly described by this dependency,
  not a scheme morphism. It is already `Algebra.FinitePresentation` in
  `Mathlib.RingTheory.FinitePresentation`, whose signature and docstring were read.
  The recorded module's `LocallyOfFinitePresentation.SpecMap_iff` identifies
  its affine specialization with `RingHom.FinitePresentation`. Thus the recorded
  dependency is usable through its existing underlying algebraic notion; no
  replacement module or duplicate scheme predicate is needed.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. Also read the recorded
  `Ideal.ResidueField` and `Ideal.Fiber` declarations in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`; those additional clauses
  are not used by this item. The canonical map is Mathlib's `localRingHom`.
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat` in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and `RingHom.FaithfullyFlat`
  in `Mathlib.RingTheory.RingHom.FaithfullyFlat`; the latter is used directly.

All imports supply notions appearing in the statement; the faithful-flat-ring-map
module transitively imports the localization-at-prime API. The docstring gives
all three DAG proof steps and their node names. No step is proved at stage 2.

Source checked: the local literature checkout has no `stacks-project/varieties.tex`,
so I opened https://stacks.math.columbia.edu/tag/0C4Y directly. Its part (1)
states faithful flatness of the corresponding local-ring homomorphism, and its
proof gives the affine tensor-product map and the local-flat argument. The
current displayed number is Lemma 33.5.1; the node's numbering 33.9 is stale,
but its stable tag and label identify the intended result. The node's additional
finite-presentation hypothesis is retained exactly as required.

Edge cases checked before writing: `K = k` and `A = B` are allowed; there is no
nontriviality assumption on either algebra beyond the existence of the specified
primes. A zero ring has no primes, so its case is vacuous rather than excluded
by an extra hypothesis. No reducedness, Noetherian, separability, algebraicness,
finite field extension, or characteristic restriction is added. Infinite and
inseparable field extensions are allowed. The finite-presentation predicate
permits zero variables and zero relations. Each ring has an independent universe
`u`, `v`, `w`, or `x`. All variables and universes are explicitly bound and
`autoImplicit` is disabled.

Searches for an existing combined statement (actual calls are in `searches.jsonl`):

- `msearch.py leansearch`, query `localization at corresponding primes of a field
  extension tensor product is faithfully flat`: service unavailable, Internal
  Server Error. No mathematical conclusion is drawn from this outage.
- `msearch.py leanfinder`, same query: eight hits, including `instFlatAtPrime`,
  `RingHom.Flat.localRingHom`, and
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`; none is the combined statement.
- `msearch.py loogle`, query `RingHom.Flat.localRingHom, Module.FaithfullyFlat`:
  zero hits.
- `msearch.py grep`, query
  `FaithfullyFlat.*localRingHom|faithfullyFlat.*localRingHom|of_flat_of_isLocalHom`:
  six hits concerning the general flat-local theorem and its applications,
  no combined field-extension/localization theorem.
- `rg` in Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the chosen declaration name and
  `localRingHom.*faithfullyFlat|fieldExtension.*faithfullyFlat`: no matches.
- `rg` in the project and source for stalk faithful flatness and
  `localRingHom.*Faithfully` found only the general flatness-localization module
  and a scheme-flatness proof, neither the item's statement.
- `grep -rn` for the item's exact blueprint id in `WeilConjectures`: no matches.

Validation: server single-file compilation and `deliver2.py --no-push` are run
for this statement; the independent second reading is left to the next worker.

## Second reading by M1

Independent reading of the sandbox node and module, all four statement-dependency
nodes, and their Mathlib declarations. Verdict: the Lean states exactly the node;
no mathematical mismatch, missing definition, or unusable dependency was found.
The theorem, node record, and module were left unchanged. This reading adds only
this report section and independent search evidence.

Source: I read the raw Stacks `varieties.tex`, section `section-local-rings`,
label `lemma-change-fields-flat`, including its proof and surrounding text:
https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex .
The section has no standing finite-type, Noetherian, separability or characteristic
hypothesis. Tag 0C4Y(1) asserts faithful flatness and localness of the stalk map
for any scheme over a field after any field extension. Its affine proof identifies
that map with localization of the tensor inclusion at corresponding primes.
The node deliberately specializes this to a finitely presented A-algebra B;
this hypothesis is already in the node and is retained in Lean. The source's
other three conclusions are not clauses of this node and are not required here.
The stale lemma number in the node does not affect the stable tag or label.

Objects, hypotheses, and conclusions, listed independently and matched:

1. Base field k: `{k : Type u} [Field k]`. Exact; no characteristic restriction.
2. Field extension K/k: `{K : Type v} [Field K] [Algebra k K]`. Exact;
   `Algebra.algebraMap` is the ring homomorphism in `def-pc-field-extension`.
   Neither finite degree nor algebraicness nor separability is assumed.
3. Commutative k-algebra A: `{A : Type w} [CommRing A] [Algebra k A]`.
   Exact; no domain or Noetherian assumption.
4. Finitely presented A-algebra B: `{B : Type x} [CommRing B] [Algebra A B]
   [Algebra.FinitePresentation A B]`. Exact: the class's `out` gives a
   surjective map from `MvPolynomial (Fin n) A` with finitely generated kernel.
   I read `def-sbc-locally-finite-presentation` and its recorded scheme predicate
   `LocallyOfFinitePresentation`; the node explicitly defines ring finite
   presentation inside that predicate. `LocallyOfFinitePresentation.SpecMap_iff`
   and `RingHom.finitePresentation_algebraMap` identify the affine case with
   this class. No substitute scheme definition or dependency module is needed.
5. Induced k-algebra structure on B: `[Algebra k B] [IsScalarTower k A B]`.
   Exact bookkeeping, not extra mathematical structure: I read
   `IsScalarTower.algebraMap_eq`, which says the map k -> B is the composite
   k -> A -> B. Conversely the composite always supplies this algebra and
   tower; unrelated k-algebra structures are correctly excluded.
6. Prime q of B: `(q : Ideal B) [q.IsPrime]`. Exact, with no maximality assumption.
7. B_K: `B ⊗[k] K`, Mathlib's existing algebra tensor product. Exact.
8. Prime q_K of B_K: `(qK : Ideal (B ⊗[k] K)) [qK.IsPrime]`. Exact.
9. Contraction q_K to B equals q: `h : q = qK.comap
   (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[k] K)`.
   Exact: I opened `includeLeftRingHom`, which sends b to b tensor 1.
   All data precede this equality in the quantifier order.
10. Canonical local map B_q -> (B_K)_(q_K):
    `Localization.localRingHom q qK Algebra.TensorProduct.includeLeftRingHom h`.
    Exact: I read its signature and localization construction, as well as
    `localRingHom_to_map` and `isLocalHom_localRingHom`. Its endpoints are
    `Localization.AtPrime q` and `Localization.AtPrime qK`, the localization
    notion recorded by `def-weil-pbc-localization-at-prime`. Localness is an
    existing instance for this exact map, so no extra localness binder is needed.
11. Faithfully flat: `.FaithfullyFlat` on that map. Exact: I read
    `RingHom.FaithfullyFlat`, which gives the target its module structure via
    precisely that map, and `Module.FaithfullyFlat` and its exactness
    equivalences in `Flat/FaithfullyFlat/Basic.lean`. These are the recorded
    notions of `def-weil-pbc-faithfully-flat-ring-map`.

Edge cases: zero A or B, and the empty affine scheme, admit no specified prime
q, so the statement is vacuous without an added nonzero assumption. There is
no index set in this statement. Presentations with zero variables or zero
relations are included. K=k and B=A are included. Infinite, transcendental,
inseparable field extensions and all characteristics are included. The four
universes u, v, w, x are independently declared, including different-size
fields and algebras; tensor products and localizations use their natural
universes. No universe or variable is unbound; `autoImplicit` is disabled.

Independent searches (different phrasing from the first worker):

- `msearch.py leanfinder`: `stalk map after extending the ground field is
  faithfully flat` returned eight hits. They include `Flat.stalkMap`,
  `flat_and_surjective_SpecMap_iff`, and the general
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`; none states this combined
  tensor-extension localization lemma.
- `msearch.py loogle`: `Localization.localRingHom, RingHom.FaithfullyFlat`
  returned zero hits.
- `msearch.py grep`: `localRingHom.*FaithfullyFlat|FaithfullyFlat.*includeLeft|
  stalk.*faithfully` returned zero hits.
- `msearch.py leansearch`: `A field extension induces faithfully flat
  homomorphisms on localizations at corresponding prime ideals` was unavailable
  (Internal Server Error); this outage supplies no mathematical verdict.
- I independently searched all Mathlib, all `WeilConjectures`, and `lean/Sheaf`
  with `rg` for faithful flatness together with `localRingHom`, `includeLeft`,
  or `stalk`, in both orders, and for the exact name and blueprint id in the
  source and `dag/lean_names_upstream.json`. No existing combined statement
  was found. I opened the source hits in `Mathlib/AlgebraicGeometry/Morphisms/Flat`
  and `AlgebraicGeometry/Modules/FlatPullbackStalk`: these apply the general
  flat-local theorem inside descent proofs, rather than declaring this result.

H5/H6/H8/H9: there are no definitions and only one theorem, with `sorry` as its
entire proof. Its docstring names the source and blueprint id and gives all
three DAG proof steps with their dependency ids. The imports provide exactly
the faithful-flatness/localization, finite-presentation, and tensor-inclusion
APIs used. Names and topic placement follow the project conventions; all Lean
lines fit 100 characters. The node's `lean.statement` is verbatim the signature.
There are no new nodes, dependency modules, or statement corrections to audit.

Validation: independent server single-file compilation succeeded in 1.7 seconds,
with no errors or warnings. Delivery dry-run and final push are performed after
this report is appended.
