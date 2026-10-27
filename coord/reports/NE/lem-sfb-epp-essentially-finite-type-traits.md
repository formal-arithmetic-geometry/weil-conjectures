## Worker report

The module `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits` states
`IsDiscreteValuationRing.exists_epp_essentially_finite_type_traits` with a single
`sorry` proof. Four accompanying helpers construct the actual reduced tensor,
upper integral closure and canonical normalization map, and express the final
residue-field tensor clause. All helper data are fully defined using Mathlib;
there are no auxiliary postponed theorems, axioms, or arbitrary map choices.
Only the item's `lean` field changes. No correction, new node, or dependency
repair is needed.

Clause-by-clause rendering:

- D is a commutative integral domain and DVR: `(D : Type u) [CommRing D]
  [IsDomain D] [IsDiscreteValuationRing D]`. Completeness is precisely
  `[IsAdicComplete (IsLocalRing.maximalIdeal D) D]`; no completeness of T
  is required.
- Its fraction field is `(F : Type v) [Field F] [Algebra D F]
  [IsFractionRing D F]`.
- T is a DVR with fraction field H: the parallel `CommRing`, `IsDomain`,
  `IsDiscreteValuationRing`, `Field`, `Algebra T H` and `IsFractionRing T H`
  binders. These rings are nonzero and not fields by the DVR definition.
- The injective local map D to T is `algebraMap D T`, with
  `[IsLocalHom (algebraMap D T)]` and `hinj`. Mathlib's local-hom condition
  is equivalent to inverse image of the maximal ideal being the maximal ideal.
- The induced fraction-field embedding is `[Algebra F H]`; the two
  `IsScalarTower D T H` and `IsScalarTower D F H` binders identify its
  restriction to D with the given ring map. They specify the diagram,
  rather than imposing an additional mathematical restriction.
- Essential finite type is exactly `hfinite`: a commutative D-algebra A,
  prime p, `RingHom.FiniteType (algebraMap D A)`, and
  `Nonempty (T ≃ₐ[D] Localization.AtPrime p)`. It does not assume finite
  type of T itself. A can live in `Type (max u w)`: finite generators of
  A over D bound its cardinality by that of D and a countable set, so this
  excludes no presentation. The binders include zero generators and all primes.
- The finite field extension F1/F is an existential field and algebra
  structure together with `Module.Finite F F₁`. Its universe is large
  enough for every finite extension of F; there is no separability condition.
- Every further finite M/F1 is expressed by universal `M`, `Field M`,
  `Algebra F₁ M` and `Module.Finite F₁ M` binders. `Algebra F M` and the
  scalar tower specify the composite F-algebra; the D-algebra and its tower
  similarly specify restriction from F. Each exists canonically, so these
  binders exclude no field extension. M has universe `max u v w x y`,
  allowing arbitrary further ambient universe y.
- R_M is exactly Mathlib `integralClosure D M`.
- The generic algebra is `eppReducedTensor F H M`, defined as
  `(H ⊗[F] M) ⧸ nilradical (H ⊗[F] M)`. Thus all nilpotents, not a chosen
  ideal or just tensor generators, are killed.
- B_M is `eppUpperClosure T F H M`, exactly `integralClosure T` in that
  reduced tensor, using T to H to the left tensor factor. Integrality over
  T is integrality over its image, so this is the node's normalization.
- `eppNormalizationMap D T F H M` is the actual map R_M to B_M:
  include M by `Algebra.TensorProduct.includeRight`, quotient by the
  nilradical, restrict scalars to D, and restrict domain and codomain to
  the integral closures. The membership proof uses Mathlib `IsIntegral.map`
  and `IsIntegral.tower_top`. These are existing proofs used to construct a
  ring homomorphism, not newly proved stage-2 theorems.
- Every maximal q of B_M is quantified with `[q.IsMaximal]`.
  Its contraction n is `q.comap (eppNormalizationMap D T F H M)`.
  The first conjunct states exactly that n is maximal.
- The second conjunct supplies `IsDomain (Localization.AtPrime q)` and,
  using that domain proof, `IsDiscreteValuationRing` for the same local ring.
  The domain proof must be explicit because a prime localization of an
  arbitrary ring is not automatically a domain.
- The third conjunct maps n along R_M to B_M to `(B_M)_q` and equates it
  with `Ideal.map (algebraMap B_M (Localization.AtPrime q)) q`.
  This is exactly n(B_M)_q = q(B_M)_q, not merely an equality of radicals.
- The fourth conjunct is `eppResidueBaseChangeReduced` on that canonical map,
  contraction, and q. It installs precisely
  `(Ideal.ResidueField.map n q f rfl).toAlgebra`, and requires
  `IsReduced (q.ResidueField ⊗[n.ResidueField] Ω)` for every field Omega
  with an `Algebra n.ResidueField Ω` structure. Because the first conjunct
  makes n maximal, n.ResidueField is canonically R_M/n (its fraction field,
  and R_M/n is already a field). The use of this canonically isomorphic
  field avoids a proof-dependent maximality instance in later conjuncts.
  Mathlib defines q.ResidueField literally as the residue field of
  `Localization.AtPrime q`, whose maximal ideal is q(B_M)_q. Thus it is
  the node's upper quotient. Mathlib's residue-field map is induced by the
  localized canonical map, so the coefficient action is specified, not arbitrary.
- Omega lives in `Type (max u v w x y z)` after universe instantiation of
  the helper. Hence it can be as large as the residues and can be enlarged
  arbitrarily with z. No test-field quantification is vacuous by size.
- `IsReduced` means every nilpotent is zero. No characteristic, perfectness,
  algebraicity of H/F, or separability hypothesis has been inserted.

Dependencies read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (full class read).
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic` (Hausdorff and precomplete).
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  `Mathlib.RingTheory.FiniteType` (the recorded ring-hom interface).
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; `Ideal.ResidueField`
  and its canonical `map`, `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (carrier IsIntegral).
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with Mathlib's tensor ring
  and ideal quotient structures.

Public imports provide these interfaces and the fraction-ring, tensor quotient,
residue-field, and finiteness APIs needed by the statement. Plain proof imports
include every currently recorded project proof-dependency module:
`WeilConjectures.FieldTheory.SeparableExtension`,
`SeparablyGeneratedSeparable`, `CommonExtensionFields`, and
`SeparablyGeneratedTensorReduced`. Mathlib proof leaves are provided by
`Mathlib.FieldTheory.SeparablyGenerated`, `Mathlib.FieldTheory.Perfect`,
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`, and
`Mathlib.RingTheory.Localization.Integral` (integral transitivity is already
in the imported integral-closure API). The still unstated proof nodes
`lem-sfb-dvr-algebraic-normalization-structure`,
`lem-sfb-epp-weak-perfect-residue`,
`lem-sfb-dvr-perfect-residue-algebraic-tower`,
`lem-sfb-dvr-index-one-separable-base-change`, and
`lem-sfb-dvr-normalized-finite-stage-descent` have no module to import.
Their complete proof route is retained in the theorem docstring.

Source and edge checks:

Read Stacks more-algebra.tex at `proposition-epp-essentially-finite-type`
(09II), `lemma-solution-goes-up` (0GLR), `remark-construction` (09EM),
`definition-solution`, and `lemma-extension-dvrs-formally-smooth` (09E7).
The latest blueprint direct-image unit was also read: this is a historical
supporting algebra input, not the unit statement. No unit or node correction
is needed. Checked equal-characteristic zero and positive characteristic,
imperfect residue fields, purely inseparable F1/F and M/F1, identity further
extension M=F1, T=D, transcendental H/F and residue extensions, splitting into
multiple generic factors, all maximal branches, and zero-generator finite-type
presentations. Reduction is essential for inseparable tensor products; no
`IsDomain` hypothesis on the unreduced tensor or on B_M is imposed.
The max-universe choices allow identity extensions and test fields containing
the whole residue field. The DVR hypothesis excludes field traits and zero
rings exactly as the node's definition does.

Searches on 2026-10-24 (msearch.py, group NE and this item):

- LeanFinder: "Epp solutions for essentially finite type traits stable under
  further finite field extension with geometrically reduced residue fields".
  Eight hits: residue-field EssFiniteType, geometrically reduced algebras,
  formally unramified field facts, and unrelated smooth descent. None gives
  existence of Epp solutions or their persistence after arbitrary finite extensions.
- Loogle: `IsDiscreteValuationRing, FiniteDimensional`. No hits.
- LeanSearch: "Epp elimination ramification essentially finite type discrete
  valuation rings". Eight hits, all DVR definitions, criteria or consequences;
  none states Epp's theorem.
- Mathlib grep: `Epp|epp|integralClosure.*map|map.*integralClosure` in
  RingTheory. Twenty-five hits, integral-closure maps and unrelated occurrences;
  no Epp theorem. Read `AlgHom.mapIntegralClosure` and `IsIntegral.tower_top`;
  the latter handles the change from D-integrality to T-integrality.
- Project/upstream rg: Epp/epp, essentially finite type, reducedTensor and
  normalization patterns under `lean/WeilConjectures` and `lean/Sheaf`.
  Found only the Epp-consuming CommonFiniteTraitExtension and
  RaynaudFaltingsNormalizedReduction modules and separate tame DVR results;
  none defines this theorem or these reduced-tensor normalization helpers.
  A direct search for the item id in `lean/WeilConjectures` found no declaration.
  Searches for each newly introduced name in Mathlib, both project roots and
  the upstream name index found no clash.

Validation: scompile.py compiled the helper module, then the complete statement,
in both sandbox and library modes without errors or non-sorry warnings. The
final delivery dry run performs the remaining preflight and per-file compile.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
