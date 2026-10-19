## Worker report

The module `Sheaf.RingTheory.FiniteAlgebraEtaleNearFieldOrDvr` states
`Algebra.exists_etale_away_of_finite_torsionFree_of_field_or_dvr` with `sorry`.
No definition or other theorem is introduced. The node changes only in `lean`.
No statement correction, new node, dependency repair, or statement dispute is needed.

Clause-by-clause correspondence:

- The commutative Noetherian integral domain is `(R : Type u) [CommRing R]
  [IsDomain R] [IsNoetherianRing R]`.
- The commutative finite R-algebra is `(B : Type v) [CommRing B] [Algebra R B]
  [Module.Finite R B]`. Its universe is independent of R's.
- Torsion-freeness is exactly `htorsion : ∀ (r : R) (b : B), r ≠ 0 →
  r • b = 0 → b = 0`. Algebra scalar multiplication is multiplication by the
  image of r; no injectivity or nontriviality of B is assumed.
- The prime is `(p : Ideal R) [p.IsPrime]`.
- `Localization.AtPrime p` is the specified local ring. `hbase` is the disjunction
  `IsField (Localization.AtPrime p) ∨ IsDiscreteValuationRing (Localization.AtPrime p)`.
  `IsField` expresses that this existing commutative ring is a field, without
  replacing its ring structure by an unrelated instance.
- `p.ResidueField` is κ(p). Mathlib gives its `IsFractionRing (R ⧸ p)` instance,
  so it is the source's fraction field of R/p, canonically.
- `p.Fiber B` is κ(p) ⊗[R] B, the recorded dependency's fibre convention. The
  source writes the factors in reverse order; the canonical tensor commutation
  identifies them as κ(p)-algebras. No different fibre construction is introduced.
- Alternative (i) is `Subsingleton (KaehlerDifferential p.ResidueField (p.Fiber B))`.
  A module is zero precisely when its underlying additive group is subsingleton.
- Alternative (ii) is an existential finite type I, field family L with κ(p)-algebra
  structures, an algebra equivalence `p.Fiber B ≃ₐ[p.ResidueField] Π i, L i`, and
  `∀ i, Module.Finite p.ResidueField (L i) ∧ Algebra.IsSeparable p.ResidueField (L i)`.
  `Algebra.IsSeparable` means each element is separable (its minimal polynomial
  has distinct roots). Finite generation over the field supplies the finite extension.
  I and the factors lie in `Type (max u v)`, the fibre's universe; finite factors
  can always be represented there. The index set is allowed to be empty.
- The two alternatives are joined by `∨`, not both required.
- The conclusion is `∃ f : R, f ∉ p ∧ ... .Etale` on
  `IsLocalization.Away.map (S := Localization.Away f)
    (Q := Localization.Away (algebraMap R B f)) (algebraMap R B) f`.
  This is the canonical R[1/f] → B[1/f], not an arbitrary homomorphism.
  Mathlib's `RingHom.Etale` is the ring-map version of the dependency's scheme
  etaleness (`HasRingHomProperty @AlgebraicGeometry.Etale RingHom.Etale`), explicitly
  accepted by the stage-2 ETale RING MAPS convention.

Dependency declarations, with signatures and docstrings read in the pinned source:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct` and `LinearMap.baseChange`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  `Mathlib.RingTheory.RingHom.Etale`: `RingHom.Etale`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.RingTheory.Localization.Away.Basic`: `IsLocalization.Away.map`.
- The field product uses `Algebra.IsSeparable` from Mathlib's field theory, also
  used by `Mathlib.RingTheory.Etale.Field`'s finite separable product criterion.

All recorded proof-dependency modules are imported non-publicly unless already
public for a statement dependency. In particular the existing interfaces
`Module.Flat.localizedModule_atPrime_of_flat` (Sheaf.RingTheory.FlatModuleAtPrime),
`AlgebraicGeometry.etale_SpecMap_algebraMap_tfae`
(WeilConjectures.AlgebraicGeometry.GroupScheme.Defs), and
`AlgebraicGeometry.Scheme.etale_fibre_iff_forall_etale_neighbourhood`
(Sheaf.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods) are imported.
The docstring gives the six-step node proof: localized torsion-free freeness,
spreading a finite basis, finite flat presentation, etale fibre criterion,
source etale opens, and closed-image/principal-open refinement.

Source reading: `literature/stacks-project/morphisms.tex`, lemma-etale-at-point
(Tag 02GU), lines 8318ff, and `algebra.tex`, lemma-etale-over-field (Tag 00U3),
lines 39394ff. The former gives the pointwise flat/fibre criterion; the latter
includes precisely finite products of finite separable extensions.

Edge cases checked mathematically against the Lean signature:

- B the zero algebra is allowed; the fibre is zero, its differential module is
  zero and it is the empty product. The empty source map is etale. No `[Nontrivial B]`.
- At p = (0), the local domain is its fraction field, so the field branch applies.
- At a DVR closed point, the DVR branch applies. No chosen uniformizer is required.
- B = R and finite products of R satisfy the hypotheses and are etale already.
- A ramified DVR extension has a non-etale residue algebra, so the fibre hypothesis
  excludes it. Purely inseparable field extensions have nonzero differentials and
  fail the separability alternative. R/(t) over a domain with t nonzero fails htorsion.
- No characteristic, positive-rank, nonempty-fibre, or common-ring-universe assumption.

Searches for an existing identical statement (all through the authorized wrapper
and source-only reads):

- LeanFinder: `finite torsion free algebra over Noetherian domain etale on base
  neighbourhood of prime with field or DVR local ring and separable fibre`.
  Eight hits, including `Algebra.IsEtaleAt`, `Algebra.etaleLocus`, and
  `Algebra.exists_etale_of_isEtaleAt`. The last localizes the source at an element
  of B from an assumed etale stalk; it does not give this base-neighbourhood result.
- Loogle: `Algebra.Etale, IsDiscreteValuationRing`: zero hits.
- Mathlib grep: `etale.*(torsion|DVR)|exists.*etale.*[Ff]inite` in RingTheory:
  four hits in TotallySplit and Unramified.LocalStructure; none is the statement.
- LeanSearch: `A finite torsion free algebra is etale on a base neighbourhood of a
  prime with field or DVR local ring and finite separable fibre`: eight hits,
  field criteria and etale-locus results, no identical theorem.
- `rg` in upstream WeilConjectures and shared lean/Sheaf for DVR/torsion-free
  etale results found only other notions/results. Searching the exact node id
  in upstream found nothing. Searching the selected full theorem name in
  Mathlib, upstream, shared lean/Sheaf, and dag/lean_names_upstream.json found
  no declaration. The existing finite-etale field criterion is used, not duplicated.

Validation: authorized `scompile.py NG lem-per-finite-algebra-etale-near-field-or-dvr`
compiled this delivered file as both sandbox and library module, 2.8s and 2.9s,
without errors or warnings. No global build or direct edits to either read-only
checkout were performed.

## Second reading by NG

This is the author's separate rereading; the dispatcher forbids starting other
agents and assigns the independent review to the maintainer. I reopened the node
and the completed module and checked each binder and conclusion as mapped above.
R is Noetherian and a domain; B is a finite commutative R-algebra with the exact
nonzero-scalar torsion-free condition; p is prime; the localization satisfies the
field-or-DVR alternative; the canonical residue-field fibre satisfies the exact
zero-differentials-or-finite-separable-product alternative; the witness f belongs
to R and avoids p; and the canonical map R_f → B_f is etale. Empty products and
zero B remain allowed. The two representational differences (tensor order and
residue field versus fraction field) are the canonical identifications supplied
by the dependency records, not mathematical changes. All universes and binders
are explicit, no `let` or file-local notation occurs, and the sole proof is `sorry`.
No mismatch was found on this rereading and no statement edits were needed.
