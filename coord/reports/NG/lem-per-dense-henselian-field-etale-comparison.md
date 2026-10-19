## Worker report

The module `Sheaf.FieldTheory.DenseHenselianEtaleComparison` states
`AlgebraicGeometry.Etale.denseHenselianField_etaleComparison`, with its proof `sorry`.
No definitions, additional assumptions, or auxiliary postponed theorems are introduced.
The item's JSON changes only in `lean`; its existing status and empty proof fields are preserved.
There was no repair note for this item.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber,
`literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`, Exposé XX,
section 4.4, printed pages 373--374. On page 374 the source explicitly treats a dense
embedding of henselian valued fields with chosen separable closures and a map between
them, and displays the restriction isomorphism of Galois groups, referring to forms of
Krasner's lemma in Bourbaki AC VI, §8, exercises 12 and 14(a). The preceding reduction
concerns canonical cohomology pullback with torsion abelian coefficients.
The module docstring supplies the argument from that comparison through field étale
topoi and derived global sections, including continuity and naturality.

Hypothesis and clause correspondence:

- Fields and their inclusion: `(K K' : Type u) [Field K] [Field K'] [Algebra K K']`.
  The inclusion is `algebraMap K K'`, automatically injective for fields.
- Two valuations: independent value groups `(Γ : Type a)` and `(Γ' : Type b)` with
  `LinearOrderedCommGroupWithZero`, and `[vK : Valued K Γ]`, `[vK' : Valued K' Γ']`.
  These are general Krull valuations, written multiplicatively by Mathlib. Additive
  inequalities `v(x-a) > γ` become multiplicative small-ball inequalities.
- Nontriviality of each valuation: `hK` and `hK'` assert an element `x ≠ 0` with
  valuation different from `1`, excluding precisely trivial field valuations.
- Henselian valuation rings: `[HenselianLocalRing vK.v.integer]` and the analogous
  binder for K'. `Valuation.integer` is the actual subring of elements with value
  at most one. It has the existing `ValuationRing` and fraction-field instances;
  henselianity is asserted of this ring, not of the underlying field as a ring.
- Induced topology and density: `h_dense : IsDenseInducing (algebraMap K K')`.
  The two topologies are those furnished by the respective `Valued` instances.
  `IsDenseInducing` combines `IsInducing` with `DenseRange`; density is equivalent
  to meeting every nonempty open ball. There is no common value-group assumption.
- Chosen compatible separable closures: fields `Ks : Type v` and `K's : Type w`,
  `[IsSepClosure K Ks]` and `[IsSepClosure K' K's]`, and the algebra structures and
  scalar towers `K → K' → K's` and `K → Ks → K's`. The common `Algebra K K's`
  expresses commutativity of the embedding square, without identifying universes.
- Restriction is a topological group isomorphism: the first conjunct gives
  `∃ e : Gal(K's / K') ≃ₜ* Gal(Ks / K), ...`. `Gal` is the existing algebra
  automorphism group, equipped with Mathlib's Krull topology. The equation
  `algebraMap Ks K's (e σ x) = σ (algebraMap Ks K's x)` characterizes e as
  restriction along the chosen embedding. Injectivity of that embedding makes
  this characterization unique; no arbitrary isomorphism or arbitrary map is used.
- Every torsion abelian étale sheaf: the second conjunct universally quantifies
  `G : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}`
  and assumes `G.IsTorsion`, the recorded local-section torsion predicate.
- Every nonnegative degree: `∀ q : ℕ`, explicitly including zero.
- Canonical cohomology comparison: `Function.Bijective (cohomologyMap
  (Spec.map (CommRingCat.ofHom (algebraMap K K'))) G q)`. This is an additive
  homomorphism between precisely the two groups in the node; bijectivity says it
  is an isomorphism. Its codomain is `Sheaf.H ((upperStar ...).obj G) q`.
  As the cohomology dependency record explains, `Sheaf.H` is the existing
  abelian-sheaf convention used by upstream comparison maps; the comparison to
  homology of derived global sections is the shared stage-3 bridge, not redefined here.
- Naturality in G: for every torsion H, every `φ : G ⟶ H`, and every cohomology
  class x, the last equation states that `cohomologyMap` commutes with
  `Sheaf.H.map φ q` and `Sheaf.H.map ((upperStar ...).map φ) q`.
- No completeness, discreteness, rank, or residue-characteristic restrictions
  appear anywhere in the signature.

Dependency declarations read and used:

- `def-trf-valuation-ring`: `ValuationRing` and `ValuationRing.TFAE`,
  `Mathlib.RingTheory.Valuation.ValuationRing`, lines 62--64 and 407--416.
  Its instances at lines 462 and 480 identify the valuation integer subring and
  its fraction field with the node's notion. The integer subring construction
  is `Valuation.integer` in `Mathlib.RingTheory.Valuation.Integers`, line 32.
- `def-weil-pbc-henselian-terminology`: import the recorded
  `WeilConjectures.Mathlib.RingTheory.Henselian`; the clause used is Mathlib's
  `HenselianLocalRing` (Mathlib.RingTheory.Henselian, line 108), not the stronger
  `IsStrictlyHenselianLocalRing`. Read the recorded upstream class and its docstring
  at lines 120--124 as well.
- `def-kun-separably-closed`: `IsSepClosure`,
  `Mathlib.FieldTheory.IsSepClosed`, lines 226--230; also read `IsSepClosed`,
  lines 60--67, and the induced `IsGalois` instance at lines 267--271.
- `def-weil-pbc-etale-sheaves`: the recorded module
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` and its reexported
  `CategoryTheory.Sheaf.IsTorsion`; read the group clone module and the full
  signature/docstring of `Sheaf.IsTorsion` in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, lines 65--77.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 470--480. These appear directly in
  the sheaf categories and in the pullback morphism.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, lines 227--241,
  and its adjunction at lines 249--253. The actual inverse-image functor appears
  in the naturality equation and in the type of the canonical comparison.
- `def-weil-pbc-etale-cohomology`: `AlgebraicGeometry.Etale.cohomology` and
  `rightDerivedGlobalSections`,
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, lines 224--236.
  This recorded module is imported, and its record explicitly permits the existing
  `Sheaf.H` convention for abelian sheaves, used by `Etale.cohomologyMap`.
- Canonical comparison and naturality: `Etale.cohomologyMap` and
  `Etale.cohomologyMap_map`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`,
  lines 174--211; both signatures and construction/docstrings were read.
- Topological groups use `Gal`, `krullTopology` from
  `Mathlib.FieldTheory.KrullTopology`, and `ContinuousMulEquiv` from
  `Mathlib.Topology.Algebra.ContinuousMonoidHom`. No new definition of an
  absolute Galois group or its topology is introduced.

Edge cases checked before and after writing: identity field inclusions are permitted;
purely inseparable dense field extensions are not excluded; q=0 is included;
zero and unbounded torsion sheaves are included; nontrivial valuations of arbitrary
rank and nondiscrete value groups are allowed; positive and zero residue
characteristic are allowed; either closure can inhabit its own universe.
The two base fields may always be placed in a common universe for their scheme
sites; this follows the existing `cohomologyMap` convention and adds no size bound
on the mathematical fields. No finiteness or uniform annihilator is imposed.

Searches executed with the prescribed msearch wrapper:

- LeanSearch: `Dense extensions of henselian valued fields induce isomorphisms of
  absolute Galois groups and etale cohomology`. Eight hits, including
  `Field.absoluteGaloisGroup`, `Valued.extension`, and `InfiniteGalois.profiniteGalGrp`;
  none states the dense henselian comparison.
- LeanFinder: `Dense extensions of henselian valued fields induce isomorphisms of
  absolute Galois groups`. Eight hits, including `galLiftEquiv`,
  `Field.absoluteGaloisGroup`, and `InfiniteGalois.mulEquivToLimit`.
  `galLiftEquiv` concerns integral closures, not this field extension comparison.
- Loogle: `galRestrict, IsDenseInducing`: zero hits.
- Mathlib grep: `Krasner|henselian.*dense|dense.*henselian|galRestrict`: 25 hits,
  including normed-field Krasner results and integral-closure restriction APIs.
  These do not state the node for general valued fields.
- Direct rg searches in both `WeilConjectures` and `lean/Sheaf`, by
  `dense.*[Hh]enselian|[Hh]enselian.*dense|lem-per-dense-henselian-field-etale-comparison`,
  found only the consumer HenselianCompletionOpenRigidity and unrelated condensed
  rigidity material, no existing comparison theorem. The same source-name search
  included `dag/lean_names_upstream.json` with no matching declaration.
- Additional direct API searches found the existing `Valued`, `Valuation.integer`,
  `IsDenseInducing`, `IsSepClosure`, Krull topology, restriction APIs, and canonical
  `cohomologyMap`; those are reused instead of supplying private copies.

Validation: the prescribed scompile.py compiled the sandbox and library forms
cleanly (2.7 s and 3.1 s), with no errors or non-sorry warnings. All variables and
universes are explicit (`set_option autoImplicit false`), and all lines are at
most 100 characters. No statement correction or disputed claim was needed.

## Second reading by NG

This is the author's second reading; the maintainer provides the independent review.
Reopened the node and module together, then checked each binder and conjunct.
The potentially significant mistakes would have been henselianity of K itself
(which is automatic for any field), rank-one/normed hypotheses, a uniform torsion
exponent, or an unspecified Galois isomorphism. The delivered signature avoids
all four: it uses the actual two integer subrings, independent arbitrary ordered
value groups, the local torsion predicate, and the restriction compatibility
identity for every automorphism and every closure element.

Rechecked the displayed Galois arrow's direction (K' to K), the contravariant
spectrum map's direction (Spec K' to Spec K), and the covariant cohomology map's
direction (H over K to H over K'). Rechecked every q includes zero and the final
naturality square applies to every map between torsion sheaves. Closure towers
express exactly compatibility of the chosen embeddings. The closure universes
are independent. No mismatches were found, and no source/node changes were made.
