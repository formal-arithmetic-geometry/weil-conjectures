## Worker report

The module `Sheaf.AlgebraicGeometry.TameTraitQuotientLogEtale` states
`AlgebraicGeometry.tame_trait_quotient_log_etale`, with its sole proof `sorry`.
No data definition or extra theorem is introduced. The natural statement is unchanged.
The eleven DAG proof steps are copied into the theorem docstring, including the
explicit invariant-DVR, Kummer-presentation and composite-chart calculations.

Source read: ILO, Exposé XVI 3.7, printed pp.254–255 (PDF pp.260–261).
The paragraph explicitly identifies T=S′/H, states that S′→T is log étale for
canonical log structures, and transfers log smoothness of X′ from S′ to T.
The node's proof supplies the general invertible-order action and arbitrary V form.

Hypothesis and clause correspondence:

| Natural statement | Lean encoding |
| --- | --- |
| Traits S=Spec R and S′=Spec B | `R B : Type u`, commutative domains and `IsDiscreteValuationRing R/B`. A DVR is exactly the nonfield local PID form of the node's Noetherian one-dimensional local domain with principal maximal ideal; a field is excluded. |
| Complete | `IsAdicComplete (IsLocalRing.maximalIdeal R) R` and the same for B. This is completeness and separation at the stated maximal ideal, rather than an unrelated metric topology. |
| Strictly henselian | Upstream `IsStrictlyHenselianLocalRing R/B`, extending `HenselianLocalRing` with separably closed residue field. The upstream root-lifting equivalence is imported as a proof dependency. |
| Mixed characteristic | `CharZero R/B` and `hR/hB : ringChar (IsLocalRing.ResidueField R/B) ≠ 0`. Characteristic of a domain equals characteristic of its fraction field; nonzero characteristic of a field is positive. |
| Finite dominant extension S′→S | `Algebra R B`, `Module.Finite R B`, and injective `algebraMap R B` (`hdom`). For spectra of domains injectivity is exactly density of the generic image. |
| Finite H acts over S | `H : Type v`, `Group H`, `Finite H`, `MulSemiringAction H B`, and `SMulCommClass H R B`. The last makes the action fix R. A scheme action is contravariant on functions; replacing h by h⁻¹ identifies this with the usual left ring action and leaves the fixed ring unchanged. |
| #H invertible on S | `htame : IsUnit (Nat.card H : R)`; global units on the affine base are exactly units at all stalks. |
| T=Spec(B^H) | Every occurrence uses Mathlib's actual `FixedPoints.subalgebra R B H`, whose elements satisfy `∀ h, h • b = b`. Its underlying ring is the fixed subring; its R-algebra structure is the canonical factorization of R→B. No abstract quotient substitute is supplied. |
| T is a trait | The conclusion provides `hD : IsDiscreteValuationRing (FixedPoints.subalgebra R B H)`. Domainness comes from the fixed subalgebra's embedding into B. |
| T complete strictly henselian | The existential strict-henselian instance and the following `IsAdicComplete` conjunct refer to this same fixed ring and its own maximal ideal. |
| T→S finite dominant | `IsFinite` and `DenseRange` of `Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R B H)))`. |
| S′→T finite dominant | `IsFinite` and `DenseRange` of `Spec.map` of `(FixedPoints.subalgebra R B H).val.toRingHom`, the actual inclusion into B. |
| Generic-field degree divides #H | Existential fraction fields K of B^H and L of B, with the induced K-algebra structure and both scalar towers, `FiniteDimensional K L`, and `Module.finrank K L ∣ Nat.card H`. The two towers force the extension of the fixed-ring inclusion. The choice of fraction-field models changes neither the degree nor the map. No faithfulness assumption is made. |
| Canonical fs log structures | `MB`, `MA`, `fsB`, `fsA`, together with presheaf isomorphisms `eB`, `eA` to the existing `divisorialLogPresheaf` along the canonical fraction-field spectrum maps. The equations `e.hom ≫ divisorialStructuralMap ... = M.alpha` pin the structures to the divisorial inclusions. This is precisely O∩j_*Oηˣ on every étale test object, with all restrictions. The isomorphisms imply the sheaf condition for the prescribed presheaves. These are characterized structures, not choices from an unconstrained nonempty proposition. |
| S′→T log étale | The log morphism q has `q.base` equal to the actual fixed-ring quotient map and satisfies existing `q.IsLogEtale`. Its source and target are the displayed fs log schemes with MB and MA. Compatibility with the structurally embedded divisorial sheaves determines its section maps; no unrelated log lift is allowed. |
| Every locally Noetherian fs V log smooth over S′ | `∀ (V : FineSaturatedLogScheme.{u}) (f : EtaleLogHom V ...), f.IsLogSmooth → ...`. This existing bundled fs-scheme interface contains the locally Noetherian hypothesis. There is no extra integrality, regularity, nonemptiness, or finite-type hypothesis. |
| The composite V→T is log smooth | `∃ g, f.CompEq q g ∧ g.IsLogSmooth`. Existing `CompEq` specifies the actual composite, including the base map and all relative étale-test section maps, so this is the composite assertion even though the interface has no composition constructor. |

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtalePrelogStructure`,
  `EtaleLogStructure`, `FineSaturatedLogScheme`, `EtaleLogHom`, `EtaleLogHom.CompEq`.
  Read the full structures and chart/log predicates. Imported through FSLogSmoothEtale.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `FSLogChart`, `FSLogChart.comparison`,
  `FSLogChart.IsEtaleChart`, `EtaleLogHom.IsLogSmooth`, `EtaleLogHom.IsLogEtale`.
  Read the complete module, including the chart group conditions and cover quantifiers.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  whose affine-local module-finiteness signature is the recorded dependency.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, with the full signatures
  read from the source; imported transitively through the log and finite interfaces.
- `Mathlib.Algebra.Algebra.Subalgebra.Operations`: `FixedPoints.subalgebra` and
  `FixedPoints.subring`; full definitions read before using the former.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`,
  its superclass and separably closed residue-field instance.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`: `divisorialLogPresheaf` and
  `divisorialStructuralMap`, using the actual relative-étale test-object definition.

All recorded proof dependencies with modules are imported non-publicly, including
`Algebra.finite_over_complete_local_product`,
`HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi`,
`NumberTheory.dvr_galois_degree_data`,
`IsDiscreteValuationRing.finite_normalization_tame_inertia`,
`IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`,
`AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra`, and
`AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale`.
The proof-only node `lem-per-trait-log-smooth-uniformizer-chart` has neither a Lean
record nor a Mathlib match at the inspected base; there is no module to import.
It is not used to define any object in this statement and is retained in the
natural-language proof plan. No unstated prerequisite is assumed in the Lean signature.

Edge cases checked before drafting:

- H trivial: its fixed algebra is B, degree is 1 and the quotient map is the identity.
- Nonfaithful H, including a completely trivial action of a larger finite group:
  no `FaithfulSMul` occurs; degree 1 still divides #H.
- Nontrivial tame cyclic Kummer extension: the N→N multiplication-by-e chart has
  finite invertible cokernel and étale comparison; the statement allows e>1.
- Imperfect separably closed residue fields: `IsSepClosed`, never `IsAlgClosed`,
  is required for traits; none of the conclusion silently assumes perfection.
- Empty V: the universal assertion admits empty fs schemes; the existing log-smooth
  cover criterion is pointwise and hence allows the empty source.
- Fields and equal-characteristic traits are excluded exactly by the natural
  hypotheses; residue characteristic is nonzero and the traits are nonfield DVRs.
- All universes and variables are explicitly bound (`autoImplicit false`). The two
  coordinate rings share the scheme universe; the acting finite group has its own
  unrestricted universe v. Fraction fields can be represented in the ring universe.

Searches made (all service searches via the prescribed msearch wrapper):

- LeanFinder: `finite tame group quotient of complete strictly henselian traits is log etale`.
  Eight ordinary étale and algebra results; no logarithmic quotient theorem.
- Loogle: `FixedPoints, MulSemiringAction, IsDiscreteValuationRing`.
  Zero hits; the service reported unknown identifier FixedPoints.
- Mathlib grep: `fixedSubring|fixedSubalgebra|invariantSubring|invariantSubalgebra|LogEtale|LogSmooth`.
  Eleven action/invariance-component hits, no log-étale or log-smooth statement.
- LeanSearch: `tame quotient of strictly henselian discrete valuation ring log etale canonical log structure`.
  Eight local-ring and ordinary étale-component hits, no full statement.
- Direct rg in Mathlib found the existing exact fixed-subalgebra construction in
  Algebra/Algebra/Subalgebra/Operations.lean; its full definition was read and reused.
- Direct rg in the upstream WeilConjectures and project lean/Sheaf trees for the item
  id and tame-trait quotient names found no declaration of this theorem. Searches
  for canonical trait log structures and complete-trait declarations found only
  general divisorial and log-scheme components, all reused rather than restated.
- DAG trait search and `tools/blueprint_refs.py search trait` found existing trait
  consumers and log-scheme definitions, not a separate canonical-trait construction
  needing a replacement. No new nodes or dependency repairs are needed.

Validation: scompile.py compiled the sandbox and library-name versions cleanly in
3.7 seconds and 3.3 seconds. No error or warning was printed. The node signature is
extracted verbatim from the theorem and the date is UTC. No statement dispute,
correction, new node or hollow data is present.

## Second reading by Q111

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
