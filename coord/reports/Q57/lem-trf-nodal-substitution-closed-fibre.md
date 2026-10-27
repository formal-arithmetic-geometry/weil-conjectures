## Worker report

Item: lem-trf-nodal-substitution-closed-fibre. Group: Q57. Date: 2026-10-24 UTC.
Module: Sheaf.RingTheory.NodalSubstitutionClosedFibre.
Main declaration: MvPowerSeries.NodalSubstitution.closed_fibre.

The module states the item, with `sorry` as its only theorem proof. Four concrete,
public abbreviations name objects introduced in the item's own statement:
`relationIdeal A h` is `Ideal.span {X 0 * X 1 - C h}`;
`Model A h` is the actual quotient of `MvPowerSeries (Fin 2) A` by that ideal;
`ambientIdeal A` is the extension of the maximal ideal of A plus the variables ideal;
`modelIdeal A h` is its image under the quotient map. These are helpers of this node,
not independent new notions. They have real Mathlib constructions and no postponed
proofs or chosen data. All five declarations are listed in `lean.declarations`.

Source checked: literature/stacks-project/curves.tex,
lemma-formal-local-structure-nodal-family, Tag 0CBX (the local tag index confirms
the label). Read the whole lemma and proof, especially the completed substitution
map in the final paragraph. The node isolates the algebra behind that paragraph;
it does not claim that the map is an isomorphism before reduction, and does not
assume the flatness used later in the source. No statement correction or dispute.

Hypotheses, individually:

- A and B: independent `Type u` and `Type v`, with `CommRing`, `IsLocalRing`,
  `IsNoetherianRing`, and `IsAdicComplete (IsLocalRing.maximalIdeal ...) ...` for each.
- The map alpha: `[Algebra A B]` supplies exactly `algebraMap A B`. Every original
  ring map alpha is covered by its `alpha.toAlgebra`; no injectivity or flatness
  is required. `[IsLocalHom (algebraMap A B)]` expresses alpha(m) contained in n,
  by Mathlib's `IsLocalRing.local_hom_TFAE` for these local rings.
- k: used literally as `A ⧸ IsLocalRing.maximalIdeal A`; B/mB is likewise the
  quotient by `(IsLocalRing.maximalIdeal A).map (algebraMap A B)`.
- The chosen k-algebra isomorphism: `θ` is a ring equivalence with the exact
  k[[x,y]]/(xy) source and B/mB target. `hθ` requires its compatibility with
  constants for every representative `a : A`. Since A -> k is surjective, this
  is exactly k-linearity for the canonical k-algebra structure on B/mB induced
  by alpha. It neither assumes a noncanonical k-action nor drops k-linearity.
- `h : A` and `hh` express h in m.
- `u v : B`, `hu`, `hv` express u,v in n.
- `huv` is precisely u*v = alpha(h).
- `hvars`, for both indices of `Fin 2`, says that reduction of u and v agrees
  with θ of the corresponding variable class. The vector `![u, v]` fixes the
  order x=0, y=1.

Conclusions, individually:

- The first four conjuncts assert that R is Noetherian, local, has maximal
  ideal `ambientIdeal A`, and is complete for that ideal.
- The next conjunct gives Noetherianity of C=`Model A h`. The existential
  `localC : IsLocalRing (Model A h)` supplies locality as a conclusion, not an
  added assumption. The explicitly instantiated `@IsLocalRing.maximalIdeal`
  identifies that maximal ideal with `modelIdeal A h`. The next conjunct
  asserts completeness for that image ideal. There are no hidden let binders.
- `φ : Model A h →ₐ[A] B` is an A-algebra homomorphism and `IsLocalHom φ`
  asserts locality. Its two variable equations give x->u and y->v.
- For every power series F and every natural N, the quotient equality modulo
  `IsLocalRing.maximalIdeal B ^ N` is the required substitution formula.
  `F.truncTotal N` retains exactly the monomials i+j<N;
  `MvPolynomial.eval₂ (algebraMap A B) ![u,v]` sums their substituted values.
- `ρ` is a ring equivalence from C/mC to k[[x,y]]/(xy). Its equation on every
  `F : MvPowerSeries (Fin 2) A` says explicitly that double quotienting followed
  by rho is coefficient reduction followed by quotienting by xy. This is the
  canonical coefficient-induced map and includes preservation of all constants
  and both variables by taking F to be C(a), X(0), or X(1).
- `φbar` is a ring homomorphism between the two specified closed fibres. Its
  equation for every c in C is precisely the commuting quotient diagram that
  defines the induced homomorphism. The equality
  `φbar = θ.toRingHom.comp ρ.toRingHom` is the required compatibility, and
  `Function.Bijective φbar` expresses that this induced map is an isomorphism.
- `(modelIdeal A h).map φ` is a_C B. The next ideal equality gives
  n=mB+(u,v)B with `Ideal.span {u,v}`. Thus both displayed maximal-ideal
  equalities of the node are present.
- `eC` identifies C/a_C with k, and `eB` identifies B/n with k. Since a_C
  was identified with the actual maximal ideal, these are exactly the two
  residue fields. Their equations on every a in A require both identifications
  to respect the given maps from A.

Dependency declarations read and used:

- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  `IsNoetherianRing`, with the all-ideals-finitely-generated equivalence.
- def-weil-pbc-adically-complete-ring: Mathlib.RingTheory.AdicCompletion.Basic,
  `IsAdicComplete`, including separatedness and precompleteness.
- def-weil-pbc-multivariate-power-series: Mathlib.RingTheory.MvPowerSeries.Basic,
  `MvPowerSeries`, with two variables `Fin 2`, its constant map C and variables X.

All three statement-dependency modules are public imports. Proof dependencies are
plain imports (all recorded signatures and proof docstrings were read):

- Mathlib.RingTheory.MvPowerSeries.Equiv, `MvPowerSeries.isNoetherianRing`.
- Mathlib.RingTheory.MvPowerSeries.Inverse, `MvPowerSeries.isUnit_iff_constantCoeff`
  and its local-ring instance (also a public import because the signature names
  the ambient maximal ideal).
- WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase,
  `power_series_complete_over_complete_base`.
- WeilConjectures.RingTheory.CompleteLocalQuotient, `quotient_complete_local`.
- WeilConjectures.RingTheory.PowerSeriesAdicEvaluation,
  `MvPowerSeries.exists_unique_adic_evaluation`.
- WeilConjectures.RingTheory.MvPowerSeriesQuotientKernel,
  `MvPowerSeries.ker_map_quotient_of_fg`.
- WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete,
  `MvPowerSeries.exists_ringHom_of_isAdicComplete`.
- The mathlib_match for quotient-local-structure comprises
  `Ideal.Quotient.nontrivial_iff`, `IsLocalRing.of_surjective'`,
  `IsLocalRing.map_maximalIdeal_of_surjective`, and `IsLocalHom.of_surjective`;
  their recorded Mathlib source signatures were read. The quotient and local
  ring modules supplying them are public imports, also used by the signature.

Edge cases checked before writing: A=k and h=0 (the map specializes to the
chosen theta), the model xy=t over k[[t]], a nonreduced complete base with h=0,
noninjective alpha, arbitrary chosen scalar-preserving theta, and arbitrary
characteristic. No regularity of h, flatness of B over A, equal universes, or
coefficient field in A/B is imposed. N=0 in the formula is harmless: the
quotient by n^0 is the zero ring, so the equality is automatic; all positive
N remain included. The zero ring is excluded exactly by the source's local
ring hypothesis, represented by Mathlib's nontrivial local-ring class.
No u/v nonvanishing hypothesis was added. The item has exactly two variables,
so there is no empty variable-index case to restrict.

Searches for an existing statement (all via prescribed msearch.py, plus local
read-only rg):

- leanfinder: "Nodal substitution A[[x,y]]/(xy-h) into a complete local algebra
  and isomorphism of the closed fibre" -> eight hits, on univariate Weierstrass
  quotients and a polynomial Weierstrass-curve quotient; none is this result.
- loogle: "MvPowerSeries.map, Ideal.Quotient, IsLocalHom" -> zero hits; service
  reported unknown identifier Ideal.Quotient.
- leansearch: "nodal formal power series quotient substitution complete local
  ring" -> eight hits, including Weierstrass division and substitution results;
  none states the nodal closed-fibre compatibility.
- grep through msearch.py: "nodal|nodalSubstitution|nodal_substitution" in
  Mathlib/RingTheory -> zero hits.
- rg for nodal notions in lean/WeilConjectures and lean/Sheaf found other
  geometric nodal charts and a polynomial strictNodalRing, not this complete
  hypersurface statement. Existing occurrences of MvPowerSeries (Fin 2) in
  NodalCoefficientStraightening, NodalCompletedResidueDenominators,
  SplitNodeCompletionTransport, SeparableNodeQuadraticCompletion and the
  geometric nodal chart files were inspected for overlap. Their results are
  different, and their concrete quotient expressions are ordinary Mathlib
  quotients, as used here.
- rg for the exact item id in lean/WeilConjectures and lean/Sheaf -> no hits.
- rg for nodalSubstitution|NodalSubstitution|nodal_substitution in Mathlib,
  lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json -> no hits,
  confirming the new declaration names are unused.

Validation: scompile.py Q57 lem-trf-nodal-substitution-closed-fibre compiled
this module as both a sandbox module and its intended library module with
exit status zero and no errors or non-sorry warnings. Every universe and
variable is explicit; autoImplicit and relaxedAutoImplicit are disabled.
The theorem docstring includes all six proof steps and their dependency names.
Only this item's lean record changes; no new nodes or dependency repairs.

## Second reading by Q57

This is the worker's final clause audit, not a claim of an independent second
worker: the dispatcher brief forbids starting another agent and assigns the
independent reading to the maintainer. The node and final module were compared
again directly. The crucial checks were that theta's k-linearity remains in
hθ, that rho is tied to coefficient reduction on every F, and that phibar is
tied to phi on every c, before asserting its equality with theta composed
with rho. Both maximal-ideal equalities and both scalar-compatible residue
field identifications are included. Locality and completeness of C occur in
the conclusion, not among the hypotheses. The dependent locality witness is
used only to name the correct maximal ideal; no theorem uses let or show
binders. This audit found no mismatch requiring a statement change. The
maintainer's independent review remains to be performed after delivery.
