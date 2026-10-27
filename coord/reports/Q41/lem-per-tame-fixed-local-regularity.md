## Worker report

The module `Sheaf.RingTheory.TameFixedLocalRegularity` states
`IsLocalRing.tame_fixed_local_regularity` with one `sorry`. It defines three helpers
belonging to this node: the specified fixed ideal, the specified cotangent difference
span, and the actual quotient cotangent module with its canonical residue-field scalars.
No additional DAG notion or dependency repair is needed. The node's mathematical
statement, statement dependencies, proof and proof dependencies are unchanged.

Source read: Travaux de Gabber VI Proposition 4.2, printed pp.76--77 (PDF pp.82--83),
including its equal- and mixed-characteristic arguments; VIII Lemma 4.2.3, printed
p.119 (PDF p.125), including the natural cotangent surjection and fixed tangent space.
The current blueprint's `lem-per-artin-gabber-affine-curve` statement and proof were
also read to check the recorded ancestor. The docstring follows this node's accepted
five-step direct averaging proof rather than introducing completion or Cohen data.

Hypotheses and conclusions, clause by clause:

* A commutative regular local ring is `(R : Type u) [CommRing R]
  [IsRegularLocalRing R]`. Mathlib's class includes both locality and Noetherianity.
  Its maximal ideal, residue field and cotangent space are `maximalIdeal R`,
  `ResidueField R` and `CotangentSpace R`.
* A finite group is `(H : Type v) [Group H] [Finite H]`. The independent universe
  `v` imposes no size restriction relative to `R`.
* Its action by local ring automorphisms is `σ : H →* (R ≃+* R)`.
  Every ring automorphism of a local ring preserves units and nonunits, hence its
  maximal ideal; locality needs no additional hypothesis. The subtype membership
  term in `fixedActionCotangentRelations` uses `MulEquiv.isUnit_map` directly.
* Identity on the residue field is the exact representative equation `hres :
  ∀ h a, residue R (σ h a) = residue R a`; residue surjectivity makes this equivalent
  to identity of the induced residue automorphism.
* Invertibility of the group order is precisely
  `htame : IsUnit (Nat.card H : ResidueField R)`; it is not invertibility of a
  different characteristic or the choice of an inverse in a coefficient field.
* `fixedActionIdeal R H σ` is `Ideal.span (Set.range fun ha : H × R ↦
  σ ha.1 ha.2 - ha.2)`, including differences for every element of `R` as stated.
  Its containment in `maximalIdeal R` is the first conclusion.
* `fixedActionCotangentRelations R H σ` is the residue-field span of
  `toCotangent (σ h x) - toCotangent x` for all maximal-ideal representatives `x`.
  Mathlib's `Ideal.toCotangent_surjective` shows these are exactly all
  `h(v)-v` for `v` in the cotangent space. Thus this expression is `D_H`, using
  the induced action on representatives; it does not assume a representation
  chosen independently of the original action.
* `IsRegularLocalRing (R ⧸ fixedActionIdeal R H σ)` renders the entire regular
  local quotient conclusion, including nontriviality and Noetherianity.
* The target of the canonical surjection is `fixedActionQuotientCotangent R H σ`.
  Its underlying additive group is literally Mathlib's `J.Cotangent`, where
  `J = (maximalIdeal R).map (Ideal.Quotient.mk I_H)`. Since `I_H ≤ m`, this is
  `(m/I_H)/(m/I_H)^2`. No arbitrary target vector space replaces it.
* The target's `k`-module structure is `Module.compHom` along
  `Ideal.quotientMap J (Ideal.Quotient.mk I_H) Ideal.le_comap_map`.
  This is the canonical map `R/m → (R/I_H)/J`, an isomorphism when `I_H ≤ m`.
  This gives the precise common-residue-field scalar structure without an
  unnecessary coefficient-field hypothesis or a second local-ring instance.
* The existential `f` is a `ResidueField R`-linear map to that target, with its
  value specified on **every** `x : maximalIdeal R` as the quotient cotangent
  class of `Ideal.Quotient.mk I_H x`. These equations uniquely determine `f`
  by surjectivity of `toCotangent`; thus no arbitrary map is substituted for
  the canonical surjection. `Function.Surjective f` states surjectivity explicitly.
* `LinearMap.ker f = fixedActionCotangentRelations R H σ` is the exact kernel
  equality over `k`.
* The last existential is an actual `k`-linear equivalence from
  `CotangentSpace R ⧸ fixedActionCotangentRelations R H σ` to the actual quotient
  cotangent module. Its normalization `∀ v, e (Submodule.Quotient.mk v) = f v`
  specifies the induced canonical isomorphism uniquely. Neither a bare abstract
  isomorphism nor equality of dimensions replaces this clause.
* No field in `R`, completeness, smoothness, generic freeness, faithful action,
  positive dimension, nontrivial action, or nontrivial group is required.

Dependency declarations read and used:

* `def-weil-regular-scheme` records `AlgebraicGeometry.IsRegularScheme` in
  `Sheaf.AlgebraicGeometry.IsRegularScheme` for its scheme clause, and its retained
  `mathlib_match` gives `IsRegularLocalRing` and `IsRegularRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs` for its ring clauses. The complete
  scheme definition and Mathlib regular-local class were read. This item uses
  the ring clause, so it imports and uses the exact Mathlib match directly.
* `lem-weil-pbc-regular-local-cotangent-dimension`: its Mathlib match is
  `IsRegularLocalRing.iff_finrank_cotangentSpace`,
  `ringKrullDim_le_spanFinrank_maximalIdeal`, and
  `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`.
  Their full signatures were read in RegularLocalRing/Defs, Ideal/KrullsHeightTheorem
  and Algebra/Module/SpanRankOperations. RegularLocalRing.Defs imports them.
* `lem-weil-pbc-nakayama-local-generators`: `IsLocalRing.map_mkQ_eq_top`,
  `Mathlib.RingTheory.LocalRing.Module`, read with its finite-module assumption.
  This module is a plain proof import.
* `lem-weil-pbc-regular-local-generators-regular-sequence`:
  `IsRegularLocalRing.isRegular_and_quotients_of_generators`,
  `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`, read with
  its parameter-list hypothesis and all initial quotient clauses. This module
  is a plain proof import. The four proof dependencies remain unchanged.
* The statement uses Mathlib's `Ideal.Cotangent`, `Ideal.toCotangent`,
  `IsLocalRing.CotangentSpace`, `Ideal.quotientMap`, `Submodule.span`,
  `Submodule.Quotient`, and `ModuleCat`. All helper definitions contain real
  constructions, no postponed proof or data choice.

Edge cases checked mathematically before writing: the trivial group and any trivial
action give `I_H=0`, `D_H=0` and the identity cotangent isomorphism. If `R` is a
field, the residue identity forces the action to be trivial and both cotangent
spaces vanish. A sign involution on `k[[x,y]]`, fixing `x` and negating `y`, with
2 invertible, gives `I_H=(y)` and cotangent kernel spanned by `dy`. DVRs and mixed
characteristic remain allowed; no characteristic equality or coefficient embedding
is present. Empty parameter lists in the proof include dimensions zero and the case
`D_H=0`. A group is always nonempty; `Finite` suffices for `Nat.card`, so no empty
or artificial enumeration case is excluded. The zero ring is already excluded by
the standard local-ring convention in the node and Mathlib.

Searches performed using the prescribed `msearch.py` wrapper:

* LeanFinder: "A finite group of invertible order acting trivially on the residue
  field of a regular local ring has regular quotient by the differences and
  cotangent space the coinvariants". Eight hits, including the standard residue
  field module structure on CotangentSpace and invariant-subring quotient maps;
  none states fixed-subscheme quotient regularity.
* Loogle: `IsRegularLocalRing, MulSemiringAction`: zero hits.
* Mathlib grep: `(fixed|coinvariant|invariant).*[Rr]egular|[Rr]egular.*(fixed|coinvariant|invariant)`
  in RingTheory: zero hits.
* LeanSearch: "A finite tame group acting trivially on the residue field of a
  regular local ring has regular fixed point quotient and cotangent space the
  coinvariants". Eight hits, principally representation coinvariants and
  `finrank_cotangentSpace_eq_zero`; none is the statement. The full definitions
  of `Representation.Coinvariants.ker`, `Coinvariants`, and `mk` were read.
  They require a supplied linear representation, rather than constructing the
  local action's cotangent maps, so they do not supply this missing interface.
* `rg` of Mathlib Ideal/Cotangent and LocalRing located `Ideal.mapCotangent`
  (linear over a supplied common algebra base) and the standard cotangent API.
  `mapCotangent` alone does not provide the residue-linear action or the common
  residue-field scalar transport for a general local ring without a coefficient
  field. The representative equations express precisely that canonical map.
* `rg` of both project Lean roots for `tameFixed`, `tame_fixed`, the item id,
  coinvariant/cotangent combinations and proposed declaration names: no match.
  The required `grep -rn` of the item id in WeilConjectures also had no match.
  RingTheory searches for fixed-point, coinvariant and tame concepts found only
  unrelated Hopf-module kernels, Kummer and DVR ramification material.
* Scanning DAG statements for cotangent/coinvariant/fixed-point concepts and
  regular local rings found the item and geometric consumers, plus existing
  regular-quotient and general cotangent nodes; none defines this local fixed
  ideal or provides this regularity-and-canonical-cotangent statement.

No statement dispute or source correction is needed. All newly declared helpers
are listed in `lean.declarations` and have source/blueprint docstrings. There is
only one postponed theorem, matching the assigned DAG node.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
