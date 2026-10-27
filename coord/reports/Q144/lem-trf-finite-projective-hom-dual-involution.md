## Worker report

The module `Sheaf.Algebra.Homology.FiniteProjectiveHomDualInvolution` states
`CochainComplex.finiteProjective_homDual_involution` with `sorry`. It supplies four
transparent helpers belonging to this node: the single complex B[0], its recorded
module Hom dual, the linear projection/insertion coordinates, and the iterated
projection identifying the double dual. There are no other postponed proofs and
no new mathematical notions, dependency repairs, or statement corrections.

Hypotheses, clause by clause:

- The arbitrary commutative ring is `{B : Type u} [CommRing B]`.
- The integer cochain complex is `P : CochainComplex (ModuleCat.{u} B) ℤ`.
  The universe `u` is arbitrary, as in the recorded module total Hom API; there is
  no finiteness assumption on the underlying ring or sets of module elements.
- The bounds are `(a b : ℤ) (hab : a ≤ b)`; vanishing outside them is
  `hP : ∀ p : ℤ, p < a ∨ b < p → IsZero (P.X p)`.
- Finitely generated projective terms are precisely
  `[∀ p : ℤ, Module.Finite B (P.X p)]` and
  `[∀ p : ℤ, Module.Projective B (P.X p)]`.
- O is `moduleScalarDualTarget B`, an abbreviation for the existing
  `singleFunctor` construction. E is `moduleScalarDual P`, an abbreviation for
  `moduleHomComplex P O`; F is `moduleScalarDual (moduleScalarDual P)`.
- `moduleScalarDualCoordinates P i r h` is a B-linear equivalence when
  `h : i + r = 0`, constructed from Mathlib `Cochain.toSingleEquiv` and
  `ModuleCat.homLinearEquiv`. Its forward map projects the (i,0) coordinate and
  identifies O^0 with B; its inverse inserts that functional and zero elsewhere.
  Using i=-r gives exactly E^r ≃ Hom_B(P^(-r),B).
- `moduleScalarBidualCoordinates P p` first projects F^p to the dual of E^(-p),
  then precomposes with the inverse of the projection E^(-p) ≃ (P^p)*. Hence it is
  exactly the asserted F^p ≃ (P^p)**, without an arbitrary comparison choice.
- The first conjunct is the differential of E under these identifications:
  `(r + 1).negOnePow` is (-1)^(r+1), multiplying precomposition with
  `P.d (-(r + 1)) (-r)`.
- The second conjunct is the differential of F: the image of d_F(z) is
  `-(P.d p (p + 1)).hom.dualMap.dualMap` applied to the image of z.
- The third conjunct gives the precise reversed interval [-b,-a], using
  `r < -b ∨ -a < r`; the fourth gives finite generation and projectivity of
  every E term, with the same Mathlib predicates as for P.
- The existential `δ : P ≅ moduleScalarDual (moduleScalarDual P)` is a chain
  isomorphism, not just a degreewise or derived isomorphism.
- Its first clause specifies every component as
  `p.negOnePow • Module.Dual.eval B (P.X p) x` in bidual coordinates.
- Its second clause specifies every inverse component as
  `p.negOnePow • (Module.evalEquiv B (P.X p)).symm` after the same coordinates.
  The existing finite-projective reflexivity instance provides evalEquiv.
- Its third clause explicitly states the homogeneous evaluation formula for
  arbitrary `p q`, `hpq : p + q = 0`, and φ in E^q, using
  `(p * q).negOnePow`. The output is transported from O^0 by
  `HomologicalComplex.singleObjXSelf` and the input φ is evaluated via the
  actual (p,0) coordinate, avoiding hidden casts between P^p and P^(-q).
- Its fourth clause requires every other Hom coordinate (`r ≠ 0`) to be zero.
- Its final clause quantifies over every finite-projective bounded complex Q
  with its own arbitrary bounds c≤d and every chain map f:P→Q. It states the
  naturality of both coordinate identifications under precomposition and double
  precomposition, then gives the normalized signed evaluation ε on Q and the
  chain identity `δ.hom ≫ H(H(f,O),O) = f ≫ ε.hom`. ε's component formula fixes it
  uniquely as the same signed evaluation isomorphism; it is not an arbitrary
  isomorphism that could make naturality vacuous. Q's bounds need not equal P's.

Dependency declarations used:

- `def-weil-abstract-derived-category`: imported its recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the statement uses the
  existing `CochainComplex`, chain maps and category isomorphisms. No derived
  localization assumption is needed for a statement entirely about complexes.
- `def-sc-module-total-hom-complex`: public import
  `WeilConjectures.Algebra.Homology.ModuleHomComplex`, declaration
  `CochainComplex.moduleHomComplex`. No replacement complex is constructed.
- `def-weil-pbc-projective-module`: `Module.Projective`, from
  `Mathlib.Algebra.Module.Projective`, publicly available through Dual.Lemmas.
- `def-weil-finitely-generated-module`: `Module.Finite`, from
  `Mathlib.RingTheory.Finiteness.Defs`, publicly available through Dual.Lemmas.
- Added the already landed definition node `def-trf-module-hom-precomposition`
  to stmt_deps. Its existing:true record owns the actual chain map
  `CochainComplex.moduleHomPrecomp`, its linear components
  `CochainComplex.moduleHomPrecompComponent`, and their differential compatibility
  in `Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy`. The final naturality
  formula uses this construction; no homotopy-preservation theorem is used.
  This definition node depends only on the original cochain-complex and
  total-Hom definitions, so no dependency cycle is introduced.
- The proof dependency `lem-sf-finite-projective-dual` is a Mathlib match with
  no Lean record. Its matching `Module.dual_finite`, `Module.dual_projective`,
  the finite-projective reflexivity instance and `Module.evalEquiv` are provided
  by `Mathlib.LinearAlgebra.Dual.Lemmas` and Dual.Defs. This import is public
  because evalEquiv and the reflexivity instance occur in the statement.

Source reading: read More on Algebra, section-hom-complexes (0A8H),
item-evaluation in section-sign-rules (0FNG), and the first paragraph of the
proof of lemma-dual-perfect-complex (07VI). The theorem docstring gives all
seven DAG proof steps, grouping the two finite-projectivity/evaluation inputs
with their corresponding constructions. In particular the second differential
is negative double transpose, not the unsigned transpose; the signed map makes
it commute with d_P.

Edge cases checked mathematically before writing: the zero complex; the zero
ring; characteristic two (both signs become +1); a=b (one nonzero term);
intervals entirely below zero; odd and even, positive and negative degrees;
zero terms at either endpoint. No nonzero-ring, positive-degree, nonempty-
support or free-module hypothesis has been added. The support predicate uses
categorical `IsZero` of a ModuleCat object, not equality of a carrier type with
an arbitrary chosen zero type. In negative degrees `Int.negOnePow` records
parity directly, so no natural-number truncation loses a sign.

Searches for an existing statement (msearch.py, Q144/item):

- LeanFinder: "A bounded finite projective cochain complex is naturally
  isomorphic to its double module Hom complex by signed evaluation". Eight
  hits, including `Cochain.toSingleEquiv`, `fromSingleEquiv`, projective
  resolutions and K-projectivity; no full signed finite-projective involution.
- Loogle: `CochainComplex.HomComplex, Module.Dual`. Zero hits.
- Mathlib grep: `bidual|double.?dual|evalEquiv`, subdirectory
  `Algebra/Homology`. Zero hits.
- LeanSearch: "The Hom dual of a bounded finite projective complex is bounded
  finite projective and signed double evaluation is a natural chain
  isomorphism". Eight hits, including `Module.dual_projective`,
  `Module.dual_finite`, generic homology evaluation and perfect pairings; these
  are only component facts, and the component facts are reused.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `signed.*[bB]idual|finiteProjective_homDual_involution|moduleScalarDualCoordinates`,
  and exact item id. No existing full statement or name clash. Related ringed
  site signed biduality/localization statements concern different objects.
- Read `ScalarDualSignedAssembly`: its scalar projection and precomposition
  helpers are private. We use the underlying existing Mathlib projection and
  the public landed moduleHomPrecomp, rather than importing or duplicating
  that theorem's sheaf-comparison statement.
- Read the recorded module-Hom and precomposition declarations and full
  signatures/docstrings; read the Mathlib module finite/projective and duality
  declarations. Searched `dag/lean_names_upstream.json` for the new names and
  precomposition; no conflicting upstream names found.

Validation: server scompile.py compiles the module in sandbox and library
modes without errors or warnings. Only the main theorem has `sorry`. The file
uses module mode, public statement imports, explicit universes and variables,
and no private helper, local instance or local notation. No statement is
considered disputed and the natural-language node statement is unchanged.


## Repair of return on head 1a9d27212c79

H2: replaced the statement dependency `lem-trf-hom-dual-preserves-homotopies`
with its already landed owning definition node
`def-trf-module-hom-precomposition` (landed at c3276c46f03). Read the owner's
statement and existing:true Lean record, then the full moduleHomPrecompComponent,
moduleHomPrecomp_comm and moduleHomPrecomp signatures and docstrings. They supply
exactly the precomposition construction used here. Updated the dependency
paragraph above. The Lean module, entire lean record and natural-language
statement are unchanged from the returned delivery. Compared the sandbox node
with current main: all other fields agree, main has no lean record yet, and
this repair retains the four original definition dependencies. The prescribed
delivery wrapper rebases the packet onto current main before preflight.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
