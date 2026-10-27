## Worker report

The module `Sheaf.RingTheory.DvrIndexOneSeparableBaseChange` states
`IsDiscreteValuationRing.dvr_index_one_separable_base_change`, with its sole proof
`sorry`. No definitions, dependency repairs, new nodes or statement corrections
are needed. The node copy changes only `lean`.

Hypothesis and clause correspondence:

- A and B are DVRs: explicit `CommRing`, `IsDomain`, and `IsDiscreteValuationRing`
  instances on independently universe-polymorphic `A : Type u`, `B : Type v`.
- The injective local map A to B is `Algebra A B`, `hinj`, and
  `IsLocalHom (algebraMap A B)`. Locality is the usual pullback condition on
  maximal ideals, equivalently reflection of units for these local rings.
- K and L are the respective fraction fields: `Field K`, `Field L`,
  `Algebra A K`, `IsFractionRing A K`, `Algebra B L`, `IsFractionRing B L`.
  `Algebra A L`, `Algebra K L` and the two `IsScalarTower` instances express
  compatibility of the specified fraction-field inclusions with A to B.
  They impose no extra mathematical restriction: an injective map of domains
  has exactly this induced map on fraction fields.
- Index one is exactly `hindex`, the equality of the extended maximal ideal
  of A and the maximal ideal of B.
- Residue separability is `hsep : Algebra.IsSeparableExtension
  (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)`, for the canonical
  residue algebra induced by the given local map. This is the recorded
  possibly transcendental separability, not algebraic separability.
- An arbitrary finite extension N/K is `N : Type y`, `Field N`, `Algebra K N`,
  `FiniteDimensional K N`; `Algebra A N` and `IsScalarTower A K N` record
  the compatible restriction to A. There is no separability condition on N/K.
- R is literally `integralClosure A N`. E is literally the quotient
  `(L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)`; C is literally `integralClosure B E`.
  Tensor multiplication, reduction by all nilpotents and the B-algebra on E
  are Mathlib's structures, not assumed descriptions of arbitrary rings.
- The existential ring map `f : R →+* C` is required, for every r, to satisfy
  `(f r : E) = Ideal.Quotient.mk _ (Algebra.TensorProduct.includeRight (r : N))`.
  This specifies exactly r mapped to the class of 1 tensor r. Since C is a
  subtype of E, the formula determines f uniquely; no arbitrary map is used.
  Existence of this specified map is included in the conclusion, never assumed.
  This avoids making another definition of the normalization map already present
  in the downstream Epp module. Importing that downstream theorem would create a
  proof-import cycle when it later imports this statement.
- Every maximal q of C is `∀ (q : Ideal C) [q.IsMaximal]`. Its contraction n
  is `q.comap f`, and the first local conjunct is precisely its `IsMaximal`.
- R_n is the recorded `Localization.AtPrime (q.comap f)` with the DVR conclusion.
  Its domain instance comes from the integral closure inside the field N.
- C_q is `Localization.AtPrime q`. Because C itself need not be a domain,
  the theorem explicitly concludes `∃ hdom : IsDomain (Localization.AtPrime q),
  @IsDiscreteValuationRing ... hdom`. This covers all product branches.
- n C_q = q C_q is the equality of `Ideal.map` of n along the composite
  R to C to C_q and `Ideal.map` of q along C to C_q.
- The residue conclusion is exactly `Algebra.IsSeparableExtension
  (q.comap f).ResidueField q.ResidueField`, with its algebra explicitly
  `(Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra`. Thus the map is
  the canonical one induced by contraction, with no independent residue action.
- All these local conjuncts precede the implication assuming
  `IsNoetherianRing (B ⊗[A] integralClosure A N)`, so they are unconditional.
  No completeness or essential finite type hypotheses appear anywhere.
- Under that Noetherian assumption the first global conjunct is
  `IsReduced (L ⊗[K] N)`. The second is an actual B-algebra equivalence e
  from `B ⊗[A] R` to C, required on every pure tensor to satisfy
  `e (b ⊗ₜ[A] r) = algebraMap B C b * f r`.
  Since pure tensors generate the tensor algebra, this is exactly the specified
  canonical comparison being an isomorphism, rather than some unrelated
  isomorphism of the two rings. Expressing an isomorphism by such an equivalence
  is logically equivalent to bijectivity of the canonical comparison map.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
  Its class signature requires the separately supplied `IsDomain`, extends
  principal ideal and local ring conditions, and excludes fields.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, used throughout for field extensions
  and the original ring map (available through the public imports).
- `WeilConjectures.FieldTheory.SeparableExtension`: `Algebra.IsSeparableExtension`.
  Its actual definition quantifies over finitely generated intermediate fields
  and asks for `Algebra.IsSeparablyGenerated`, as the dependency node requires.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, the actual
  subalgebra of integral elements.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; tensor ring and
  quotient structures are imported from `Mathlib.RingTheory.TensorProduct.Quotient`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  `Ideal.ResidueField.map`; the latter's signature requires exactly the contraction
  equality supplied here as rfl.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.

Plain proof imports cover all already stated proof dependencies, including
PID torsion-free flatness (`Mathlib.RingTheory.Flat.TorsionFree`), flat ring maps
(`Mathlib.RingTheory.RingHom.Flat`), integral lying over
(`Mathlib.RingTheory.Spectrum.Prime.Topology`), Krull intersection
(`Mathlib.RingTheory.Filtration`), normality
(`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`), and
`WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal`.
The proof-only nodes `lem-sfb-dvr-algebraic-normalization-structure` and
`lem-sfb-separable-residue-finite-tensor-fields` have no recorded Lean declaration
in the read repository and are not statement prerequisites; no nonexistent
modules are imported. The complete eight-step node proof is included in the
main theorem's docstring for stage 3.

Sources read: `literature/stacks-project/more-algebra.tex`, labels
`lemma-extension-dvrs-formally-smooth` (09E7), `remark-construction` (09EM),
and `lemma-formally-smooth-goes-up` (09EQ). The already accepted node qualifies
09EQ's global comparison by the Noetherian tensor hypothesis; the statement
preserves that qualification exactly and does not reopen the stage-1 split.

Edge cases checked before writing:

- N = K gives R = A, E = L and C = B: the local conclusions become the original
  index and residue assumptions; the Noetherian comparison is the identity.
- Purely inseparable finite N/K remains allowed, in every residue characteristic.
  No finite separability, Nagata, excellence or completeness hypothesis is added.
- L tensor_K N may have multiple field factors after reduction: C is not assumed
  to be a domain and all maximal branches are quantified independently.
- Non-finitely-generated separable residue extensions are allowed by the actual
  recorded `Algebra.IsSeparableExtension`, unlike `Algebra.IsSeparable`.
- Tensor Noetherianity occurs solely inside the global implication; failure of
  Noetherianity does not discard a local assertion or force reducedness globally.
- DVRs are nontrivial and not fields. All five object universes are explicit and
  independent; there is no restriction equating ring or field universes.
- Existential f cannot make a conclusion vacuous: it must exist and satisfy its
  ambient formula. That formula makes it unique. The pure tensor condition also
  uniquely determines the comparison isomorphism, including the identity case.

Searches made through the prescribed msearch.py wrapper (2026-10-24):

- LeanFinder: "An injective local map of discrete valuation rings with ramification
  index one and separable residue extension preserves these properties after
  integral closure in a finite fraction field base change". Eight hits, including
  `IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx`,
  `Algebra.isUnramifiedAt_iff_map_eq`, `Algebra.IsUnramifiedAt.of_liesOver` and
  formal-unramified residue criteria. None gives this theorem without essential
  finite type or algebraic residue separability restrictions.
- Loogle: `IsDiscreteValuationRing, Algebra.IsSeparableExtension` returned no hits
  and unknown identifier for the project-specific separability predicate.
  Repeated with `IsDiscreteValuationRing, integralClosure`: zero hits, valid query.
- Mathlib grep: `toIntegralClosure|ramificationIdx.*base|base.*ramificationIdx`
  in RingTheory returned five hits in Smooth/IntegralClosure. Its
  `TensorProduct.toIntegralClosure` has target the closure in an unreduced
  B tensor_A N and its isomorphism results require algebraic smoothness;
  it is not the statement of this node.
- LeanSearch: "Index one and separable residue extensions of DVRs persist under
  normalization after finite field base change, with tensor comparison isomorphism
  when the tensor algebra is Noetherian". Eight hits: unramified and etale
  base-change, integral residue algebraicity and tensor algebraicity results;
  no exact combined statement with these hypotheses.
- rg over `lean/WeilConjectures` and `lean/Sheaf`: DVR/base-change, index-one,
  normalization-map and normalized tensor patterns. Related Abhyankar results
  have additional tame/separability hypotheses. EppEssentiallyFiniteTypeTraits
  contains the downstream normalization-map formula, which was read; this module
  neither duplicates its definitions nor imports the downstream theorem.
- grep for the exact node id in `lean/WeilConjectures`: no result. rg for the new
  declaration in `dag/lean_names_upstream.json`, both project roots and Mathlib:
  no existing name.

Validation: scompile.py compiled the sandbox and final library-name module
cleanly (7.6 and 3.4 seconds respectively, no warnings or errors). All variables
and universes are bound, `autoImplicit` is false, all lines are at most 100 columns,
there is one theorem and one expected sorry. No statement dispute remains.

## Second reading by Q104

No second reading by a worker: under the dispatcher's direct-delivery instructions,
the maintainer's independent review is the independent reading. A self-check
against the open node and file verified each hypothesis and each conjunct as
listed above; in particular, both canonical-map formulas and the scope of the
Noetherian implication were checked explicitly. No mismatch or correction found.
