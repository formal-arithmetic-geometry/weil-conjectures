## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence` states the ordinary,
unbounded, constant-module support sequence and its realization of the derived support
triangle. All new theorem proofs are `sorry`; the definitions contain actual data.
No node statement or proof is corrected, no dependency is replaced, and no new notion
needs a separate DAG node. All auxiliary declarations belong to this item's specified
sequence, canonical comparison maps, and naturality clauses.

Hypotheses and clauses, matched individually:

- Schemes and the closed immersion: `{Z P U : Scheme.{u}}`, `(i : Z ⟶ P)` and
  `[IsClosedImmersion i]`. The open immersion is `(j : U ⟶ P)` with
  `[IsOpenImmersion j]`. Complementarity is exactly
  `hij : Set.range i.base = (Set.range j.base)ᶜ`.
- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The auxiliary sequence and maps need only commutativity; finiteness is retained in
  the main assertion and the boundary-naturality assertion. The common `u+1` coefficient
  universe is the recorded small-etale coefficient convention; it covers every finite ring
  by universe lift and makes no equality between site object and morphism universes.
- Ordinary constant-A module sheaves are the existing
  `Sheaf P.smallEtaleTopology (ModuleCat.{u+1} A)`, and the other two analogous categories.
  Their unbounded derived categories are `_root_.DerivedCategory` of those categories.
  No bounded or constructible subcategory occurs.
- The specified H_A is the existing `closedUpperShriek (ModuleCat A) i j`, definitionally
  `sectionsWithSupport (ModuleCat A) j ⋙ upperStar (ModuleCat A) i`. Its support functor
  is the pointwise kernel of the actual `upperStarLowerStarAdjunction` open unit.
  Thus there is no private copy of H_A or of a kernel construction.
- The canonical supported identification is the closed adjunction unit at the support
  kernel, invertible by upstream
  `isIso_upperStarLowerStarAdjunction_unit_app_of_isZero`. The inverse followed by the
  kernel inclusion is the counit of the existing
  `lowerStarClosedUpperShriekAdjunction`; its `lowerStarClosedUpperShriekHomEquiv`
  explicitly uses this formula. `etaleSupportSequence.f` uses precisely that counit,
  mapped to complexes by `Adjunction.mapHomologicalComplex`, named as
  `etaleSupportInclusion`. The open termwise unit is named `etaleSupportRestriction`.
  Both definitions supply the actual existing adjunction maps with explicit source and
  target functors, allowing the kernel checker to reuse their types. Consequently its first
  object is termwise i_*H_A(I), not an unspecified supported object.
- A degreewise-injective K-injective model is
  `(I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat A)) ℤ)` with
  `[I.IsKInjective] [∀ r : ℤ, Injective (I.X r)]`. An arbitrary derived object `L` and
  its representing isomorphism `e : DerivedCategory.Q.obj I ≅ L` are explicitly bound.
- `etaleSupportSequence.g` is the termwise open adjunction unit. The named theorem
  `etaleSupportSequence_zero` supplies its zero composite with the counit. The
  `ShortComplex.mk` definition has these exact objects and arrows.
- Main-theorem `hS : (etaleSupportSequence A i j hij I).ShortExact` gives the leading
  and trailing zeros, exactness, monicity, and epicity. It is exactly degreewise short
  exactness by `HomologicalComplex.shortExact_iff_degreewise_shortExact`, without an
  additional assumption or a weaker derived-exactness replacement.
- Naturality on chain maps is actual data `etaleSupportSequenceMap A i j hij f`, whose
  components are termwise i_*H_A(f), f, and j_*j^*(f); its two squares are the existing
  counit and unit naturality equations. Composition and identities are inherited from
  these functors and equality of morphisms of short complexes componentwise.
- `etaleSupportShriekComparison` is an actual isomorphism Q(H_A I) to Ri_A^!(QI).
  It is the inverse `rightDerivedFunctorObjQIso` followed by `rightAdjointUniq` from the
  constructed closed derived adjunction to the dependency's chosen ordinary right adjoint.
  This is the unique counit-compatible comparison, not an arbitrary object isomorphism.
  Applying that right adjoint to e transports it to the arbitrary L.
- `etaleSupportFirstComparison` applies exact termwise i_* and its fixed
  `mapDerivedCategoryFactors` / `rightDerivedFunctorIsoMapDerivedCategory` comparison to
  that shriek comparison. This accounts for the precise first object of the triangle.
- The theorem supplies `hJ : (j^* I).IsKInjective` as a conclusion, not an assumption.
  `etaleSupportThirdComparison` is the inverse `rightDerivedFunctorObjQIso` for j_*,
  followed by j_*'s derived action on the exact j^* comparison. It computes
  Q(j_*j^*I) ≅ Rj_*j^*(QI); applying Rj_*j^* to e gives the stated comparison for L.
- A single `δ` is a natural transformation on the full ordinary derived category from
  Rj_*j^* to (i_*Ri_A^!)[1]. Its `Triangle.mk` components are distinguished, and their
  first two arrows are the actual counit of `Adjunction.ofIsLeftAdjoint R(i_*)` and
  the actual unit of `mapDerivedUpperStarLowerStarAdjunction`. These are precisely
  the arrows used in `lem-exc-closed-support-triangle`.
- The theorem supplies a triangle isomorphism `t` from the canonical
  `DerivedCategory.triangleOfSES hS` to this counit/unit triangle at L. Its three
  components are constrained to the above first comparison transported through e,
  e itself, and the above third comparison transported through e. A triangle
  isomorphism includes all three commuting squares, hence the connecting morphism.
  `triangleOfSESδ` uses the existing cone-to-quotient inverse with Mathlib's cone
  sign, not a newly chosen boundary.
- `etaleSupportSequence_boundary_naturality` spells out the third square for every
  chain map between the stated models and for any short-exactness witnesses. It is
  exactly δ_I followed by Q(i_*H_A(f))[1] = Q(j_*j^*(f)) followed by δ_J.
- No injectivity of an underlying abelian sheaf or of any scalar restriction is bound.
  Injectivity always lives in the module-valued etale sheaf category itself.

Dependency declarations read and used (full source signatures and docstrings inspected):

- `def-weil-pbc-scheme-conventions` is a convention node with no declaration:
  `Scheme`, `IsClosedImmersion`, `IsOpenImmersion`, and their actual base ranges are used.
- `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` and the upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` = `DerivedCategory (Sheaf ... (ModuleCat A))`.
- `def-pur-kinjective-complex`: Mathlib
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, `CochainComplex.IsKInjective`.
- `lem-exc-closed-support-triangle`: `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`,
  `AlgebraicGeometry.Etale.exists_etale_closedSupportTriangle`, with exactly its chosen
  ordinary derived adjunctions and natural-transformation type.
- Direct/inverse image: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`.
  The node's bounded-below direct-image clause is irrelevant to this unbounded item;
  its recorded underived functor is used and its total derived functor is the existing R.
- Injectivity: `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective` (the `InjectiveResolution` record is not needed for an
  already supplied unbounded complex).
- Exactness: Mathlib `CategoryTheory.ShortComplex.ShortExact`, imported via
  `Mathlib.Algebra.Homology.ExactSequence` and `DerivedCategory.ShortExact`.
- The proof-only recorded modules are imported without `public`: supported kernel
  adjunction, closed-immersion essential image, ringed-site injective mono restriction,
  independent-universe Grothendieck module sheaves, module inverse-image exactness,
  functorial injective K-injective replacement, localized K-injective restriction,
  open restriction, etale slice equivalence, degreewise short exactness, and adjoint
  uniqueness. `Sheaf.CategoryTheory.KInjectiveTotalDerived` and
  `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint` arrive publicly through the support
  triangle dependency, and right-adjoint preservation and homotopy adjunction arrive
  through the imported upstream derived-adjunction modules.
- Canonical H_A, its adjunction, and its derived adjunction come from
  `WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek`:
  `sectionsWithSupport`, `closedUpperShriek`, `lowerStarClosedUpperShriekAdjunction`,
  `derivedLowerStarClosedUpperShriekAdjunction`. The exact-functor and K-injective
  model comparisons are `Functor.mapDerivedCategoryFactors`,
  `rightDerivedFunctorIsoMapDerivedCategory`, and `rightDerivedFunctorObjQIso`.
- Canonical triangle and boundary: `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`,
  `DerivedCategory.triangleOfSES`, `triangleOfSESδ`, and `triangleOfSESδ_naturality`.

Source checked locally: `literature/stacks-project/sites-cohomology.tex`,
`lemma-restriction-along-monomorphism-surjective` (Tag 093X), and
`literature/stacks-project/etale-cohomology.tex`,
`lemma-cohomology-with-support-triangle` (Tag 0A45), including its injective-complex proof.
The seven-step proof docstring follows all seven steps of this DAG node. In particular,
the module statement retains the node's module-linear, unbounded refinement.

Edge cases checked before writing:

- U empty and Z=P: the open restriction is zero and the sequence is the support
  isomorphism followed by zero. No nonemptiness or properness is imposed.
- Z empty and U=P: the kernel is zero, open unit invertible; the statement gives the
  zero-to-I-to-I sequence. P empty also satisfies all clauses.
- A the zero ring: every module sheaf is zero; no nontriviality or cardinality lower bound.
- I zero and arbitrary negative degrees: no bound, positive-degree restriction, or
  termwise nonvanishing. A non-bounded-below K-injective model is allowed verbatim.
- e may be any representing isomorphism, including an automorphism of QI. Its action
  is explicitly retained in all three triangle components, so the statement does not
  silently specialize to identity representations.
- The hypotheses do not include quasi-compactness of j or Noetherianity of schemes:
  Tag 093X uses the open-fibre-product monomorphism directly.

Searches for an existing statement (2026-10-21):

- `msearch.py ... leanfinder` query: "Injective etale module sheaves support kernel short
  exact sequence of complexes natural derived support triangle". Eight hits, notably
  `DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective`,
  `CochainComplex.isKInjective_of_injective`, and `CochainComplex.cm5b`; none is this
  ordinary etale, unbounded support-sequence realization.
- `msearch.py ... loogle` query:
  `CategoryTheory.ShortComplex.ShortExact, DerivedCategory.triangleOfSES`. Twelve hits
  include `triangleOfSES`, `triangleOfSES_distinguished`, `triangleOfSESIso`, and
  `triangleOfSES.map`; the generic SES API is used, not restated as a new notion.
- `msearch.py ... leansearch` query: "The canonical closed support exact sequence for a
  degreewise injective K injective complex of etale module sheaves realizes the derived
  adjunction counit and open unit triangle". Eight hits on generic K-injectives and
  injective-resolution lemmas; no etale support sequence or complete realization.
- `msearch.py ... grep` query: `sectionsWithSupport|closedUpperShriek|injective.*support`
  in `CategoryTheory`: zero Mathlib hits. Broader direct `rg` in `lean/WeilConjectures`
  and `lean/Sheaf` for support/short-exact/injective combinations found the existing
  generic H_A in `Derived.ClosedImmersionUpperShriek`, which is reused. The pro-etale
  `SupportsExact` and `SupportLocalizationTriangle` modules concern a different site,
  with bounded-below/quasi-compact restrictions; they do not state this item. The
  upstream `Derived.ClosedSupportTriangle` states a triangle at an object, without
  this injective-model SES or its normalized comparison data.
- Direct `rg` for this node id and the ten chosen declaration names in both source
  roots found no existing statement or name clash. No new definition node is created.

The theorem proofs intentionally postponed are `etaleSupportSequence_zero`,
`etale_injective_support_sequence`, and `etaleSupportSequence_boundary_naturality`;
all carry this node's source/proof docstring. No statement dispute or node fault found.

## Second reading by NM

The delivering worker reread the node and all three theorem signatures against the
actual helper bodies. This is a self-check, not a claim of an independent worker review:
the dispatcher forbids starting another agent and assigns independent review to the
maintainer. The rereading retained the exact prescribed counit/unit, checked directions
of both model comparisons and the boundary equation, and made the arbitrary L and its
representing isomorphism explicit rather than leaving them implicit in QI. The natural
boundary is shared across all derived objects; its SES realization fixes all three
triangle components. The degreewise assertion is encoded by Mathlib's equivalent
`ShortExact` on complexes. Definitions contain no postponed data, and the three proof
obligations are exactly the item's zero composite, short-exact/derived realization,
and naturality clauses. Validation results are recorded below after compilation/preflight.

Validation: final diagnostic-free source compiled through the prescribed `scompile.py`
against the live server build, with no errors or warnings: sandbox 36.1 s, library name
16.7 s, both within the unchanged 60-second limit. The typed termwise-arrow definitions
avoid repeated kernel conversion of the full adjunction constructions. The node differs
from the read-only base only in `lean`; the recorded main signature matches verbatim,
all ten declarations are listed, and the maximum source line width is 98 characters.
