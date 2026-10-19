## Worker report

The module `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction` defines the
continuous-function commutative-ring presheaf and its pro-etale sheaf, using pointwise ring
operations and restriction by precomposition.  It equips the finite extension with the spectral
norm, defines the integral and rational coefficient sheaves, defines the positive finite quotient
rings and their quotient tower, and takes the categorical inverse limit of the tower.  It also
defines the sectionwise localization presheaf and its sheafification.  The main statement is
`AlgebraicGeometry.Scheme.continuousCoefficientImmersionRestriction`.

The binders render the node as follows.  `l` and `[Fact l.Prime]` are the prime and its primality;
`E`, `[Field E]`, `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]` are the finite coefficient
extension.  `X : Scheme.{u}` is the base scheme, with `[IsLocallyNoetherian X]` and
`[CompactSpace X]` rendering “noetherian” as locally Noetherian plus quasi-compact.  The morphism
`h : Z ⟶ X` and `[IsImmersion h]` render a locally closed immersion (Mathlib's immersion class is
the closed-then-open factorization).  The four conjuncts are respectively the adic inverse-limit
comparison, localization at the selected uniformizer, and the integral and rational inverse-image
comparisons along `h`.  The helper declarations and their docstrings record the coefficient-map
and composition compatibility clauses used by the source proof.

The statement dependencies used are: `Padic.coefficientExtensionIntegers`,
`Padic.coefficientExtensionUniformizer`, and `Padic.coefficientExtensionRing` from
`Sheaf.NumberTheory.Padics.CoefficientExtension`; `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.Scheme.ProEt`, `AlgebraicGeometry.IsClosedImmersion`, and
`AlgebraicGeometry.IsOpenImmersion` from Mathlib; `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`
from `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`; `CategoryTheory.constantSheaf` from
`Mathlib.CategoryTheory.Sites.ConstantSheaf`; `CategoryTheory.Limits.limit` from
`Mathlib.CategoryTheory.Limits.HasLimits`; and the recorded ringed-site, derived-category,
tensor, and finite-coefficient modules are imported to preserve the stage-3 proof plan.

Edge cases checked: the quotient tower is indexed by `ℕᵒᵖ` at level `n+1`, so only positive
levels occur; the zero scheme is allowed by the existing pro-etale site and sheaf definitions;
`Z` is not separately assumed noetherian because an immersion into a noetherian scheme supplies
that property in the source proof; and no nonzero or characteristic hypothesis was added.
The `ULift` wrappers only place coefficient rings in the sheaf universe and do not alter their
ring operations or the continuous-function construction.

Searches made before introducing the declarations were:

- `msearch.py leanfinder` for “continuous p-adic coefficient sheaves restrict to locally closed
  subschemes and rational coefficients are localization of integral coefficients”: no matching
  declaration (only generic restriction and lattice hits).
- `msearch.py leanfinder` for inverse image of continuous-function coefficient sheaves: no match.
- `msearch.py loogle` for `Sheaf`, `ContinuousMap`: generic continuous-map presheaves only; no
  pro-etale finite-extension comparison.
- `msearch.py leansearch` for continuous coefficient sheaves under immersions: service unavailable,
  with zero hits.
- `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` for `pro.?etale|continuous.*coefficient`:
  only Mathlib's generic `continuousMapPresheaf` and `ellAdicSheaf`; no finite-extension theorem.

No `STATEMENT-DISPUTED` flag was found necessary.  The main theorem proof and the named comparison
lemmas are `sorry` statements as required for stage 2; all definitions have concrete data.

## Earlier second reading (a previous round; superseded)

I reopened the node and the module.  The hypotheses match the prime, finite extension, noetherian
base, and locally closed immersion clauses.  The four displayed conjuncts match the inverse-limit,
localization, integral restriction, and rational restriction clauses.  The continuous-function
presheaf uses pointwise operations and precomposition, the quotient tower uses the stated quotient
maps, and localization is the sheafification of sectionwise `Localization.Away`.  The only universe
adjustment is the explicit `ULift`, which is a categorical size transport.  No dependency module was
needed because every recorded dependency declaration is imported and used.

## Second reading by Q34

I independently read the current node, every statement-dependency record, the dependency
signatures, and the sandbox module. The supplied source is Bhatt--Scholze rather than a
Stacks .tex place: I read Lemmas 4.2.12 and 6.5.8(1), Definition 6.8.1, Lemma 6.8.2,
and the paragraph immediately before Definition 6.8.6 in the authors' paper
(https://www.math.uni-bonn.de/people/scholze/proetale.pdf). The literature directory on
this machine does not contain that PDF. Section 6.8 initially permits any scheme;
Lemma 6.5.8 uses constructible locally closed subsets; the paragraph before 6.8.6
explains that locally closed immersions are constructible in the topologically
noetherian case. The node's noetherian assumption suffices and is retained. Localization
at the chosen uniformizer agrees with localization at ℓ by its DVR decomposition.

The node's objects, hypotheses and conclusion clauses, matched item by item:

1. Prime ℓ: `(l : ℕ) [Fact l.Prime]`. Exact; primes 2 and all other primes are included.
2. Finite extension E/Qℓ: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`. Exact finite dimension, not a field-extension
   finite-type hypothesis. The coefficient dependency is the recorded
   `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
   `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`, and
   `coefficientExtensionRing`; I opened their constructions in CoefficientExtension
   and its recorded CoefficientExtensionFinite import. The topology uses the
   `AbsoluteValue.toNormedField` spectral norm and the valuation-ring subspace topology.
3. Scheme and its small pro-etale site: `X : Scheme.{u}`, `X.ProEt`,
   `ProEt.topology X`. Exact Mathlib site, as used by the recorded
   ProEtaleDerivedCategory and ProEtaleInverseImage modules: objects in universe u+1,
   morphisms in u, coefficient category `CommRingCat.{u+1}`. No site-universe equality
   or new Small/Noetherian/field hypothesis is introduced by a helper.
4. Continuous-function rings A_X and E_X: `integralCoefficientSheaf` and
   `rationalCoefficientSheaf`, both instances of `continuousCoefficientSheaf`.
   `continuousMapPresheafCommRing` has carrier C(|V|,T), pointwise ring operations,
   and restriction `ContinuousMap.comp` with the scheme map. The ULift is on the
   coefficient carrier, with the transported topology and ring structure.
   `continuousMapPresheafCommRing_isSheaf` gives sheafhood; the small-site sheaf is
   the existing continuous pushforward/restriction. Exact.
5. Module/tensor convention: retained imports of the recorded `ringedSiteModules`
   and `siteSheafTensorRight` interfaces. I opened both signatures: they use actual
   SheafOfModules and sheafified sectionwise tensor, with independent module size.
   The node asserts ring-sheaf comparisons and has no module/tensor conclusion to
   add; no module parameter or additional tensor hypothesis is appropriate here.
6. Noetherian base: `[IsLocallyNoetherian X] [CompactSpace X]`. Exact conjunction
   from `pqf-def-locnoeth` and `def-weil-pbc-quasi-compact-scheme`; CompactSpace
   imposes no Hausdorff condition. Neither a characteristic restriction nor a
   separate noetherian assumption on Z was added.
7. Positive discrete quotient coefficients and quotient maps: `finiteCoefficientRing`
   uses `coefficientExtensionRing l E (n+1)`, `finiteCoefficientRingMap` is the
   canonical quotient factor map, and `finiteCoefficientTower` applies the recorded
   `constantSheaf` functor. Its index is ℕᵒᵖ; n=0 means exponent 1. Exact.
8. Canonical completion comparison: witness `i` is an isomorphism to
   `finiteCoefficientLimit`, the actual `Limits.limit` of that tower. For every n,
   witness `q` identifies the constant quotient sheaf with its continuous-function
   presentation, preserving all constant sections through `toSheafify`. The equation
   after `i.hom ≫ limit.π ... ≫ q.hom` is pointwise quotient reduction by
   `Ideal.Quotient.mk`. These formulas determine the comparisons; arbitrary
   isomorphisms do not meet the repaired statement. Exact.
9. Canonical localization comparison: witness `b` is from
   `integralCoefficientLocalization`, constructed as `presheafToSheaf` of the
   sectionwise `Localization.Away` presheaf. Its
   `integralCoefficientLocalizationNormalized` clause identifies every integral
   numerator with its image in E. A ring map out of localization is uniquely
   determined on numerators, hence also on all fractions. Exact.
10. Every locally closed immersion: arbitrary `h : Z ⟶ X` with `[IsImmersion h]`.
    I opened Mathlib Morphisms/Immersion: this is embedding + locally closed range +
    surjective stalks, with its closed-then-open `liftCoborder` factorization. Exact.
11. Integral and rational ring-sheaf restrictions: witnesses `cA` and `cE` use the
    recorded `proEtaleSheafInverseImage`, not a constant-coefficient substitute.
    Their `integralCoefficientRestrictionNormalized` and
    `rationalCoefficientRestrictionNormalized` clauses say that the ring-sheaf
    adjunct sends s to s composed with the first projection of the chosen fibre
    product. I checked the dependency's actual order: V ×_X Z, variable factor first.
    The adjunction bijection determines each inverse-image map uniquely. Exact.
12. Compatibility with A→E: witnesses `aX`, `aZ` satisfy
    `integralRationalCoefficientNormalized` (pointwise valuation-ring inclusion).
    The equation `h⁻¹(aX) ≫ cE.hom = cA.hom ≫ aZ` is the actual coefficient square,
    not a sentence only in a docstring. Exact.
13. Compatibility with composition: for arbitrary `W`, `k : W ⟶ Z` and
    `[IsImmersion k]`, the witnesses `dA`, `dE`, `eA`, `eE` have the same pullback
    normalizations. The final two equations identify eA and eE with the successive
    restrictions after `proEtaleRingInverseImageComp k h`. I opened that construction:
    it is the adjunction mate of canonical fibre-product pasting. Exact; k may be an
    identity or have empty source. The helper comes from the already landed
    `lem-weil-pbc-profinite-coefficient-inverse-image`, now cited in stmt_deps.

Mismatches found and repaired:

- H3: the former main theorem was only four `Nonempty` clauses. It neither fixed
  canonical maps nor asserted the coefficient square or composition. The report and
  docstring claimed compatibilities absent from the signature. Replaced those clauses
  by explicitly normalized isomorphism witnesses and both compatibility equations.
- H3: the four separate comparison helper theorems were stronger than the node's
  hypothesis list (the restriction helpers omitted the noetherian base), while still
  failing to specify canonical maps. Removed them; the complete assertion now lives
  in the one main theorem with the node's hypotheses.
- H8: the old theorem docstring had no six-step proof. Added the node's complete route:
  fpqc descent; discrete open-fibre gluing; complete-DVR residue lifting and continuity;
  local denominators and sheafification; finite quotient restriction and limits;
  localization adjunction, coefficient square and composition. Added proof plans to
  the named functor-law helpers. No theorem proof was filled.
- H9: supplied the module header/public imports and standardized the blueprint markers.
  Removed the unused X binder from the global sheafhood lemma. Restored the imports
  of the recorded immersion-limit, weakly-etale-localization and finite constant-ring
  proof dependencies, plus the Mathlib completion and finite-quotient leaves.
- Type checking the new formulas required exposing opaque section carriers. Added
  `continuousCoefficientValue` and its integral/rational/finite specializations as
  concrete evaluation functions, using `@id` to expose the carrier. These are actual
  evaluations; they choose no map or object. The normalization predicates are real
  section formulas, with no `sorry` data and no file-local notation or instances.

Edge cases: empty schemes and empty source immersions use the same sheaves and
adjunction, and no nonemptiness binder was introduced. On the empty object the unique
continuous function and unique sheaf section meet every normalization. Positive levels
are exactly n+1, so there is no accidental level-zero quotient; ℕᵒᵖ has the required
inverse arrows. Zero sections, zero fractions, all constant sections, identity immersions,
and k=identity are covered by the equations. No requirement ℓ≠char(X) appears: X is
arbitrary in characteristic, whereas E is the given extension of Qℓ. The common ambient
universe u is arbitrary; the site's object/morphism universe distinction is preserved,
and ULift performs only the coefficient size transport.

Independent searches: I ran `msearch.py leanfinder` for "sheaf of continuous functions
into a topological ring inverse image canonical comparison immersion" (eight generic
open-immersion hits, none this theorem), and `msearch.py loogle` for
`"ContinuousMap", "RingHom"` (generic continuous-map ring structures and coercions,
none this theorem). LeanSearch for the inverse limit of constant quotient sheaves of a
finite p-adic valuation ring returned Internal Server Error and is recorded unavailable,
not a negative mathematical verdict. I searched Mathlib, the slopmaster2 WeilConjectures
sources, and lean/Sheaf using coefficient/valuation/localization/completion and immersion
terms, and opened the relevant source hits rather than relying on names.

H4 search findings: the exact general theorem does not already exist. Mathlib's
`continuousMapPresheaf` and `continuousMapPresheafAb` supply the underlying functions and
fpqc descent. The 51-module framework's `ProEtale.continuousMapRingSheaf` was opened in
the required shared checkout: it is RingCat-valued, takes `T : Type` (universe zero), and
lifts the entire function carrier. It cannot express this CommRingCat-valued construction
with `E : Type u` without a transport/generalization. The present generalized ring
presentation retains the same underlying Mathlib functions and operations and supplies
no competing site, topology or coefficient datum. The existing
`WeilConjectures.completedIntegralCoefficientSheafUnrestricted` is RingCat-valued with
commutativity forgotten; `AdicCoefficientDatum` instead requires a general complete
Noetherian datum and uses the connected-components/sheafification finite-ring
presentation. Neither is the literal positive constant CommRingCat tower used here.
I also opened the existing finite-coefficient ring sheaf and finite constant-ring
comparison: these have the correct underlying coefficient meaning for the proof, while
the new q formulas identify precisely the presentation used in this item's tower.
No missing independent definition node or dependency replacement is required.

The node's natural-language statement is correct and unchanged; no statement_change or
citer audit is needed. The only added statement dependency is the landed canonical
inverse-image composition interface. Every delivered declaration is recorded under the
item's lean.declarations, and lean.statement is regenerated verbatim from the repaired
main signature. Validation results are recorded below after the prescribed compile
and delivery preflight.

Validation: the prescribed scompile.py invocation passed with no diagnostics for both
sandbox compilation (18.2 seconds) and the library-path check (14.1 seconds), within
the standard per-file limit. `autoImplicit false` is in force, every universe and
variable in the delivered signature is bound, and all theorem proofs remain `sorry`.
