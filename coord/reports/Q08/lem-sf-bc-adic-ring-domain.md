## Worker report

The module `Sheaf.Paper.SfBcAdicRingDomain` states the node in two declarations:
`AlgebraicGeometry.Scheme.sf_bc_adic_ring_domain` gives the arithmetic and normalized
finite free resolutions, and `AlgebraicGeometry.Scheme.sf_bc_adic_completed_domain`
gives the completed coefficient sheaf, integral full subcategory and reindexing.
Both proofs are `sorry`; there are no definitions, new nodes or dependency repairs.
The natural-language proof of each declaration is in its docstring, following all
five steps of the node. The two statements are clauses of this one DAG node.

The earlier interrupted worker mistook Q83's stage-1 merge for a stage-2 delivery.
The ledger entry at line 26687 and Q83's report record only a completed split:
Q83 explicitly wrote no Lean, and the live node has no lean record. Consequently
there is no existing stage-2 delivery to repeat or overwrite. There is no repair note
or Q08 return for this item. This delivery leaves the stage-1 split unchanged.

Clause-by-clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The absolute value,
  valuation ring R, maximal ideal, chosen uniformizer, positive quotients and
  identity-induced transitions are exactly the recorded `Padic.coefficientExtension*`
  constructions. No independent ring, absolute value, uniformizer or map is supplied.
  Uniqueness of the extended absolute value makes the recorded spectral absolute value
  exactly the one in the statement; the definition node chooses one uniformizer.
- Nonarchimedeanness is `IsNonarchimedean (Padic.coefficientExtensionAbsoluteValue l E)`.
  Noetherianity, domain and DVR are the three following class propositions on the
  actual `Padic.coefficientExtensionIntegers l E`.
- The maximal ideal assertion is `(Ideal.span {Padic.coefficientExtensionUniformizer
  l E}).IsMaximal` and its equality to `Padic.coefficientExtensionMaximalIdeal l E`.
  Finiteness and characteristic of the residue field are `Finite` and `CharP ... l`
  on the recorded `Padic.coefficientExtensionResidueField l E`.
- The adic coefficient hypotheses are packaged as an existential
  `d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)` whose ideal
  equals the actual principal uniformizer ideal. All remaining fields of this
  structure are proofs: Noetherianity, finite generation, additive torsion of R/I,
  finite positive quotients and their ordinary-module perfectness. The existential
  cannot choose different coefficient data: its only non-proof field is fixed by
  the displayed equality. It is not used to define an arbitrary chosen object.
- The quantifiers `∀ n : ℕ, 1 ≤ n →` cover exactly the positive exponents, including
  n=1. `Finite (Padic.coefficientExtensionRing l E n)` asserts finite underlying set.
  `∀ x, l ^ n • x = 0` is annihilation by l^n as an additive group; it is equivalent
  to annihilation by the integer scalar in the quotient ring, without imposing
  the incorrect ramification restriction l=uniformizer.
- `Function.Surjective (Padic.coefficientExtensionTransition l E n)` uses the actual
  identity-induced homomorphism, not an arbitrary surjective map.
- `adicQuotientPerfect R (Ideal.span {uniformizer}) n` is the published predicate
  whose body is `DerivedCategory.IsPerfectRingComplex` of the quotient in degree zero.
  The named predicate installs the standard module-category localization internally.
- The resolution is a complex P, `P.IsStrictlyGE (-1)` and `P.IsStrictlyLE 0`, with
  `Module.Free R (P.X i)` and `Module.Finite R (P.X i)` for every i. The isomorphisms
  em and e0 identify the two surviving terms with R; the differential equation says
  exactly multiplication by the nth power of the recorded uniformizer.
- The map ε to the single quotient complex has its degree-zero component equal to
  the quotient map after e0, and all other components zero. An explicit derived
  isomorphism φ from `DerivedCategory.Q.obj P` to the single quotient object satisfies
  `DerivedCategory.Q.map ε = φ.hom`. Thus ε is the specified quasi-isomorphism and P
  is a finite free resolution. The derived form is retained as required by the
  2026-10-21 isomorphism convention, rather than only a per-degree cohomology claim.
- The second declaration uses the existing `pbcPadicCoefficientDatum l E`, which fixes
  precisely the same R and principal ideal and fills its proof fields by
  `pbcPadicCoefficientFacts`. Its completed sheaf on every `T : Scheme.{u}` is asserted
  equal to `limit (reductionCoefficientSystem T (pbcPadicCoefficientDatum l E))`.
  The system uses the recorded continuous-component-function sheafifications and
  the canonical quotient transition maps. Limits in this sheaf category have
  compatible-family sections; no discrete constant integral sheaf occurs.
- The integral category clause quantifies `[IsNoetherian T]`,
  `hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n`, and `hl : IsUnit (l : Γ(T, ⊤))`.
  These are exactly the hypotheses of the cited definition. It identifies the
  recorded `pbcBoundedConstructibleComplete T l E hdim hl` with the full subcategory
  of its recorded ambient `PbcCompletedDerived` defined by the conjunction of
  `PbcIsIntrinsicallyComplete`, `PbcHasUniformConstructibleReductions` and
  `PbcHasCompatibleEtaleOrigins`. In particular the common finite cohomological
  interval and compatibility of the etale witnesses are retained inside the
  published predicates; neither a per-level bound nor independent origins replaces them.
- The last two clauses say for every m≥0 that the ring at positive exponent m+1
  is `R ⧸ (pbcPadicCoefficientDatum l E).ideal ^ (m+1)` and that its transition is
  `reductionQuotientMap ... (m+1) m (Nat.le_succ m)`. This identifies the whole
  inverse sequence, including its maps. Longer maps are composites, already fixed
  in the recorded sequence functor. Index zero here is exponent one, not R/R.

Universes: the arithmetic theorem uses E in arbitrary Type u and makes no scheme
assumption. The scheme theorem uses T : Scheme.{u} and E : Type (u+1), exactly the
published unlifted coefficient convention of IntegralUniformCoefficient. No equality
between small-site object and morphism universes is imposed. Rings from smaller
universes may be viewed in the coefficient universe by cumulativity; the site remains
the recorded small pro-etale site. The coefficient sheaf assertion applies to every
scheme; geometric hypotheses occur only inside the integral-category clause.

Dependencies read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing` (recorded declaration), with its public
  `Sheaf.NumberTheory.Padics.CoefficientExtension` constructions
  `coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  `coefficientExtensionMaximalIdeal`, `coefficientExtensionResidueField`,
  `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`,
  `coefficientExtensionRing`, `coefficientExtensionTransition`. Full definitions,
  theorem signature and docstrings were read.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
  `DerivedCategory.IsPerfectRingComplex`, the exact recorded ring-perfect notion.
- `Sheaf.Paper.AdicCoefficientDatum`, recorded `Scheme.completedReductionTower`
  and its full signature and universal-pair docstrings; the statement uses
  `reductionCoefficientSystem`, `reductionQuotientMap` and the public
  `AdicCoefficientDatum` from `CompletedAdicCoefficientDatum`. The finite function
  coefficient construction, ringSystem and completedRing were read. The perfectness
  wrapper `Scheme.adicQuotientPerfect` is from `CompleteCoefficientDatum`.
- `Sheaf.Paper.IntegralUniformCoefficient`, recorded
  `Scheme.pbcBoundedConstructibleComplete`, and `pbcPadicCoefficientDatum`, with
  all its signatures and docstrings read. The reused three predicates and full
  subcategory are from its public `Sheaf.Paper.BoundedConstructibleComplete`.
- Proof imports: `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
  `Padic.extension_integers_dvr`; `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`,
  `AlgebraicGeometry.standard_quotients_perfect`; and
  `Mathlib.Topology.Algebra.Valued.LocallyCompact`,
  `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField`.
  Other proof dependencies are public transitively: `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
  (`spectralNorm_unique_field_norm_ext`, `spectralNorm_extends`,
  `isNonarchimedean_spectralNorm`, `spectralMulAlgNorm`),
  `Mathlib.RingTheory.Noetherian.Defs` (`IsNoetherianRing`), and the p-adic number
  and ideal quotient definitions. No new arithmetic specialization is necessary.

Edge cases checked before finalizing:

- n=1 is the residue quotient and gives the ordinary uniformizer resolution;
  m=0 in the second theorem is exactly this positive level.
- n=0 is excluded precisely where the node excludes it. No empty positive tower occurs.
- E=Q_l recovers Z_l and its familiar finite quotients.
- In ramified extensions l need only be divisible by the uniformizer. Then l^n is
  divisible by the nth uniformizer power, so the stated annihilation remains true;
  the false equality (l)=(uniformizer) is never assumed.
- R is a subring of a field, its maximal ideal is proper, and its residue is nonzero.
  The primality binder excludes l=0 and l=1 and makes CharP ... l the intended prime.
- The empty scheme is allowed for the completed sheaf and the category; finite
  dimensionality is expressed by an upper bound on topologicalKrullDim.
- The common finite interval and compatible etale origins are inherited unchanged.
- No coefficient comparison identifies the completed ring with a discrete integral
  constant sheaf, and no extra scheme hypothesis restricts the ring assertion.

Searches actually run on 2026-10-22:

- msearch leanfinder: "The valuation ring of a finite extension of the l-adic numbers
  has finite perfect torsion quotients and forms an adic coefficient datum" returned
  eight hits (finite-place valuation-ring constructions, Tilt, BDeRham and p-adic
  completeness). None states this joint resolution/completed-domain assertion.
- msearch loogle: "IsDiscreteValuationRing, IsNoetherianRing" returned two hits:
  `IsLocalRing.finrank_CotangentSpace_eq_one_iff` and `IsDiscreteValuationRing.TFAE`.
  These are characterizations and do not state the package coefficient domain.
- msearch grep: "finite_quotient_maximalIdeal_pow_of_finite_residueField|
  isNonarchimedean_spectralNorm" returned eight hits. The relevant two declarations
  were read at Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:111 and
  Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:645; each supplies only one clause.
- msearch leansearch: "The integers of a finite p-adic extension form a Noetherian
  discrete valuation ring with finite perfect torsion quotients" returned eight hits,
  including p-adic integer/local-field DVR instances, with no whole-item match.
- rg in lean/WeilConjectures and lean/Sheaf for the exact blueprint id and for
  `adic_ring_domain|adicRingDomain` found no existing declaration of this item.
  The subsequent search for the two proposed full-name stems in Mathlib and
  dag/lean_names_upstream.json also found none.
- rg for coefficientExtension and AdicCoefficientDatum found the reused published
  definitions and the already stated ring-facts theorem `pbcPadicCoefficientFacts`.
  That theorem supplies the proof fields of the datum but does not include residue
  characteristic, the l^n annihilator, canonical transition surjectivity, the specified
  resolution or the completed-domain/reindexing clauses, so it is not an exact match.

The blueprint package proof Clause (4), the complete node proof, all statement
prerequisites and their recorded declarations were read. No statement correction or
STATEMENT-DISPUTED fault is needed. No definition was duplicated.

Validation: scompile.py compiled this file separately as sandbox and library module
against the live published build, cleanly (final pass: 3.0 s and 2.7 s). Every theorem
proof is exactly `by sorry`, all universes and variables are explicit, and line lengths
are at most 100. The prescribed dry run and delivery follow this report.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
