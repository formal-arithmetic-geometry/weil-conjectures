## Worker report

The item is stated by `WeilConjectures.PointScalarTransfer.scalar_compatible_transport_transfer`
in `Sheaf.Paper.PointScalarCompatibleTransportTransfer`. Its proof is `sorry`.
The definitions contain actual data, exclusively recorded restrictions, applications,
coefficient unliftings, tensor functors, or composites of specified maps.
The accepted statement and seven-step proof are unchanged. The theorem docstring
contains all seven steps verbatim, with line wrapping. No statement dispute or correction.

The inherited BLOCKED ending concerned stage-1 resplitting. The current
brief-stage2 §0 explicitly distinguishes that from this authorized stage-2 statement.
The live item has an accepted split but no Lean record. This delivery preserves the split.

The returned-delivery repair imports the existing prime-unit theorem and canonical
restriction transformations from `Sheaf.Paper.PointAutomorphismTransportScalarExtension`.
No second theorem or definition of those notions remains. The dependency node
`lem-weil-point-automorphism-restriction-natural` retains its landed record.

Hypotheses and objects, in the order of the node:

- `D : FiniteFieldDatum.{u}` supplies p, a>=1, q=p^a, k_0 and its fixed algebraic
  closure k. `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give the coefficient prime.
  `Q : Type u`, `[Field Q]`, `[Algebra ℚ_[l] Q]`, `[IsAlgClosure ℚ_[l] Q]` give the
  fixed coefficient closure. The algebraic-closure and J-linearity instances are
  explicitly included in the theorem's section variables.
- `g : Spec (.of D.k) ⟶ Spec (.of D.k)` with `[IsIso g]` is an arbitrary scheme
  automorphism, with no k_0-linearity restriction. The recorded completed module
  categories use `Scheme.ProEt.topology`, with site objects in Type (u+1) and
  morphisms in Type u, and module carriers in Type (u+1).
- Each `F : Padic.FiniteCoefficientFields l Q` is a finite subextension of the
  fixed closure. Its valuation ring and uniformizer are precisely
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`.
  Coefficients are the inverse-limit completed ring sheaf, not a discrete constant
  integral sheaf. `Integral` abbreviates `sfIntegralConstructibleCategory`, the
  currently recorded category for def-weil-derived-complete-integral-detailed.
  Its predicate includes completeness and a common interval for all reductions.
- `inverseImage` is the full-subcategory lift of `inverseImageIntegralDerived`.
  Its preservation proof projects `isomorphismComparisonInputs_constructible`;
  prime invertibility is supplied by the finite-field hypotheses. No completeness
  or constructibility hypothesis is added beyond membership in `Integral`.
- `sections` is the inclusion followed by `pointCompletedDerivedSections`, i.e.
  exact termwise final-object sections with the recorded constant-scalar action.
  `Modules` and `Fields` are the corresponding module/field derived categories.
- `J F : Integral F ⥤ Integral F`, with `(J F).Linear O_F`, is exactly the family
  of linear endofunctors in the statement. `extension` is the recorded completed
  integral scalar extension restricted to the constructible category.
- `phi`, `unit`, and `assoc` apply `pointSectionsScalarExtensionIso`,
  `pointIntegralScalarUnit`, and `pointIntegralScalarAssoc`, using
  `pointIntegralConstructible_iff` to pass the equivalent admissibility predicate.
  `tensor`, `moduleUnit`, and `moduleAssoc` use the recorded ordinary integral
  module tensor and coefficient-multiplication unit and associator.
- `beta` is precisely chi_X^{-1}, then the specified inverse-image tensor iso,
  then G_L(chi_Y), packaged by `isoMk` in the full subcategory. This retains the
  comparison of lem-weil-isomorphism-comparison-scalar-extension, not an arbitrary iso.
- `δ E L h : J E ⋙ extension E L h ≅ extension E L h ⋙ J L` supplies natural
  comparison isomorphisms. `hδunit` states the unit equation after multiplication
  identifications. `hδtower` states the given tower equality with the specified A.
- `u F H` is an object-indexed morphism G_F H → J_F H. It is not a natural
  transformation. `hu` is T(u_E) ≫ δ = beta ≫ u_L. `hσ` is sigma_L followed by
  Gamma(beta^{-1}) and phi at G_E H, equal to phi_H followed by tensor(sigma_E).
  `sigma` applies the existing `pointAutomorphismRestrictionDerived`, localized from
  the recorded sectionwise restriction theorem.

Conclusions (the conjunctions of the theorem, in order):

1. `v = sigma ≫ sections.map u` and `zeta = sections.map δ.inv ≫ phi.hom` are
   definitions, with the composition order equivalent to the node's right-to-left
   notation. The first conjunct is v_L ≫ zeta = phi ≫ tensor(v_E).
2. The second conjunct states zeta's identity-extension equation with module
   multiplication on the target and J of the integral unit on the source.
3. The third conjunct states zeta's tower with Gamma(J_M A), tensor(zeta), and
   the specified `moduleAssoc`, in precisely that order.
4. `rationalize` is `coefficientComplexRationalize.mapDerivedCategory`,
   `fieldTensor` is the corresponding field tensor functor, and `rho` is exactly
   `coefficientComplexDerivedBeta`. Its documented normalized value is
   ((n tensor a) tensor b) ↦ ((n tensor 1) tensor ab). `rationalPhi` and
   `rationalZeta` are q_L of the integral arrow followed by this rho. The fourth
   conjunct is the specified rational transport square in D(L).
5. The fifth conjunct states compatibility of v with the identity-extension unit.
6. The sixth states compatibility of v with A, derived from the square rather
   than assumed as naturality of v.
7. The seventh gives the actual pasted integral transport equation across a tower.
8. The eighth gives the rational target unit under `fieldUnit`.
9. The ninth gives the rational target tower under `fieldAssoc`.
10. The tenth gives the actual pasted rational transport equation, using q_M(A).
    Together with the imported unit/tower equations for phi and the mixed rho
    tower these render the identity/successive-extension compatibility stipulated
    in the node. No extra coherence datum is quantified or assumed.
11. The final existential supplies additive functors S and SJ on `Raw`, which is
    literally `sfRationalConstructibleCategory` (raw scalar localization, with no
    Karoubi completion). Their object values are q_F Gamma(H) and q_F Gamma(JH).
    The two HEq formulas fix their values on a tensor f for every localized scalar
    a, through `sfRationalCoefficientEquiv`; additivity fixes all finite sums.
    Hence denominators and torsion in integral Hom groups cause no restriction.
    Φ and Ζ are natural isomorphisms for the recorded `sfRationalScalarExtension`,
    with components exactly rationalPhi and rationalZeta. Naturality therefore
    quantifies all raw morphisms, including fractions, not just integral arrows.
    HEq is used only to express equal values whose endpoint objects have the
    preceding explicit object equalities. Neither u nor v is made natural.

Dependency declarations used (all recorded modules are directly imported):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `Scheme.ProEt.topology`. The scheme-morphism-properties node is a convention;
  `Spec`, scheme morphisms, and `IsIso` are the existing categorical constructions.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  construction imports: `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the completed coefficient sheaf.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` and its public imports:
  `AlgebraicGeometry.ProEtale.inverseImageIntegralDerived` and coefficient transport.
- `Sheaf.Paper.PointProEtaleSectionsExactOfUniverses`:
  `point_proEtale_sections_exact_of_universes`; the supplied sections specialization
  is `pointCompletedDerivedSections` from `PointSectionsScalarExtension`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`;
  at the common universe the imported `sfConstructibleIntegralScalarExtension`
  restricts the same normalized strict-tower construction.
- `Sheaf.Paper.PointSectionsScalarExtension`: `pointIntegralConstructible_iff`,
  `pointSectionsScalarExtensionIso`, `pointIntegralScalarUnit`,
  `pointIntegralScalarAssoc`, `pointIntegralModuleDerivedTensor`,
  `pointIntegralModuleDerivedUnit`, `pointIntegralModuleDerivedAssoc`, and
  `pointSectionsScalarExtension` (naturality/unit/tower proof plan).
- `Sheaf.Paper.IsomorphismComparisonScalarExtension`:
  `isomorphismComparisonInputs_constructible`, `isomorphismScalarTensorDerived`,
  `scalarCompletionIso`; their composite is `isomorphismComparisonScalarBeta`.
- `Sheaf.Paper.IsomorphismDerivedPullback`:
  `isomorphismIntegralDerivedPullback_termwise` supplies the preservation plan.
- `Sheaf.Paper.PointAutomorphismRestrictionNatural`: `point_automorphism_restriction_natural`
  and its coefficient, sections, and inverse-image constructions.
- `Sheaf.Paper.PointAutomorphismTransportScalarExtension`:
  `pointTransportPrimeUnits` supplies stalkwise prime invertibility;
  `pointAutomorphismRestrictionDerived` supplies the canonical derived restriction,
  built from `pointAutomorphismRestrictionModules`. These existing declarations are
  used directly, with no copies.
- `Sheaf.Paper.CoefficientComplexRationalization`:
  `coefficientComplexRationalize`, `coefficientComplexFieldTensor`,
  `coefficientComplexDerivedBeta`, `coefficientComplexDerivedFieldUnit`,
  `coefficientComplexDerivedFieldAssoc`, `coefficientComplexRationalization`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalScalarExtension`, `sfRationalCoefficientEquiv`.
- `Sheaf.Paper.SfIntegralConstructibleLinear`: the inherited O_F-linear action.
- Proof-only `Sheaf.CategoryTheory.SemilinearScalarLocalization`:
  `CategoryTheory.ScalarLocalization.existsUnique_semilinear_extension`,
  `extensionNatIso`, `extensionNatTrans_laws`, and whiskering laws.

Edge cases checked against the signatures: E=L and repeated fields in a tower are
included via non-strict ≤; multiplication/completeness units are written explicitly.
The zero object, zero u, and zero maps are allowed. g=id and J=id need no special
hypotheses. g need not descend to k_0. u may be non-natural: only its scalar square
is assumed, and its needed compatibility with A is a conclusion. Sections and rho
accept arbitrary derived arrows; no representative as a chain map is required.
The rational clauses allow arbitrary denominators and finite sums, even if integral
Hom groups have torsion. No idempotent splitting or condition on torsion is imposed.
The site has its genuine object/morphism universe difference; no equality is forced.

Searches: `msearch.py leanfinder` for "Scalar compatible comparison morphisms transfer
point section transport squares and coefficient rationalization" returned generic
presieve compatibility / scalar-map hits, none with this statement.
`msearch.py loogle` for `"NatTrans.naturality"` returned naturality and its variants,
which do not state transport of object-indexed families through completed sections.
`msearch.py grep` for `transport.*(rationaliz|[Ss]calar)|[Ss]calar.*transport` in
Mathlib/Algebra/Category/ModuleCat returned zero matches. `rg` of the live
WeilConjectures and Sheaf sources for scalar/transport combinations found the
specific point-automorphism transport theorem but no theorem with arbitrary J,u.
The exact blueprint-id grep of WeilConjectures returned no match. The earlier
sandbox searches.jsonl contains these searches as well; they were rerun here.

Validation: all compilation uses scompile.py under the fixed 60-second per-file
limit. The inherited maxHeartbeats=12000 probe failed during theorem elaboration;
removing that artificially small diagnostic setting and using the library's
`respectTransparency=false` option yields clean statement compilation. After the
returned-delivery repair, the single item module uses the existing helpers and is
validated against the live server sources.

## Dependency modules

None. The returned-delivery repair removed the temporary dependency module
`Sheaf.Paper.PointRestrictionIntegralDerived` and restored the dependency node's landed
record unchanged. The canonical sectionwise restriction theorem is imported directly;
the existing prime-unit theorem and its module/derived restriction constructions are
imported from `Sheaf.Paper.PointAutomorphismTransportScalarExtension`.


## Returned-delivery repair

The immutable returned head was `f0a8b824f2a3`. The retained packet was first dry-run
against current live sources: it passed mechanically as `f376a705ba8`, but still
contained the duplicate named by the maintainer. The repair removes
`WeilConjectures.pointRestrictionPrimeUnits` and uses the existing
`WeilConjectures.pointTransportPrimeUnits` instead. Its explicit section binders are
`D : FiniteFieldDatum.{u}`, `l : ℕ`, `[Fact l.Prime]`; its explicit theorem binder is
`_hl : l ≠ D.p`. Both old and existing declarations conclude
`∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x)`.
No different variables or open namespaces change those types.

The same source inspection found the two local restriction definitions to be
identical to `pointAutomorphismRestrictionModules` and
`pointAutomorphismRestrictionDerived`, so their copies were removed as well.
`sigma` applies the existing derived transformation directly. The item Lean record
no longer lists any of the three removed declarations. The main theorem signature,
the informal statement, proof, dependencies, and edge cases are unchanged.

The repair search used `rg -n` on the live `lean/WeilConjectures` and `lean/Sheaf`
for all three local helper names and `pointTransportPrimeUnits`; the existing module
was read with its full binders and docstrings, and checked against current server
source with `scompile.py --source Sheaf.Paper.PointAutomorphismTransportScalarExtension`.
The two definitions have the same scalar-unlifting and localization composites,
not merely isomorphic endpoints. No statement correction or new node is needed.

Repair self-check: the theorem signature is verbatim equal to `lean.statement`;
all non-`lean` fields agree with the current node; the declaration list exactly
matches the remaining declarations in source order; every line is at most 100
columns; precisely one `sorry` remains, belonging to the main theorem. The four
prime-unit applications and the derived restriction application use the existing
names. `scompile.py` completed with exit 0 and no diagnostics for both the sandbox
and library module (44.2 s and 27.8 s respectively, each within the 60 s limit).

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (stage-2 reviewer, 2026-10-23)

The repair above imported `Sheaf.Paper.PointAutomorphismTransportScalarExtension`. That is the
module of lem-weil-point-automorphism-transport-scalar-extension, whose `proof_deps` contain this
item. When that node's stage-3 proof imports this module (stages/2-statements.md §7), the two
modules would form an import cycle, so that proof could not use this lemma (delivery-errors C6).

The fix removes that import and restores the local helpers of the previously reviewed head
f0a8b824:
- `pointRestrictionIntegralModules` and `pointRestrictionIntegralDerived`. Their bodies are
  identical to the downstream `pointAutomorphismRestrictionModules/Derived`, which can become
  aliases of these at stage 3.
- `pointRestrictionPrimeUnits`, now stated for every field `K` over `k₀` and applied at
  `K = k`. This is a genuine generalisation, not a word-for-word duplicate of
  `pointTransportPrimeUnits`.

The main theorem and every other declaration are unchanged. The fixed file compiles clean with
nt_compile.py in 40.2 s.

