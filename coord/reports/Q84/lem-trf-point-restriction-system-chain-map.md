## Worker report

The module `Sheaf.Paper.PointRestrictionSystemChainMap` states the strict-system
restriction/insertion construction for every automorphism of the geometric point.
Its main declaration is
`WeilConjectures.PointRestrictionSystem.restriction_system_chain_map`.
All four theorem proofs are `sorry`; all definition data are real constructions.
The auxiliary continuity, coefficient-assembly and additivity statements express
parts of the same specified inverse-image/chain-map construction. Each has the
item's blueprint annotation and a complete proof plan. There are no new DAG nodes,
no dependency-record repairs and no statement correction.

Hypotheses and notation, matched individually:

- The finite-field datum, finite base field and its algebraic closure are
  `D : FiniteFieldDatum.{t}`; the point is `Spec (.of D.k)`.
- The prime and characteristic condition are `(l : ℕ) [Fact l.Prime]` and
  `(_hl : l ≠ D.p)` in the main theorem.
- The finite extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The recorded
  `Padic.coefficientExtensionIntegers` and `coefficientExtensionRing` provide R
  and its quotient rings. Their ideals are maximal-ideal powers, equivalently
  powers of a uniformizer; no property here depends on the chosen generator.
- The automorphism is `(g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]`.
  There is no assumption that it is over the finite base field.
- The small site is `ProEt.topology (Spec (.of D.k))`, using `Scheme.ProEt`.
  It keeps object universe t+1 and morphism universe t. Coefficients and modules
  have universe `max u (t+1)`; t and u are independent.
- The finite B_n, quotient maps, completion and projections are the recorded
  `integralCoefficientSheaf`, `coefficientSequenceCommRingTransition`,
  `completedIntegralCoefficientSheafUnrestricted` and its limit projections.
  `pointRestrictionRing ... (some n)` is exactly the finite ring sheaf.
  Index `n : ℕ` denotes the source's positive exponent n+1, including exponent 1.
- The strict category is the existing `coefficientSequenceModules`. It consists
  of module sheaves over B_bullet on the vertical sequence site. Its horizontal
  restrictions are precisely quotient-linear transitions, and its morphisms are
  the compatible component maps. `sequenceRing` only forgets commutativity of
  the existing coefficient sequence sheaf. No second system category is defined.
- `reindex D g` applies `proEtaleIsoPostcompose g` at every level. The theorem
  `coefficient_existsUnique` specifies the section components to be exactly
  `inv (pointRestrictionCoefficientMap ... (some n))`, with uniqueness over all
  components. `coefficient` chooses this uniquely determined morphism, not a map
  from an unrestricted existence assertion. `pull` is Mathlib's actual
  `SheafOfModules.pushforward` along that reindexing with that coefficient map.
  Thus it is F on every level with c_n inverse action, retaining all transitions.
- `sections` is the existing coefficient restriction followed by levelwise
  `pointRestrictionSections ... none`. Restriction first along pi_n and then
  along the constant R-to-completion map equals restriction along R-to-A_n, by
  `integralConstantConeOfUniverses` and its actual quotient legs. No limit of
  the input system is taken. The target is `ℕᵒᵖ ⥤ ModuleCat R` with the canonical
  universe lift of R already used by the recorded coefficient tower operations.
- Unbounded complexes are `CochainComplex ... ℤ`. `complexSections` and
  `transportedComplexSections` use `mapHomologicalComplex (ComplexShape.up ℤ)`.
  The auxiliary `operations_additive` supplies their zero-morphism preservation
  from pointwise additivity, with no new hypothesis on systems.

Conclusions, matched clause by clause:

1. U is `ProEt.mk (𝟙 (Spec (.of D.k)))`. V is its image under
   `proEtaleIsoPostcompose g`; `pointRestrictionArrow g` is the arrow V to U
   with underlying scheme map g.
2. The degreewise, levelwise recipe is the right side of
   `HasRestrictionComponents`: the actual presheaf restriction along
   `Prod.mkHom (𝟙 n) (pointRestrictionArrow g)`. The recorded
   `pointRestrictionRaw` defines the same restriction followed by colimit
   insertion and sheafification in canonical reindexing coordinates. The
   single-level dependency identifies that insertion with identity; it is not
   replaced by an arbitrary linear map.
3. The first conjunct of `restriction_system_chain_map` explicitly asserts
   A_n-linearity for every module sheaf and every scalar b and section x.
   The target scalar multiplication is on the module returned by
   `pointRestrictionInverseImage`, hence uses c_n inverse, as required.
   R-linearity is also built into every component of the ModuleCat-valued
   tower morphisms in its second conjunct.
4. The strict transition identity is built into the inner natural
   transformation `((u.app M).f i)`, a morphism of towers. Its naturality at
   `(homOfLE (Nat.le_succ n)).op` is exactly the stated quotient-transition
   square. The sections functor retains the original transitions, and `pull`
   transports their actual maps by reindexing. This is before localization.
5. The second conjunct is `∃! u : complexSections ... ⟶
   transportedComplexSections ..., HasRestrictionComponents ... u`.
   A component `u.app M` is a chain map of whole strict towers. Its defining
   `HomologicalComplex.Hom.comm` is the differential compatibility equation.
   The predicate prescribes every i,n section component. HEq compares only
   the unchanged section carriers, accommodating the equality casts in the
   existing coefficient restriction definition; it imposes actual equality
   of the component functions, not existence of an unspecified comparison.
6. For every system chain map f the outer `NatTrans.naturality f` gives
   Gamma(f) followed by u_M' equals u_M followed by Gamma(Gf), exactly the
   node's displayed equality with categorical composition order reversed.
   Uniqueness is stated for the entire natural transformation; componentwise
   prescribed values also give the requested uniqueness for each input M.
7. The input is every strict system complex. There are no normalization,
   cartesianness, flatness, surjectivity, boundedness, constructibility, Tor
   amplitude or completeness assumptions.

Dependency declarations read and used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, and its public finite
  field/coefficient conventions. The point lemma uses the underlying
  `FiniteFieldDatum` and finite coefficient extension directly; no auxiliary
  separated finite-type X_0 is required for this point-system statement.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
  The scheme-properties dependency is a convention node with no declaration.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, `integralConstantConeOfUniverses`,
  and the retained completed coefficient sheaves and quotient maps.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` and its publicly retained
  `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageFiniteCoefficientMap` and the canonical coefficient comparisons.
  No derived pullback or comparison is substituted for the strict inverse image.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearSections.Systems` and the
  description of the same vertical sequence-site category as arbitrary strict
  semilinear systems. The concrete DVR sequence specialization is the existing
  coefficient-sequence module category, not a private implementation of it.
- `Sheaf.Paper.CoefTowerCoaugmentation`: the ordinary R-module tower convention
  (`CoefTower.coefficient`, `CoefTower.towerSections`). The direct composite
  here uses the existing independent-universe point sections, rather than
  restricting E to the scheme universe as the older abbreviations do.
- `Sheaf.Paper.PointAutomorphismRestrictionNatural`:
  `pointRestrictionScalars`, `pointRestrictionRing`,
  `pointRestrictionCoefficientMap`, `pointRestrictionScalarAt`,
  `pointRestrictionSections`, `pointRestrictionInverseImage`,
  `pointRestrictionArrow`, `pointRestrictionRaw`, and
  `point_automorphism_restriction_natural`. Their full signatures and relevant
  definition bodies/docstrings were read.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: the recorded unbounded
  complex/derived conventions. This result itself takes place on complexes.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `proEtaleIsoPostcompose_isContinuous`, `isoSectionwiseInverseImage`,
  `isoSectionwiseConstantMap` and `isoSectionwiseModuleInverseImage`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (the actual unchanged-section construction).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `coefficientSequenceTopology`, `coefficientSequenceCommRingSheaf`,
  `coefficientSequenceModules`, `coefficientSequenceRestriction` and its unique
  unchanged-section/transition specification. Its already-landed definition node
  `def-coef-ringed-sequence-site` is added to stmt_deps to cite this existing
  concrete realization. It adds no hypothesis and changes no statement text.

Edge cases checked against the statement and constructions: g=id (allowed by
IsIso without a positive-power restriction); exponent 1 (n=0); zero systems and
zero transitions; non-surjective transitions; non-flat quotient maps; unrelated
modules at adjacent levels; differentials in every integer degree, with no lower
or upper bound; arbitrary system chain maps; either ordering of the independent
site and coefficient universes. The restriction/naturality calculation works in
all these cases. No statement dispute or source fault was found.

Searches actually run (the msearch entries are in searches.jsonl in the sandbox):

- LeanFinder: "Restriction along an automorphism gives a natural chain map on
  towers of sheaves of modules commuting with quotient-linear transition maps".
  Eight hits, including SheafOfModules.restrictScalars and its component lemmas;
  these supply scalar restriction, not the claimed whole-system transformation.
- Loogle: "PresheafOfModules.restriction,
  CategoryTheory.NatTrans.mapHomologicalComplex". Zero hits.
- Mathlib grep through msearch: "natTransΓRes|semilinear.*(system|transition)|
  restriction.*colimit". Four hits; GlobalSections.natTransΓRes concerns ordinary
  section restriction and is not the arbitrary quotient-system theorem.
- LeanSearch: "A site automorphism induces a natural linear chain transformation
  on strict inverse systems of module sheaves". Eight hits, notably
  SheafOfModules.pushforwardNatTrans and pushforwardNatTrans_app_val_app.
  These are relevant ingredients, not this whole varying-coefficient statement.
- rg in lean/WeilConjectures and lean/Sheaf for pointRestrictionRaw, restriction
  with system/tower, and the item id; rg in dag/lean_names_upstream.json for the
  proposed names; `tools/lean_names_upstream.py show` for the item. No upstream
  exact match. The existing PointSystemTransport.chainTransport_existsUnique
  covers only positive powers of the specified Frobenius, so cannot record this
  arbitrary-automorphism statement as existing. Its strict-system construction
  was read to confirm reuse of the same coefficient-sequence primitives.

Validation: scompile.py compiled the sandbox probe and the delivered library
module successfully (exit 0), with no errors or warnings. All theorem proofs
remain sorry; explicit universes and autoImplicit=false are retained.

## Return repair H2

The immutable returned head was `dbfcfa3b1966`. Its reported defect is repaired
by adding the already-landed definition node
`def-trf-point-restriction-coordinates` to the item's `stmt_deps`, and naming it
in `lean.note`. Its `existing: true` record owns
`AlgebraicGeometry.ProEtale.pointRestrictionScalars`, `pointRestrictionRing`,
`pointRestrictionCoefficientMap`, `pointRestrictionScalarAt`,
`pointRestrictionSections`, `pointRestrictionInverseImage`,
`pointRestrictionArrow`, and `pointRestrictionRaw` in
`Sheaf.Paper.PointAutomorphismRestrictionNatural`. I read the live definition
node and these declarations' full signatures, bodies and docstrings; they are
the coordinates used by the saved module. The site reindexing construction is
also covered by this definition node. The theorem dependency
`lem-weil-point-automorphism-restriction-natural` is retained because the node's
text explicitly cites its restriction/insertion map sigma.

This is a definition-ownership repair only: the Lean module, statement text,
proof and proof dependencies are unchanged. Relative to the current read clone,
the packet changes only `lean` and the two landed definition dependencies
`def-coef-ringed-sequence-site` and
`def-trf-point-restriction-coordinates`. No dependency module or new node is
added. The maintainer's mathematical reading of the returned head remains
applicable clause by clause, including identity automorphisms, n=0, arbitrary
transitions, all integer degrees and independent universes. The unused-import
and future helper-ownership observations were advisories, not requested Lean
changes.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
