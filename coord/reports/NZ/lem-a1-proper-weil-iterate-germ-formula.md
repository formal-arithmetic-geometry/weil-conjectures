## Worker report

Stage 2 statement delivery for `lem-a1-proper-weil-iterate-germ-formula`.
The new module is `Sheaf.Paper.ProperWeilIterateGermFormula`, namespace
`WeilConjectures.ProperWeilIterateGerms`. Nothing is proved. The three named
postponed statements are `rational`, `global_eq`, and `commonStage`; each belongs
to this node and has a source and natural-language proof docstring. The remaining
five declarations contain actual composites or a transparent proposition, never
postponed data. This repair adds definition ownership and citations as detailed below; all mathematical signatures remain unchanged.

Hypotheses and objects, clause by clause:

- The finite-field tuple is the existing `D : FiniteFieldDatum.{u}`. Its fields
  give p prime, a positive, q=p^a, a finite field of cardinality q, and its fixed
  algebraic closure. There is no new copy of this datum.
- `Y₀ : Over (Spec (.of D.k₀))` with `[IsProper Y₀.hom]` is precisely a proper
  finite-type model. Mathlib properness supplies locally finite type,
  quasi-compactness and separatedness. No finite-morphism assumption is present.
- The scheme Y and s are `(D.geometricFiber Y₀).left` and `Spec (.of D.k)`;
  the structure map is `(D.geometricFiber Y₀).hom`.
- `l : ℕ`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]` give the required prime and
  distinct characteristic. Prime invertibility is supplied by the recorded
  dependency instances, not added as an independent hypothesis.
- Rational coefficients are any `E : Type u` with `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. This is the E case of
  the rational/common-stage alternatives. The unused choice of embedding E
  into a chosen closure is not mathematical input to the rational equation;
  `global_eq` explicitly specializes to the recorded finite-subfield datum
  `c : D.CoefficientDatum` and `F : Padic.FiniteCoefficientFields c.l c.Qbar`.
- Common-stage coefficients are arbitrary `Ω : Type v` with `[Field Ω]`,
  `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`. The coefficient universe v
  is independent of scheme universe u. All realizations use the published
  coefficient extension into modules in `max u v`.
- `K : sfWeilComplex ... E` and `sfCommonStageWeilComplex ... Ω` are the
  recorded categories of fixed pairs. Their carriers already lie in bounded
  constructible categories; their `str` is an actual rational/common-stage
  isomorphism. No heart, integral Weil lattice, weight, or semisimplicity
  hypothesis occurs.
- The point `z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left` and
  `hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _` express exactly a k-point.
- Every index `n : ℕ` denotes exponent `n+1`, following the recorded
  `localPositivePower`, `localWeilIterate`, `localPointTransportIterate`,
  `ProperSemilinearGerms.movingPoint`, and `rationalTransport` interfaces.
  Thus every r≥1 occurs, and index zero is exponent one, not a missing case.

Conclusions and specified constructions:

1. `global` is the existing compact transport component followed by C of the
   Weil map, with C=`ProperSemilinearGerms.rationalSections` at the identity
   compactification. It is explicitly typed as an endomorphism. `global_eq`
   identifies it with component 2 of the recorded `globalGeometricFrobenius`.
2. `contractedGlobal` is `rationalTransport ... K.carrier n` followed by C of
   `localWeilIterate ... K n`. The existing recursion for `rationalTransport`
   is the repeated compact transport with the inverse scalar-localized
   compositor at the end, so this is exactly tau^[r] then C(theta^[r]).
   Conjunct 1 of `rational` is `global ^ (n+1) = contractedGlobal`.
3. `block` is exactly the three displayed factors in Lean composition order:
   `localPointTransportIterate` on the moving-point pullback, point fibre of
   `rationalSquare`, then `rationalFibre z` of `localWeilIterate.hom`.
   The square is the canonical comparison of the equality
   h^r ≫ z_r = z ≫ g^r, supplied by `movingPoint_properties`. The moving
   point is the recorded h^(-r) ≫ z ≫ g^r, so there is no fixed-point
   assumption in the definition or germ formula.
4. `rational` conjunct 2 is `F^r ≫ e_z = e_(z_r) ≫ B`, the two sides of
   the node's second displayed equation written with Lean's left-to-right
   composition. Both germs are the actual `rationalGerm` of the dependency,
   constructed using the whole-system adjunction counit and proper comparison.
5. Conjunct 3 is `IsIso (block ...)`. Conjunct 4 quantifies over every
   `f : K ⟶ L`, and equates `B_K ≫ U_z` with `U_(z_r) ≫ B_L`.
   There is no `[IsIso f]` restriction; zero and noninvertible arrows occur.
6. Conjunct 5 assumes exactly `hfix : movingPoint ... = z`, asserts the return
   equality, and identifies the block (with its source transported by
   `eqToHom (congrArg ... hfix).symm`) with `localFrobeniusOperator` for every
   proof of that return. This handles the actual semilinear return,
   never the generally incorrect equality g^r z=z of scheme morphisms.
7. Conjunct 6 quantifies over closed points y, residue embeddings ι and their
   k₀-compatibility hι, a point identification with `localClosedPoint`, and
   the return at `localClosedPointDegree ... - 1`. Its equality is `HEq` to
   `localClosedFrobenius`, solely because its endpoints are transported along
   the point identification. The positive degree is supplied by the dependency;
   degree 1 therefore gives index 0 and is included.
8. `realizedFormulas` writes all six preceding conclusions after the exact
   `ProperSemilinearGerms.stageRealization` functor, including invertibility,
   arbitrary-morphism naturality, fixed-point return, and the closed-point
   clause. This is a transparent Prop with every equality spelled out.
9. `commonStage` asserts these formulas at EVERY finite field F, not just an
   arbitrary chosen model. It also asserts finite Weil models for EVERY
   common-stage pair, and simultaneous finite Weil models for EVERY arrow,
   with the underlying represented-arrow equation explicitly stated. Thus
   this includes morphisms represented at fields larger than either original
   object stage and noninvertible arrows. The models have rational isomorphisms,
   not invariant integral Weil structures.
10. `modelSectionsComparison` is canonical: inverse of the published literal-stage
    object equality, followed by C of the underlying supplied Weil-model
    isomorphism. The last conjunct of `commonStage` says this actual comparison
    intertwines F^r with the scalar-extended rational F^r, for EVERY model and
    every isomorphism to the common-stage pair. Identity extensions and further
    fields are included. The germ and block formulas are expressed in these
    finite-model coordinates, as in the dependency's faithful-realization
    convention; they retain the specified germ and all three block factors.
11. Every equality is between derived arrows. No cohomology, trace, eigenvalue,
    weight, or semisimplicity operation is used in any conclusion.

Dependency declarations read and reused (the direct imports also include every
recorded module of the statement and proof dependencies):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`,
  `CoefficientDatum`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart` and the rational/common-stage
  constructible categories used by the fixed-pair interface. No heart restriction
  is imposed on the complexes in this node.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfCommonStageWeilComplex`,
  `sfWeilPrimeInvertible`, `sfWeilStageObject`, `sfCommonStageWeilForget`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback` and the
  common-stage pullback used by the fixed-pair categories.
- `Sheaf.Paper.IntegralPullbackComposition`: `integralPullbackComposition`,
  through `localPullbackComposition` and the existing germ/transport recursions.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`: the recorded compact-cohomology
  construction; the present derived C is its published Frobenius/coefficient
  realization `frobeniusCohomologyRationalFunctor` at the identity compactification.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`: `frobeniusCohomologyTransportRational`.
- `Sheaf.Paper.GlobalGeometricFrobenius`: `globalGeometricFrobenius`,
  `globalGeometricFrobeniusQbar`.
- `Sheaf.Paper.ProperSectionsSemilinearGerms`: `ProperSemilinearGerms.rationalGerm`,
  `.movingPoint`, `.movingPoint_properties`, `.rationalSquare`, `.rationalSections`,
  `.rationalFibre`, `.rationalTransport`, `.stageRealization`, and
  `properSectionsSemilinearGermsRational` / `properSectionsSemilinearGerms`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre` and its scalar comparisons.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`, `localWeilIterate`,
  `localPointTransportIterate`, `localFrobeniusOperator`, `localClosedPoint`,
  `localClosedPointDegree`, `localClosedFrobenius`.
- `Sheaf.CategoryTheory.NaturalTransportPowers`: `NaturalTransport.inducedEndomorphism_pow`.
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`: the published adjunction
  interface used by the germ dependency.
- `Sheaf.Paper.ProperCoincidenceFrobenius`: `properFrobeniusRationalFunctor`,
  `properFrobeniusRationalIso`, `properCoincidenceFrobenius`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`: the published actual
  cohomology functors, `frobeniusCohomologyQbarSourceEq`,
  `frobeniusCohomologyTransport_isIso`, and canonical scalar/realization comparisons.
- `Sheaf.SixFunctors.FrobeniusPointTransportNatural`: `frobeniusPointTransport_natural`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the actual common-stage Pair
  category, `inclusion`, finite stage and representative conventions.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`: `basicOperationsCoefficientReduction`.

Edge cases checked before and during writing: exponent 1; residue degree 1;
empty proper scheme (the k-point assertion has no instances, without excluding the
scheme); zero complexes; zero/noninvertible Weil morphisms; a moving point that
never returns at the selected exponent; identity coefficient extension; different
initial finite stages; arbitrary coefficient-closure universe. The source/target
of B are the moving fibre and original fibre respectively, not silently equal.
The statement imposes no finite-Tor, finite-map, weight, or semisimplicity hypothesis.

Searches for an existing statement:

- `msearch.py ... leanfinder "Evaluation of iterated global geometric Frobenius on
  compact cohomology of a Weil complex at a moving geometric point equals the
  iterated local stalk transport"`: eight hits, all ring Frobenius/perfection or
  Witt-isocrystal results (`coe_iterateFrobeniusEquiv`, `iterateFrobeniusEquiv_apply`,
  `PreTilt.coeff_iterate_frobeniusEquiv_symm`, `IsPurelyInseparable.iterateFrobeniusₛₗ`,
  `iterateFrobeniusEquiv_symm_add`, Witt-vector Frobenius and equivariance). None
  states an equation on constructible derived Weil complexes.
- `msearch.py ... leansearch "Evaluation at a moving geometric point intertwines
  powers of global geometric Frobenius with the iterated Weil fibre map and point
  transport"`: eight hits on `LinearMap.iterateFrobenius`, Witt-vector identities,
  and scheme structure-sheaf/residue-field evaluation naturality. None matches.
- `msearch.py ... loogle "CategoryTheory.NaturalTransport.inducedEndomorphism_pow,
  WeilConjectures.globalGeometricFrobenius"`: zero hits; first project-specific
  identifier unknown to the Mathlib service. Read the actual local project
  declaration and used it as a proof dependency, not as an exact match.
- `msearch.py ... grep "WeilComplex|semilinear.*germ|germ.*Frobenius"`: zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `properWeilIterate|Weil.*[Ii]terate.*[Gg]erm|[Gg]erm.*[Ii]terate|<item-id>`:
  only unrelated topological/analytic germs and the semilinear-germ dependency.
- `grep -rn <item-id> lean/WeilConjectures`: no hits. The existing generic natural
  transport power theorem lacks the Weil germ/naturality/local-return conclusions;
  the existing proper semilinear theorem lacks the Weil structure and F^r.

Source reading: latest blueprint global/local geometric Frobenius definitions,
plus the actual Deligne Weil II PDF printed pp. 150--153, especially (1.1.3)
localization/common finite stages, (1.1.7) geometric convention, (1.1.10)--(1.1.13)
Weil action and degree-normalized closed-point Frobenius. The seven proof steps of
the assigned node are retained in the declaration proof docstrings.

The original delivery omitted definition ownership. The returned H2 fault is repaired below with two existing-definition nodes and five direct statement-dependency citations.
Validation: `scompile.py` compiles the sandbox and the actual module separately;
the final version is clean, with no extra warnings. Final delivery preflight and
its separate per-file compilation are run through `deliver2.py` below.

## Second reading by NZ

This is a separate self-review pass, not a claim of review by a second agent;
the dispatch brief prohibits starting agents and assigns independent review to
the maintainer. I reopened the complete node and the final module. The rational
six conjuncts match the two displayed equations, invertibility, arbitrary Weil
morphism naturality, the fixed-point return and the closed-point clause. A first
version had assumed the return alongside `hfix`; the final version explicitly
asserts that return from `hfix` before quantifying over its proof. The common-stage
six formulas are written after faithful scalar realization and quantify over all
finite stages; finite-model existence covers every common-stage pair and arrow,
while `modelSectionsComparison` ties each model to the actual published global
operator. Explicit End typing/`End.of` and parentheses around powers were needed
for Lean's monoid notation; they change no object or operation. Removed the unused
name on the point-identification proof without dropping that hypothesis. Checked
that no heart-only, finite-morphism or integral-invariance hypothesis has entered.


## Repair of return at ac681637b6b6

The retained sandbox is the returned delivery. Compared its item node with current
main: before this repair, all non-Lean fields were identical. The return explicitly
accepted every mathematical clause and the three theorem docstrings. This repair
changes no definition body or theorem signature: it promotes two existing imports
to public imports and directly imports the point-Frobenius and finite-index owner
modules. It adds two exact-existing definition records and cites them, together
with the three existing owners, in both the item's statement and `stmt_deps`.
The theorem `lem-a1-proper-sections-semilinear-germs` remains only a proof dependency;
its germ identity is not assumed by the new definition nodes.

Every declaration flagged by H2 now has an explicit statement owner:

- `ProperSemilinearGerms.rationalSections`, `rationalFibre`, `rationalTransport`,
  `rationalSquare`, `stageRealization` and `movingPoint_properties`:
  `def-a1-proper-sections-semilinear-iterate-data`, module
  `Sheaf.Paper.ProperSectionsSemilinearGerms`. The first two are the actual compact
  sections and derived point-fibre functors. The recursion renders the contracted
  compact transport, with positive exponent `n+1`. The two moving-point identities
  supply precisely the section proof `.1` and square equality `.2`; the square
  comparison is the composite of the inverse compositor, equality identification,
  and compositor, with no arbitrary comparison map. Stage realization uses the
  actual small coefficient embedding and preserves independent universes.
- `frobeniusCohomologyQbarFunctor` and `frobeniusCohomologyQbarSourceEq`:
  `def-a1-common-stage-cohomology-realization`, module
  `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`. The new definition statement
  specifies the object formula and every representative-arrow formula, including
  the two canonical change-of-stage comparisons. Its published existence/uniqueness
  theorem determines the functor uniquely; this is not a choice from bare existence.
  The source equality is exactly the object clause. These are the precise functor
  and equality used by `modelSectionsComparison` and the final global-operator
  intertwining clause.
- `frobeniusPointIso`, `frobeniusPointPrimeInvertible`:
  `def-weil-frobenius-point-transport`, module
  `Sheaf.SixFunctors.FrobeniusPointTransport`; this supplies the moving-point
  automorphism and the point pullback instance.
- `GeneralAlgebraicallyClosedCoefficients.inclusion`:
  `def-weil-algebraically-closed-coefficients`, module
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`; this is the actual common-stage
  inclusion used in simultaneous models and arrow realization.
- `Padic.FiniteCoefficientFields`:
  `def-weil-finite-subextension-directed-set`, module
  `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`; this is the finite coefficient
  index in `global_eq`, `commonStage` and the realization formulas.

No new Lean file or postponed proof is introduced. In particular there is no H4
copy of the recursion or the moving-point property theorem. The original germ
owner retains its declarations and is cited by the new iterate-data owner.

## New nodes

`def-a1-proper-sections-semilinear-iterate-data` is an `existing:true` definition
owner in `sec-deligne-laumon-a1` for exactly the six published declarations listed
above. Its TeX gives compact sections, point fibres, the positive-iterate recursion,
the two elementary moving-point identities, the canonical square and stage
realization. Source: Deligne Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.14), pp.150--153,
as implemented by the already published module. No germ identity is included.
The exact Lean signature for the primary recursive definition is copied verbatim.

`def-a1-common-stage-cohomology-realization` is an `existing:true` definition owner
in the same chapter for the published canonical Qbar functor and source equality.
Its TeX spells out the unique functor's value on every pair and representative
arrow, including ordinary/compact choice, the actual compactification, identity
enlargements and independent universes. Source: the same Deligne finite-field and
cohomology-transport passages, with the recorded common-stage coefficient recipe.
Its primary signature is copied verbatim from the published source.

Searches for both owners are recorded in their `mathlib_searches` and the sandbox
`searches.jsonl`, with actual result names. `msearch.py leansearch` and `leanfinder`
were each run on (1) "Iterated semilinear proper cohomology transport and pullback
square at a moving geometric point" and (2) "Canonical derived cohomology functor
on algebraically closed coefficients defined by common finite coefficient stages".
Each returned eight hits: seminorms, scheme pullback squares, group cohomology and
generic derived functors; none is this constructible coefficient construction.
`msearch.py grep` for
`rationalTransport|rationalSquare|stageRealization|frobeniusCohomologyQbarFunctor`
returned zero Mathlib hits. `rg` over `lean/WeilConjectures`, `lean/Sheaf` and
`dag/nodes` found the exact published declarations and users of them. Auditing all
definition-node Lean records found only the old germ/moving-point owner in the
first module, and no definition owner of QbarFunctor/SourceEq in the second.
`tools/blueprint_refs.py search semilinear germ` returned one different blueprint
node; `search coefficient cohomology` returned 262 broad matches without a separate
owner. `ancestor` confirmed `lem-a1-finite-boundary-weights`; both new records use
the full via chain through this item and its parent. Thus the definitions are
reused, not redeclared; the new records supply the missing DAG ownership.

## Statement corrected

This is a citation-only ownership correction explicitly required by the return,
not a disputed mathematical statement. The old statement is preserved verbatim
in the item's `statement_change.old_statement`. The additional paragraph names
the existing specified constructions and introduces no hypothesis or conclusion.
The source is Deligne Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.14), pp.150--153.
The original `stmt_deps` is preserved in `statement_change.old_stmt_deps`; proof
and proof dependencies are unchanged. A complete scan of every node's `stmt_deps`
and `proof_deps` found exactly one citer:

- `lem-a1-finite-weil-sections-decomposition`: holds. Every formula and hypothesis
  it uses is unchanged; the extra references assign ownership to the same maps.

## Second reading by NZ (repair)

Reopened both exact source signatures and their full docstrings, the new definition
records and the retained module. Checked the recursion against
`localPullbackComposition`: the inverse compositor contracts
`L(g^r)^*Lg^*M` to `L(g^(r+1))^*M`, after the iterate on `Lg^*M`.
The square has source `(h^r)^*z_r^*M` and target `z^*(g^r)^*M`.
The elementary projection/square identities are explicitly owned, rather than
silently imported from the uncited germ theorem. The Qbar source equality is
exactly the unique functor's object equation. No extra data, stronger assumption,
unit change or theorem proof has entered. The previously checked zero object,
empty scheme, n=0 (exponent one), fixed point, arbitrary Weil arrow, finite stage
identity and independent-universe cases remain unchanged.
