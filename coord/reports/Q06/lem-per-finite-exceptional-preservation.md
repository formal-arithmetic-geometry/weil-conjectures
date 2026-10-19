## Worker report

The module `Sheaf.Paper.FiniteFieldExceptionalPreservation` states
`AlgebraicGeometry.Etale.finiteField_exceptional_preservation`, with one postponed
proof and no new Lean definitions. The node statement and proof are unchanged.
The existing scheme-excellence predicate is cited through its landed node.
The canonical coefficient maps are cited through the new definition node
`def-per-exceptional-coefficient-maps`, which records the four unchanged existing
definitions. There are no new or dependency modules.

Hypotheses, clause by clause:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite field B of characteristic ell: `(B : Type (u + 1)) [Field B] [Finite B]
  [CharP B l]`. The coefficient universe is the published ModuleCat convention.
- Schemes X,Y: `{X Y : Scheme.{u}}`; Noetherian: `[IsNoetherian X] [IsNoetherian Y]`.
- Excellent schemes: `_hX : Orgogozo.IsExcellentScheme X` and `_hY` for Y. The
  reused definition is `∀ U : S.affineOpens, IsExcellent Γ(S, U)` and directly
  uses the dependency's ring predicate, not a different version of excellence.
- Ell invertible on both schemes: `_hlX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`
  and the corresponding `_hlY`.
- Morphism f: `(f : X ⟶ Y)`; separated: `[IsSeparated f]`; finite type:
  `[LocallyOfFiniteType f] [QuasiCompact f]`.
- Compactifiability: `[HasCompactification f]`. All maps consistently use
  `HasCompactification.compactification f`, the compactification chosen by this
  existing API; no arbitrary coefficient comparison is assumed.

Conclusions, clause by clause:

1. `HasBoundedBelowUpperShriek (ModuleCat B) f` asserts existence of the
   ordinary ambient right adjoint together with preservation of D+. Restricting
   the existing ambient adjunction therefore gives the required bounded-below
   right adjoint. Compact support itself has its existing D+ compatibility.
2. The next two universal implications assert preservation of the exact recorded
   `DerivedCategory.isBoundedConstructible` predicate by `rightDerivedLowerShriek`
   and `rightDerivedUpperShriek` respectively. In particular no finite-Tor
   predicate, finite-field base scheme, finite-dimensional scheme or smoothness
   hypothesis has replaced bounded constructibility.
3. The existential F,G,a,eF,eG clause explicitly supplies the restricted adjunction
   between `BoundedConstructibleDerivedCategory B X` and its Y analogue. eF,eG
   identify their inclusions with the ambient functors. The displayed equation
   identifies its Hom bijection with the ambient exceptional Hom bijection after
   those identifications. Thus the adjunction itself restricts with its unit and
   counit; the statement does not merely assert existence of an unrelated adjunction.
4. Every finite extension is quantified by `(C : Type (u + 1)) [Field C] [Finite C]
   [Algebra B C]`, using `algebraMap B C`. A unital homomorphism from the field B
   into a field is injective, and finite C is finite-dimensional over B, so these
   are exactly finite extensions of finite fields, including the identity.
5. T_W is the existing `scalarExtension (algebraMap B C) W`. Its abbreviation
   specializes the general-site fixed scalar extension to the *small etale*
   topology, not the pro-etale topology. `scalarTensorIso` in
   `Sheaf.Paper.EtaleDerivedScalarTensor` identifies its scalar restriction with
   tensor by C_W[0], normalized by the actual balancing map on cochain
   representatives; symmetry supplies the coefficient-first convention.
6. `c` is a natural isomorphism on D+(X_et,B), viewed in the ambient output
   category. Every component is required to equal the existing
   `ExceptionalCoefficients.compactSupportMap (algebraMap B C)` at the selected
   compactification. That map is the proper scalar mate followed by direct image
   of the canonical open scalar comparison. Thus a basis or an arbitrary
   isomorphism is not part of the data.
7. `α` is a natural isomorphism on the full bounded constructible input category,
   with components exactly the existing `ExceptionalCoefficients.mateMap`.
   The last displayed equation is `F_C(α_L); ε_C = c^{-1}_{G_B L}; T_Y(ε_B)`.
   Its inverse is written using the existing total `comparisonInverse`: on D+,
   c's components are isomorphisms by clause 6. Preservation gives G_B L bounded
   constructible, hence in D+, so the zero fallback in that preexisting helper
   is never used here. The definition of mateMap is precisely the adjunction
   transpose of this composite, so its normalization is fixed, not just an
   existence assertion about some exceptional isomorphism.

Dependency declarations read and reused:

- `def-weil-scheme-morphism-properties` is a convention node, not a declaration.
  The named Mathlib properties `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  and `IsNoetherian` render its relevant notions.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, together with the actual
  `Orgogozo.IsExcellentScheme` in `Sheaf.Paper.OrgogozoInductionData` (landed
  `def-trf-orgogozo-induction-data`, now cited).
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement`,
  its category, and the imported `Compactification`/`HasCompactification` data.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, its chosen-compactification
  `rightDerivedLowerShriek`, and the D+ compatibility.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `DerivedCategory.isBoundedConstructible`, `BoundedConstructibleDerivedCategory`.
  These are ordinary small-etale categories with constructibility by finite
  locally constant module values and bounded cohomology.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`, the genuine
  K-flat-derived tensor; this is the tensor in the scalarTensorIso just described.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`:
  `rightDerivedUpperShriek`, `rightDerivedUpperShriekAdjunction`,
  `HasBoundedBelowUpperShriek`.
- `Sheaf.Paper.ExceptionalCoefficientComparison`: `compactSupportMap`,
  `comparisonInverse`, `mateMap`, and `openIso` in `ExceptionalCoefficients`
  (new owner `def-per-exceptional-coefficient-maps`, with `existing: true`). Their full defining
  terms were read. That node's theorem only treats smooth finite quotient
  coefficients and is not this theorem about arbitrary finite field extensions.
- All recorded proof-dependency modules are imported without `public` unless
  they are already used by the statement. The finiteness prerequisite
  `lem-per-quasi-excellent-etale-direct-image-finiteness` currently has no Lean
  record, so it has no module to import; it remains in the unchanged proof plan.

Edge cases checked before writing: empty X or Y and the zero complex cause no
nonempty or nonzero assumption; the empty input case requires no maximum over
charts. A finite field excludes the zero ring by Field, just as in the node.
The identity extension B=C and every prime including 2 are included. No
positive-dimensional, connected, regular, smooth, finite-dimensional, finite-field
base, or separable-closure assumption is imposed. All universes and binders are
explicit. Both coefficient fields occupy the established u+1 coefficient universe
for Scheme.{u}; their finite extensions are covered up to canonical universe lifts.

Source read directly: the local Bhatt--Scholze PDF, Section 6.7, Theorem 6.7.1 and
Lemma 6.7.18 with its proof. Its local smooth/closed factorization and the
projection-formula/adjunction argument agree with the node's expanded twelve-step
proof, copied in full mathematical content into the theorem docstring.

Searches for an existing declaration (2026-10-18):

- msearch leansearch, query `Exceptional inverse image on etale sheaves preserves
  bounded constructible complexes and commutes with finite field coefficient extension`:
  eight sheaf-pullback/etale stability results; no matching theorem.
- msearch leanfinder, query `finite field coefficients etale compact support
  exceptional inverse image preserves bounded constructible and commutes finite
  scalar extension`: eight unrelated Chevalley/constructible-spectrum results;
  no matching theorem.
- msearch loogle, query `CategoryTheory.Adjunction, ModuleCat`: twelve results,
  including ModuleCat.extendRestrictScalarsAdj and restrictCoextendScalarsAdj;
  neither is an exceptional preservation/coefficient theorem.
- msearch grep, query `derivedExtendScalars|derivedChangeOfRings|extendScalars`
  under Mathlib/CategoryTheory: zero results.
- rg in the upstream WeilConjectures tree for exceptional preservation and finite
  coefficients found UpperShriekConstructible and TraceFormula definitions.
  The former assumes a finite-type field base and uses the upstream distinct
  constructibility predicate; it is not this excellent-scheme statement.
- rg for the item id in upstream WeilConjectures found no result.
- rg in lean/Sheaf for scalarExtension, coefficient comparisons, and excellence
  found the exact existing helpers reused above. No second definition is made.
- The three added-interface candidates were checked through the DAG: no path
  from the reused coefficient or excellence node back to this item exists.

Validation: scompile.py compiled the delivered module cleanly (exit 0), both in
the sandbox and as a library module, with no errors or warnings.

No statement correction, disputed statement, or dependency module repair is needed.
The returned H2 ownership issue is repaired by the definition node below.

## Second reading by Q06

A separate self-check of the completed node and module matched every hypothesis
and conclusion against the list above. This is a worker consistency check;
independent review belongs to the maintainer, as the dispatch brief prescribes,
and no second agent was started. The full-subcategory Hom equation was checked
for direction: eF inverse starts at ambient F_B(K), the restricted adjoint map
lands in G(L), and eG hom moves its inclusion to ambient G_B(L). The coefficient
comparison uses D+ inputs, while the exceptional comparison uses precisely
bounded constructible inputs. Both isomorphisms are natural by their Lean types.
The exceptional counit is the same chosen ambient adjunction's counit in the
comparison definition and in the equation. No mismatch or change to the natural
statement was found.

## New nodes

`def-per-exceptional-coefficient-maps` owns the unchanged existing
`ExceptionalCoefficients.openIso`, `compactSupportMap`, `comparisonInverse`, and
`mateMap` in `Sheaf.Paper.ExceptionalCoefficientComparison`. Its `lean` has
`existing: true`; its main signature is copied verbatim from `def compactSupportMap`.
No module is moved, copied, or edited. The item cites this definition node instead
of `lem-pur-exceptional-coefficient-comparison`. That theorem's specialized quotient
coefficient conclusions are not a prerequisite for these definitions.

The new node quantifies over commutative rings A,B and a ring map phi, exactly the
module's section variables. Its open comparison is `openIso` at an open immersion;
its compactification and object are the binders of `compactSupportMap`; its
inverse-or-zero is the full `if IsIso ... then inv ... else 0` construction of
`comparisonInverse`. Only `mateMap` needs `[Finite A] [Finite B]` and the chosen
compactification, as the new node says. Its defining transpose uses precisely
`comparisonInverse` followed by the scalar extension of the ambient counit.
No invertibility statement or extra preservation assertion is placed in the
definition node. The identity coefficient map, zero complexes, and empty schemes
remain covered; inverse-or-zero makes all four definitions total at their stated
domains. Neither `tensorIso` nor `unitIso` occurs in the item's statement.

New-node searches on 2026-10-18: LeanSearch for canonical scalar extension comparison
for compactly supported etale cohomology and its exceptional adjunction mate gave
eight ordinary module extension/restriction and localization hits, no exact match.
LeanFinder for scalar extension/open extension by zero and compact support mates
gave eight unrelated continuous-linear-map/support results. msearch grep for
`compactSupportMap|comparisonInverse|mateMap|openIso` in Mathlib CategoryTheory gave
zero hits. Direct rg in upstream WeilConjectures gave no matches; rg in the
existing project found precisely the reused four definitions at lines 46,64,79,94.
DAG searches found the theorem and consumers but no definition owner; blueprint
search found only the general scalar-exceptional comparison units. These actual
search results are recorded in the new node's `mathlib_searches`.

Repair self-check: compared the saved packet with the returned head's description
and current base. The initial dry run compiled and passed without pushing, but
retained the reported H2 defect. The only substantive repair is the new ownership
node and its replacement statement-dependency edge; the Lean file, mathematical
statement, twelve-step proof plan, and existing hypothesis/clause audit are retained.
The new node's statement describes each of the four actual defining terms read
from the published module. Its main Lean signature and declaration list were
checked against that module. No `.choose` of the coefficient-comparison theorem
is used, and no second definition is introduced.
