## Worker report

The item is defined in `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint` as
`AlgebraicGeometry.Scheme.HasAmbientExceptionalRightAdjointDatum`. Its body is `Nonempty`
of the actual structure `SfAmbientExceptionalRightAdjointDatum`: no construction or
right adjoint is extracted from a mere unproved existence claim. The compact-support
candidate is a real composite of the transported recorded extension by zero, termwise
derived descent, and the canonical K-injective derived direct image.

Read the complete item and all thirteen immediate dependency statements and their
Lean/mathlib records. Read the source declarations and docstrings for Scheme, Over,
finite type, proper/separated, Compactification/Refinement, the p-adic quotient and its
finiteness interface, the intrinsic derived category, canonical constant-ring module
pullback/direct image, derived direct image, extension by zero and its exactness,
Functor.mapDerivedCategory and its singleFunctor comparison, and Adjunction/homEquiv.
The published relocated finite-coefficient extension-by-zero source was retrieved by
`scompile.py --source` because the old checkout does not contain that module path.
The archived blueprint definitions at orders 1488 and 1473 were read on the server;
the local read-only repository has only literature indexes, not those text files.

Hypotheses and defining clauses, one by one:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_ell: `E : Type u`, `Field E`, `Algebra (Padic l) E`, and
  `FiniteDimensional (Padic l) E`. The ring, integer ring, chosen uniformizer, and
  quotient are the recorded `Padic.coefficientExtensionRing l E n`; no second
  coefficient ring is defined. The finite instance comes from
  `Padic.finite_coefficientExtensionRing l E n hn`.
- Positive integer level: `(n : ℕ) (hn : 1 ≤ n)`. This includes n = 1.
- Scheme base and schemes: `(S X Y : Scheme.{u})`.
- Ell invertible on the whole base: `_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x)`.
  Invertibility in all local rings is the usual invertibility-on-a-scheme condition.
- Structure morphisms: `[X.Over S] [Y.Over S]`, with `X ↘ S` and `Y ↘ S`.
- Finite type of each structure morphism: both `LocallyOfFiniteType` and `QuasiCompact`
  instances, for each of `X ↘ S` and `Y ↘ S`.
- S-morphism f: `(f : X ⟶ Y) [f.IsOver S]`; this says exactly that the structure
  morphisms commute.
- Finite type and separated f: `[LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`.
- Chosen compactification: `(c : Compactification f)`, with existing fields `Z`, `i`,
  `g`, `comm`, `isOpenImmersion`, and `isProper`. Its S-structure is the composite
  `c.g ≫ (Y ↘ S)`. The existing refinement category uses actual proper Y-morphisms,
  with `i_hom` and `hom_g`, identities and composition as in the node.
- Every `D_T` is literally the recorded `Scheme.proEtaleDerivedCategory T A`, with
  the standard unbounded derived category of `proEtaleRingModules` over the constant
  CommRingCat sheaf after forgetting commutativity. The small-site object/morphism
  universe disparity is retained, and no universe equality or small-site restriction
  is added.
- For every d, `sfAmbientCompactSupportCandidate A d` is
  `(sfIntrinsicExtensionByZero d.i A).mapDerivedCategory ⋙
  proEtaleConstantDerivedDirectImage d.g A`. This is precisely D(j_!) followed by Rp_*;
  it is not the right derived functor of the underived composite. The recorded
  `SfDerivedDirectImage` module is imported and uses this same finite-level direct image.
- Clause 1 is the field `fullCD : ∃ c_cd : ℕ, sfFullCohomologicalDimension c.g A c_cd`.
  The dependency definition includes the original direct image and every site-object
  base change, with `r : ℤ`, `(c_cd : ℤ) < r`, and `Limits.IsZero` of its cohomology
  sheaf. It quantifies over ALL original-source module sheaves, then their canonical
  tensor inverse images along `pullback.fst`; it imposes no etale-origin condition.
- Clause 2: `rightAdjoint c` is G_c, and `adjunction c` is F_c ⊣ G_c.
  `Adjunction.homEquiv K L` gives the bijections natural in K and L. Reading
  Mathlib/CategoryTheory/Adjunction/Basic.lean:108–182 and 351–456 confirms that
  its unit is Φ(id), counit is Φ⁻¹(id), and natural Hom bijections are equivalent to
  this structure. No choice of a different adjunction convention is made.
- Clause 3: `rightAdjoint` and `adjunction` are families over EVERY `Compactification f`.
  The selected adjunction in clause 2 is their evaluation at c, so equality at c is
  definitional and no duplicate distinguished choice is stored.
- `theta v` is F_d ≅ F_e and `rho v` is G_e ≅ G_d, natural isomorphisms of functors
  for every refinement `v : d ⟶ e`. Their component directions are as in the node.
- `unit_compatibility` reads η_e ≫ ρ_(F_e K) = η_d ≫ G_d(θ_K).
  `counit_compatibility` reads F_d(ρ_L) ≫ ε_d = θ_(G_e L) ≫ ε_e.
  Lean's `≫` composes left to right, rendering precisely the displayed equations.
- `theta_id`, `rho_id` normalize identity refinements; `theta_comp` says
  θ_(v≫w) = θ_v ≪≫ θ_w; `rho_comp` says ρ_(v≫w) = ρ_w ≪≫ ρ_v.
- There are no FullCD fields for other d, no constructibility/interval/Tor preservation
  fields, no boundedness restriction, and no assertion that these data always exist.

Dependency declarations used: Mathlib `Scheme`, `Scheme.Over`, `Scheme.Hom.IsOver`,
`LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsProper`, `Functor.mapDerivedCategory`,
`Adjunction`; upstream `Compactification`, `Compactification.Refinement` and its category,
and `ProEtale.openImmersionLowerShriek` in the relocated FiniteCoefficient module;
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (`Padic.coefficientExtensionRing`,
`Padic.finite_coefficientExtensionRing`); `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
(`proEtaleDerivedCategory`); `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
(`proEtaleConstantRing`, `proEtaleConstantModulePullback`);
`Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`
(`proEtaleConstantDerivedDirectImage`);
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`
(`finiteCoefficientIntrinsicRealization`, `finiteCoefficientIntrinsicRealization_exact`).
The derived exact functor and natural-bijection adjunction dependencies are Mathlib leaves;
they correctly have no `lean` record and require no repair.

Edge cases checked by reading the formulas: n = 1; zero sheaf and zero complex;
empty source, target or base when the given morphisms exist; arbitrary nonempty or empty
site-object schemes; identity refinements and composable refinements; identity/proper
compactifications; and general scheme bases such as Spec Z[1/ell]. None requires a
finite-field base, a uniform bound for all compactifications, bounded-below objects,
or an etale-origin restriction. The existential predicate may be false; no universal
existence theorem is introduced. Quantification in FullCD is deliberately over original
source sheaves, not arbitrary sheaves on the base-changed source.

Searches actually run with msearch.py:

- LeanFinder: `A coherent family of right adjunctions for derived compact support functors
  indexed by compactification refinements` — eight generic condensed/locally-constant
  adjunctions; no match for the datum.
- Loogle: `CategoryTheory.Adjunction` — twelve generic adjunction constructors and facts,
  including Adjunction.mkOfHomEquiv, confirming the ingredient but not the whole datum.
- grep of Mathlib: `HasAmbientExceptionalRightAdjoint|FullCohomologicalDimension` — no hits.
- rg of upstream WeilConjectures, Mathlib and lean/Sheaf for all proposed full declaration
  names — no collision. Additional conceptual rg found upstream ExceptionalAdjoint.lean:
  its `HasAmbientExceptionalRightAdjoint` stores ONLY FullCD and omits the refinements,
  as its own module docstring admits, so it is not this node's datum. Its
  `HasUniformCohomologicalDimensionLE` has the stronger base-changed-input quantifier and
  cannot serve as this node's exact FullCD definition. `rightDerivedLowerShriekOfCompactification`
  acts on fixed-scalar sheaves; its formula is reused after the specified intrinsic transport.
- Searched the source by the literal node id: no upstream attachment.
- Inspected server delivery branches. `deliver/NW/def-weil-full-cohomological-dimension`
  exists, but its node is stage-1 DAG-only with no `lean` record. It confirms the same
  original-source/pullback quantifier. No Lean implementation is available there to reuse.
  The anticipated published FullCohomologicalDimension module was queried by
  `scompile.py --source` and was unavailable.

No statement correction or mathematical dispute is needed. The principal work is filling
three dependency interfaces while preserving the exact intrinsic category. The only
`sorry` introduced is the named theorem `sfIntrinsicExtensionByZero_exact`, belonging to
its genuine DAG node and carrying the complete two-step natural-language proof.

## Dependency modules

`def-weil-extension-by-zero`: the recorded fixed-scalar functor has the correct construction
but does not have the intrinsic source and target used by proEtaleDerivedCategory. The
module `ProEtaleIntrinsicExtensionByZero` repairs this interface using exactly the published
functor and the canonical additive exact realization equivalences. The equivalence inverse
is determined up to the equality/isomorphism used by downstream modules, not chosen from
a mere arbitrary nonempty class. The extension's zero/nonzero values, restrictions, module
actions and maps are unchanged under this canonical coefficient presentation.

`lem-weil-extension-by-zero-exact`: the genuine dependency has no Lean record.
`ProEtaleIntrinsicExtensionByZeroExact` states its additive, finite-limit and finite-colimit
preservation assertions for the recorded functor transported to intrinsic coefficients.
It imports the recorded proof-node modules `LocalizedModuleAdjunctionExact` and
`ProEtaleWeaklyEtaleLocalization`; the instances are projections of the named theorem.

`def-weil-full-cohomological-dimension`: no recorded declaration is available, and the
upstream candidate's second quantifier is strictly stronger. `SfFullCohomologicalDimension`
states both of the exact original clauses using DerivedCategory.singleFunctor in degree
zero and homologyFunctor. The second clause uses pullback.snd for p_V and the already
recorded proEtaleConstantModulePullback along pullback.fst for F restricted to X_V.
The predicate is defined for general schemes and commutative coefficients because its
formula needs no geometric hypotheses; the owning main definition specializes it to
exactly the required positive finite p-adic coefficient level and scheme-base hypotheses.
Only `lean` changes in each dependency node copy. No new DAG node is introduced.

## Second reading by NL

Independently read the complete item, all thirteen statement-dependency nodes, the four
delivered modules, and the dependency declarations themselves. Retrieved and read the
archived blueprint sources at orders 1488, 1473, 1471 and 1492 from the project server
because this machine's literature directory contains indexes only. Also read Stacks
`categories.tex`, definition-adjoint (0037) and its unit/counit paragraph;
`sites-modules.tex`, lemma-extension-by-zero (03DI) and
lemma-extension-by-zero-exact (03DJ), including the sectionwise formula and proof; and
`derived.tex`, lemma-right-derived-exact-functor (015F). The source introduces no
Noetherian, finite-field, boundedness or etale-origin hypothesis for this optional datum.

Object/hypothesis/clause checklist, written before judging the implementation:

1. A prime ell and finite extension E/Q_ell: `(l : ℕ) [Fact l.Prime]`,
   `(E : Type u) [Field E] [Algebra (Padic l) E]` and
   `[FiniteDimensional (Padic l) E]`. Verdict: exact. Read the coefficient-extension
   construction: its spectral absolute value, integer subring, chosen uniformizer and
   quotient are the already recorded ones, not new choices made by this delivery.
2. Level n >= 1 and A = O_E/(varpi_E^n): `(n : ℕ) (hn : 1 ≤ n)` and
   `Padic.coefficientExtensionRing l E n`. The named finiteness theorem supplies
   `[Finite A]` from these hypotheses. Verdict: exact; no finite field replaces A.
3. A scheme S with ell invertible: `(S X Y : Scheme.{u})` and
   `(_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))`. Verdict: exact; invertibility
   in every local ring is invertibility on S. The predicate does not silently use a
   stronger characteristic or finite-field assumption.
4. Finite-type S-schemes X and Y: `[X.Over S] [Y.Over S]` together with
   `LocallyOfFiniteType` and `QuasiCompact` for both structure maps `X ↘ S`, `Y ↘ S`.
   Read `Over.lean` and the finite-type declarations. Verdict: exact.
5. A separated finite-type S-morphism f: `(f : X ⟶ Y) [f.IsOver S]`,
   `[LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`. Verdict: exact.
6. A chosen compactification c: `(c : Compactification f)`. Read its `Z`, `g`, `i`,
   `comm`, `isProper`, `isOpenImmersion` fields and the refinement structure/category.
   Its ambient S-structure is `c.g ≫ (Y ↘ S)`, and `comm` makes its open map an
   S-morphism. Refinements have `i_hom` and `hom_g`; properness follows by the
   existing `Refinement.isProper` instance. Verdict: the same compactifications and
   proper Y-morphisms as the node, without extra stored structure.
7. Ordinary unbounded D_T over the constant coefficient sheaf: the actual
   `proEtaleDerivedCategory T A`. Read its expansion and `proEtaleRingModules`:
   these use the constant CommRingCat sheaf, forgotten to RingCat, and the standard
   derived category of its module sheaves. Verdict: exact; no completion,
   constructibility or bounded-below subcategory is substituted.
8. F_d = R(p_d)_* D(j_d!): `sfAmbientCompactSupportCandidate A d` is exactly
   `(sfIntrinsicExtensionByZero d.i A).mapDerivedCategory ⋙
   proEtaleConstantDerivedDirectImage d.g A`. Read the recorded finite-level
   direct image in `SfDerivedDirectImage`, which uses this same right derived
   functor. Read `mapDerivedCategory` and its singleFunctor comparison.
   Verdict: correct order and exact termwise descent, on the full derived category.
9. One nonnegative bound for the chosen proper part: the structure field
   `fullCD : ∃ c_cd : ℕ, sfFullCohomologicalDimension c.g A c_cd`.
   The definition's first conjunct quantifies over every source module sheaf F,
   integer r and r > c. The second quantifies over every `V : Y.ProEt`, the same
   original-source sheaves F and all r > c, using `pullback.snd` for p_V and
   `proEtaleConstantModulePullback (pullback.fst ...) A F` for F restricted to
   the fiber product. `DerivedCategory.singleFunctor _ 0` embeds F and
   `homologyFunctor _ r` is H^r; `IsZero` asserts vanishing of that sheaf.
   Verdict: both clauses, exactly the original-source/pullback quantifier;
   no etale-origin restriction and no bound for the other compactifications.
10. G_c and natural Hom bijections: `rightAdjoint c` and `adjunction c`.
    Read Mathlib `Adjunction`, `homEquiv`, `CoreHomEquiv` and `mkOfHomEquiv`.
    They encode precisely the natural bijections, with unit Phi(id) and counit
    Phi-inverse(id), rather than an unrelated notion of adjunction. Verdict: exact.
11. Adjunctions for every compactification, agreeing at c: the `rightAdjoint` and
    `adjunction` families quantify over every `d : Compactification f`. The
    distinguished choice is their evaluation at c, hence agreement is definitional.
    Verdict: exact; no separate choice or additional compatibility equation is needed.
12. Natural comparisons for every refinement: `theta v : F_d ≅ F_e` and
    `rho v : G_e ≅ G_d`. These are functor isomorphisms, not just pointwise
    isomorphisms without naturality. Verdict: both directions match the node.
13. Units agree: `unit_compatibility` is
    `eta_e(K) ≫ rho_v(F_e K) = eta_d(K) ≫ G_d(theta_v(K))`.
    Verdict: both sides have source K and target G_d(F_e K), exactly the displayed
    equation after converting the node's right-to-left composition to Lean's `≫`.
14. Counits agree: `counit_compatibility` is
    `F_d(rho_v(L)) ≫ epsilon_d(L) = theta_v(G_e L) ≫ epsilon_e(L)`.
    Verdict: both sides run from F_d(G_e L) to L, exactly the node's equation.
15. Identities and composition: `theta_id`, `rho_id` set identity comparisons;
    `theta_comp` uses `theta v ≪≫ theta w`, while `rho_comp` uses
    `rho w ≪≫ rho v`. Verdict: correct covariance/contravariance and all equations.
16. Existence of these data only: `HasAmbientExceptionalRightAdjointDatum` is
    `Nonempty (SfAmbientExceptionalRightAdjointDatum A f c)`. Verdict: exactly the
    existential predicate; it adds neither universal existence nor any preservation
    property of G_c. No object is extracted from this `Nonempty` by a definition.

Dependency-module review (H13):

- `ProEtaleIntrinsicExtensionByZero`: read the published relocated
  `FiniteCoefficient.LowerShriek.Open.Defs` via `scompile.py --source`. Its functor
  really is left Kan extension on module-valued presheaves followed by sheafification;
  monicity makes each index empty or a singleton. Read
  `finiteCoefficientIntrinsicScalarMap`, `finiteCoefficientIntrinsicRealization` and
  its exact-equivalence theorem in the published intrinsic comparison module. The
  equivalence is obtained from this specified functor; its inverse is determined up
  to natural isomorphism. Transport therefore preserves exactly the sections, scalar
  action and morphisms in the node's extension-by-zero construction. Its finite-ring
  hypotheses agree with the dependency node. No private second construction is used.
- `ProEtaleIntrinsicExtensionByZeroExact`: additive plus preservation of finite limits
  and colimits states exactness for this very transported functor. The docstring
  follows both current DAG proof steps, first identifying the localized site and
  coefficients and then applying exact extension by zero. The three instances are
  projections of the named postponed theorem, not additional unrecorded claims.
  Its proof imports were opened; the older localized-module theorem is specialized
  in universes, so no unsupported direct application is used in a definition here.
- `SfFullCohomologicalDimension`: the formula was checked against blueprint order
  1473 above. It is defined for general commutative A and p because those formulas
  require no properness or finite-type hypothesis. The main predicate specializes
  it to precisely A_{E,n} and the proper part of the chosen compactification;
  `IsProper c.g` and finite type of Y over S give finite type of c.Z over S.
  This general definition introduces no additional assumption or altered clause
  in the use requested by the node. The source warning is not a defining conjunct.

Edge cases: n = 1 is included; n = 0 is excluded exactly as in the node. Zero sheaves
and zero complexes remain in all quantifiers. The empty scheme is allowed for S,
X or Y whenever the specified morphisms exist; the invertibility condition on an
empty S is correctly vacuous. There is no nonempty-site-object or nonempty-index
hypothesis. Identity and composable refinements are explicitly covered. No
algebraically closed or finite-field assumption is added; e.g. a general base with
ell inverted is permitted. All universe binders are explicit (`universe u`), the
small-site object/morphism disparity u+1/u is retained, and no independent smaller
test universe makes a quantifier vacuous. Coefficients use the recorded ULift to
the site coefficient universe, not an equality between site universes. Read every
signature by eye and checked all four recorded `lean.statement` strings verbatim
against their files.

Independent searches (actual calls, different queries from the first worker):

- LeanSearch: `An unbounded derived compact support functor with right adjoints coherent
  for refinements of scheme compactifications` returned Internal Server Error.
  The unavailable service is logged; it provides no evidence of absence.
- LeanFinder: `A right adjunction for compact support derived image coherent under
  refinement of compactifications` returned eight condensed/topological adjunction
  results. None gives the geometric FullCD/refinement datum.
- Loogle: `CategoryTheory.Adjunction, "mate"` returned the generic `mateEquiv`
  family in `Mathlib.CategoryTheory.Adjunction.Mates`; these give ingredients,
  without the geometric data or hypotheses.
- msearch grep: `compactification.*(adjoint|cohomolog)|(adjoint|cohomolog).*compactification`
  found only the unrelated Stone-Cech compactification adjunction in Mathlib.
- Direct rg in Mathlib, slopmaster2 WeilConjectures and project `lean/Sheaf` found
  no collisions with any delivered declaration. Conceptual searches for coherent
  adjunctions, ambient adjoints, and full cohomological dimension located the upstream
  `ExceptionalAdjoint` and `FullCohomologicalDimension` modules, which I opened.
  `HasAmbientExceptionalRightAdjoint` stores only a bound and expressly omits
  refinement compatibility. `HasUniformCohomologicalDimensionLE` quantifies over
  arbitrary sheaves on each base-changed source, not the restrictions of original
  source sheaves in this node. The etale-origin predicates and etale ambient adjoints
  concern different classes/categories. None can replace the delivered notions.

Verdict: no mathematical mismatch, hollow definition, added hypothesis, omitted clause,
unbound variable or unsupported size restriction found. No Lean or node correction was
needed; the second reading adds this independent clause-by-clause report only. The
sole new `sorry` is the named exactness theorem belonging to its matching DAG node;
all data constructions are real. Only `lean` differs from the base in each of the four
node copies, and all Lean lines satisfy the 100-character convention. Compilation and
delivery-preflight results are recorded below after running the required wrappers.

Validation: `scompile.py NL def-weil-ambient-exceptional-adjoint` with all four sibling
modules passed. Each file was compiled separately in the private overlay, including its
library-form check; no errors or warnings occurred. Library-form times were 6.5 s for
extension by zero, 9.7 s for FullCD, 10.8 s for exactness and 7.0 s for the main module,
all within the default 60-second limit.

The first delivery dry run printed OK and passed both compilation and server preflight.
Its refresh revealed a concurrently landed stage-1 split of
`def-weil-full-cohomological-dimension` by NW. Reopened that complete current statement
and its eight dependency records: it spells out the same two conditions, degree-zero
embedding, canonical fiber-product projections and original-source module pullback
already checked above. It adds no mathematical clause requiring a Lean change. Refreshed
this dependency's sandbox JSON from the current shared node, preserving only our `lean`
record; the delivery therefore retains the newly reviewed split and dependency list.
No second definition has landed for it (`lean` is still absent on the base).
