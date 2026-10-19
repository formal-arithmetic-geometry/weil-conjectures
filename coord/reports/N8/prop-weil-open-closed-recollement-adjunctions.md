## Worker report

The module `Sheaf.Paper.OpenClosedRecollementAdjunctions` states
`WeilConjectures.openClosedRecollement_adjunctions`. Its sole postponed proof is
this theorem. The two auxiliary instances apply already recorded finiteness and
constant-coefficient-isomorphism theorems; the abbreviation specializes the
recorded tensor pullback and exact derived descent. No new mathematical notion
or arbitrary functor, coefficient identification, or adjunction is introduced.

Hypothesis and clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E of Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its coefficient ring is exactly the recorded
  `Padic.coefficientExtensionRing l E (n + 1)`, namely O_E/(varpi_E^(n+1)).
  `(n : ℕ)` enumerates all positive levels bijectively. There is no level-zero case.
- Schemes and invertibility: `{X U Z : Scheme.{u}}` and the three instances
  `[∀ x : T, Invertible (l : T.residueField x)]`, for T=X,U,Z, spell out the
  standing hypotheses of def-weil-open-closed-recollement.
- Complementary open and closed immersions: `(j : U ⟶ X) (i : Z ⟶ X)`,
  `[IsOpenImmersion j] [IsClosedImmersion i]`, and
  `(_hU : Set.range j = (Set.range i)ᶜ)`. No quasi-compactness assumption occurs.
- The ambient ordinary derived categories are the actual
  `DerivedCategory (proEtaleRingModules T (proEtaleConstantRing T A))`;
  the imported `proEtaleDerivedCategory T A` is this same standard localization.
  Objects are not restricted to bounded or constructible complexes, and there is
  no integral completion or rationalization.
- Extension by zero is exactly the recorded `sfIntrinsicExtensionByZero j A`,
  followed by `mapDerivedCategory`. Its exactness instances are imported from
  the recorded exactness module. No new extension-by-zero functor is constructed.
- Pullback is `openClosedDerivedPullback l E n f`, a specialization of
  `proEtaleRingDerivedPullback f R S c`. Here R and S are the actual constant
  commutative ring sheaves and c is `asIso (proEtaleCoefficientInverseImageMap f A)`.
  This is the canonical constant-section map, whose invertibility is supplied by
  the existing `finiteCoefficientCommRingMap_isIso` theorem. Its usual universe
  lift is assigned the discrete topology explicitly when applying that theorem;
  no topology is assumed on the input extension E and no new hypothesis is added.
  The underlying pullback is the recorded sheaf inverse image followed by the
  sheaf tensor extension of scalars, then exact termwise descent.
- Closed derived direct image is precisely `proEtaleConstantDerivedDirectImage i A`,
  defined by the recorded sectionwise direct image and K-injective right derivation
  in all modules. It is the finite-level direct image reexported by the recorded
  def-weil-derived-direct-image module.
- `∃ (aj : ... ⊣ ...) (ai : ... ⊣ ...), ...` states both adjunctions for these
  specified functors, including their actual units, counits, and triangle identities.
  `IsIso aj.unit` is the open natural isomorphism id -> j* j!;
  `IsIso ai.counit` is the closed natural isomorphism i* Ri_* -> id. These are
  assertions about adjunction units and counits, not about arbitrary isomorphisms
  between the same functors. IsIso for a natural transformation is equivalent to
  componentwise invertibility. The six proof steps of the node are reproduced in
  the theorem docstring, including the normalization of the counit on K-injectives.
- The final sentence specifying the operations selects the imported constructions;
  it does not make an additional assertion about tensor products or internal Hom.

Dependency interfaces read and used:

- def-weil-derived-direct-image: `Sheaf.Paper.SfDerivedDirectImage`; its finite
  stage uses `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage`, from
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`. Read the current
  server source as well as the local source.
- def-weil-pbc-proetale-operations:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` publicly reexports
  `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction` and
  `Sheaf.AlgebraicGeometry.ProEtaleOperations`. The actual declarations used are
  `proEtaleRingModulePullback`, `proEtaleRingDerivedPullback`, and the canonical
  constant coefficient specialization of direct image. The tensor construction,
  finite-preservation instances and ordinary derived constructions were read in full.
- def-weil-extension-by-zero:
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`; the import is public through
  its exactness module. Its canonical realization equivalences are unchanged.
- def-weil-derived-pullback-tensor-hom has no current Lean record. The finite-level
  operation used here is already constructed by the preceding recorded PBC interface;
  this item does not need the unstated integral/rational/common-stage packaging,
  tensor bifunctor, or internal Hom from that umbrella definition. Its complete node
  statement was read; no second definition or incomplete replacement of it is delivered.
- def-weil-open-closed-recollement has no current Lean record. This theorem needs
  precisely its coefficient/immersion hypotheses, explicitly bound above; it does
  not take or construct a recollement triangle or assert its existence. Thus there
  is no missing triangle object needed to type this adjunction statement. Checked
  the server DAG and the delivery branches: deliver/NK/def-weil-open-closed-recollement
  is a stage-1 definition split and has no Lean declaration. Read its report as well.
- def-weil-scheme-morphism-properties is explicitly a convention, with no separate
  notion. Used Mathlib's `IsOpenImmersion` and `IsClosedImmersion` as it instructs.

Proof imports include the recorded extension-by-zero adjunction and exactness,
constant exactness, homotopy adjunction, K-injective resolutions and preservation,
K-injective Hom calculation, localization universal property and adjunction machinery.
Two legacy proof-only imports (the old open-unit and closed-counit modules) cannot be
combined with the required reorganized finite-coefficient source: the compiler reports
`environment already contains 'AlgebraicGeometry.ProEtale.«term(_)_*[_]»'` from the
finite-coefficient module. They were omitted rather than redeclaring their statements.
The declarations remain named in the proof docstring for stage 3; the actual finite
coefficient constructions and required recorded public dependencies are imported.

Edge cases checked: n=0 in Lean means the source's n=1, including the residue-ring
case; every larger positive level occurs. Empty X (hence empty complementary pieces),
empty U, empty Z, and identity immersion cases all type without Nonempty or
quasi-compactness hypotheses. The zero derived object and arbitrary unbounded,
nonconstructible objects are included. The site keeps object universe u+1 and Hom
universe u. The ULift of scalars is the dependency's standard size lift, not a
restriction on schemes, extensions, or complexes. Isomorphisms of units/counits do
not rely on exactness of closed direct image or conservativity of geometric stalks.

Searches for the whole assertion:

1. msearch.py leanfinder, query `derived open closed recollement adjunction extension
   by zero unit isomorphism closed direct image counit`: eight hits, all abstract
   `CategoryTheory.Adjunction.derived...` comparison/unit/counit lemmas. No concrete
   pro-etale recollement assertion.
2. msearch.py loogle, query `CategoryTheory.Adjunction.derived`: three hits,
   derived/derived_counit/derived_unit. Infrastructure, not this statement.
3. msearch.py grep, query
   `derived.*adjunction|extensionByZero|openClosed|isIso.*counit`, scope CategoryTheory:
   25 hits, chiefly general fully faithful adjunctions and derived comparisons.
4. Source rg for `openClosed`, `openImmersionLowerShriek`, derived adjunctions,
   `FiniteCoefficientDerivedCategory`, and exact item id in WeilConjectures;
   analogous rg in lean/Sheaf, the finite-coefficient framework and the upstream
   name index. The whole assertion is absent. Existing upstream derived adjunctions
   use the fixed-scalar sheaf presentation; their individual definitions are not a
   statement of the conjunction for the recorded intrinsic module operations.
5. Read the node's earlier LeanSearch result (service unavailable), LeanFinder,
   qualified Loogle and focused grep records. No absence claim relies on its two
   invalid earlier queries.

Source check: read the exact blueprint order-1849 statement and proof on the server,
where the literature copy is present. Also checked Stacks
https://stacks.math.columbia.edu/tag/09AA and
https://stacks.math.columbia.edu/tag/09BN: closed direct image is fully faithful
without a quasi-compact-complement hypothesis; the open unit is invertible for any
open immersion. The statement remains unchanged. No STATEMENT-DISPUTED flag or
statement correction is needed.

Validation: the prescribed scompile.py wrapper compiled the final module cleanly,
including a second compilation at its actual library module path. No warning other
than the permitted sorry warning occurred. No global build or live source edit was
performed. The final deliver2.py --no-push result is recorded by the worker's READY
handoff; delivery is left to the independent second reader.

## Second reading by N8

I independently read the sandbox theorem and node, the six statement-dependency
nodes and their recorded interfaces, the blueprint source at order 1849 (available
locally in `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`),
and Stacks `proetale.tex`, labels `lemma-closed-immersion` (09AA) and
`lemma-open-immersion` (09BN), including the neighboring results which separately
require a quasi-compact complement. The source statement agrees verbatim with
the node. There is no `statement_change` and no source-based correction is needed.

The complete object/hypothesis/conclusion checklist is:

1. A prime ell: `(l : ℕ) [Fact l.Prime]`. Correct, including ell = 2; no
   characteristic-zero assumption is imposed on the schemes.
2. A finite extension E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`. Correct. I opened
   `Padic.coefficientExtensionRing`: this is the quotient of the spectral-valuation
   integer ring by the power of its uniformizer ideal, not E itself, Z/ell^n, or
   an arbitrary finite ring. No topology or norm on E is required from the caller.
3. A positive integer level: `(n : ℕ)` together with the uniform use of
   `Padic.coefficientExtensionRing l E (n + 1)`. Correct: this reindexes exactly
   the source's n >= 1, including its first level. The auxiliary finite instance
   applies `Padic.finite_coefficientExtensionRing` with `Nat.succ_pos n`.
4. Schemes U, Z, X with ell invertible: `{X U Z : Scheme.{u}}` and the three
   pointwise `Invertible (l : T.residueField x)` instances. Correct: these are
   exactly the hypotheses written in def-weil-open-closed-recollement. There is
   no finiteness, Noetherian, separation, boundedness or nonemptiness binder.
5. The specified complementary immersions: `(j : U ⟶ X) (i : Z ⟶ X)`,
   `[IsOpenImmersion j] [IsClosedImmersion i]`, and
   `Set.range j = (Set.range i)ᶜ`. Correct: this is complementarity of the
   underlying scheme-point images, with the given scheme structures retained.
6. The ambient ordinary derived categories with these constant coefficients:
   the functor types unfold to `DerivedCategory (proEtaleRingModules T
   (proEtaleConstantRing T A))`. Correct: these are localization at all
   quasi-isomorphisms of unbounded cochain complexes, not a constructible,
   bounded-below, completed, integral or rational category.
7. The actual open extension by zero j!: `(sfIntrinsicExtensionByZero j A).
   mapDerivedCategory`. Correct. I opened the recorded declaration and its
   exactness module: it transports the already constructed open localization
   extension by zero through the canonical fixed-scalar realization equivalence.
8. The actual pullbacks j* and i*: `openClosedDerivedPullback l E n j` and
   `openClosedDerivedPullback l E n i`. Correct. This abbreviation is a direct
   application of the recorded `proEtaleRingDerivedPullback`, with the canonical
   `proEtaleCoefficientInverseImageMap` and `asIso`, not a private construction.
   I read its tensor object/map definitions and exact-descent definition. The
   auxiliary isomorphism instance applies the existing finite constant-ring-map
   theorem with the standard ULift and discrete topology, adding no hypothesis.
9. The actual closed Ri_*: `proEtaleConstantDerivedDirectImage i A`. Correct.
   I opened that declaration: it is `proEtaleConstantModuleDirectImage` followed
   by `rightDerivedFunctor`, with K-injective resolutions in all module sheaves.
   I also checked `WeilConjectures.sfFiniteDerivedDirectImage`: it uses exactly this
   functor at coefficient level n+1, so the theorem uses the recorded operation.
10. Both adjunctions: the dependent existential binders `aj : j! ⊣ j*` and
    `ai : i* ⊣ Ri_*`. Correct order and quantification. An `Adjunction` includes
    natural unit, natural counit and both triangle identities; no adjunction is
    assumed as an input.
11. The open unit id -> j*j! is invertible: `IsIso aj.unit`. Correct: this concerns
    the unit of the asserted adjunction itself, with every component included.
12. The closed counit i*Ri_* -> id is invertible: `IsIso ai.counit`. Correct:
    this concerns the actual counit, not just an unspecified objectwise isomorphism.
13. The last source sentence fixes which operations the notation means. Items
    7--9 use those recorded constructions. It does not assert a separate tensor
    or internal-Hom compatibility, and the Lean adds no such assertion.

Dependency check: `def-weil-pbc-proetale-operations` publicly retains the arbitrary
identified-commutative-ring-sheaf operations through the finite-coefficient interface;
I read `ProEtaleOperations` and `ProEtaleOperationsCanonicalAdjunction` directly.
`def-weil-extension-by-zero` supplies exactly the intrinsic constant-ring functor
used here, and `def-weil-derived-direct-image` reexports the finite-level functor
used here. The unreified umbrella nodes `def-weil-derived-pullback-tensor-hom`
and `def-weil-open-closed-recollement` require no additional object in this theorem:
the former's finite pullback is the already recorded operations interface, and
the latter supplies the coefficient/immersion hypotheses, not a recollement
triangle assumed here. The statement does not use the triangle notion or the
umbrella node's integral/rational/tensor/Hom parts. Consequently there is no
missing notion, new definition node or dependency module to add. The morphism
properties node is a convention; its designated Mathlib immersion classes are
used. I also read `coord/pefw-upstream-framework.md` and the relevant module-object
derived adjunction declarations: they concern the condensed-ring presentation
and do not already state this conjunction for these intrinsic finite coefficients.

Edge cases: Lean n=0 is source level 1; source level 0 is outside the node's
explicit positive-level quantification. Empty X, empty U or Z, identity open or
closed immersion, and zero complexes are allowed. No Nonempty or QuasiCompact
assumption is present. Arbitrary unbounded and nonconstructible complexes are
included by the ordinary derived categories. Prime 2 and all allowed residue
characteristics are included. The small site retains object universe u+1 and
morphism universe u, and the coefficient ULift is exactly the existing standard
presentation; no site-universe equality or essentially-smallness hypothesis was
added. All variables and the single universe u are explicitly bound.

Independent searches (different queries from the worker):

- `msearch.py leanfinder`: "An open embedding induces a fully faithful extension
  by zero functor on unbounded derived categories and a closed embedding induces
  a fully faithful derived pushforward". Eight hits: generic derived-category
  exact-functor/localization infrastructure, single-functor fullness, and Zariski
  module pushforward; none states this pro-etale conjunction.
- `msearch.py loogle`: `CategoryTheory.Adjunction.isIso_unit_of_iso`. One general
  adjunction lemma; it does not assert either geometric adjunction or supply the
  required isomorphisms for these functors.
- `msearch.py grep`: `fullyFaithful.*[Ee]xtension|[Oo]pen.*[Aa]djunction|
  [Cc]losed.*[Cc]ounit`. General category-theoretic and unrelated topology hits;
  no whole-statement match. Source `rg` independently searched
  `sfFiniteDerivedPullback`, `ConstantDerivedPullback`, open/closed adjunctions,
  closed counits and exact item names in both `lean/Sheaf` and slopmaster2's
  `WeilConjectures`. I opened the closed-immersion fixed-scalar counit theorem
  and the newer module-object derived adjunctions rather than treating names as
  matches. These are individual ingredients or other coefficient presentations.
  The item's exact public declaration is absent from those sources.

H5/H6/H8/H9: neither helper instance has postponed data: both are applications of
existing named proofs; the abbreviation contains the actual imported functor.
The sole postponed theorem is the item and its proof is exactly `by sorry`.
Its docstring includes all six node proof steps: linear adjunction and exactness,
open localization descent and triangle identities, degreewise open unit,
K-injective direct-image computation, natural Hom bijections with representative
independence, and the closed-counit formula and naturality transport. Every new
declaration and the module docstring name a source and the exact blueprint id.
I found no unbound binder, local notation/instance, private notion, extra conclusion,
or line exceeding 100 characters. The worker explicitly documents the two old
proof-only imports that collide with the reorganized finite-coefficient modules;
the required dependency interfaces and usable proof infrastructure remain imported.

Mismatches found and changes made: none in the node or Lean. I retained the correct
statement and constructions and appended this independent audit only. The prescribed
`scompile.py` compiled the final module both as a sandbox module and at its actual
library path, in 5.5 and 5.8 seconds respectively, with no errors or warnings.
