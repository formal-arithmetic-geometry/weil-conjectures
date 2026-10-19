## Worker report

Item: `det-prop-closed-adjoint-constructible-support`; group Q40; 2026-10-18 UTC.

The module `Sheaf.Paper.ClosedSupportConstructible` states
`AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_constructible`, with its sole
proof `sorry`. The real Prop-valued definition `ClosedSupportConstructibleAssertions`
expands this node's conclusion; it does not introduce another support functor, coefficient
construction, or constructibility predicate. Both declarations are listed in the Lean
record. The item's statement, statement dependencies and proof plan are unchanged.

### Hypotheses and clauses

- Distinct primes: `(ℓ : ℕ) [Fact ℓ.Prime]`, `(p : ℕ) [Fact p.Prime]`,
  `(hpℓ : p ≠ ℓ)`.
- The characteristic-p base field: `(k : Type u) [Field k] [CharP k p]`.
- A fixed algebraic closure: the existing `PadicAlgCl ℓ`, with its extended norm. This
  is the project's chosen representative for the algebraic closure in the node.
- Finite subextensions E: `∀ E : PadicAlgCl.FiniteIntermediateField ℓ`. This existing
  subtype records precisely finite-dimensional intermediate fields of that closure.
- The permitted coefficient choices: the conclusion is the conjunction of the assertion
  for every `Profinite.continuousMapRingObj.{u} E` and the assertion for
  `Profinite.padicAlgClRingObj.{u} ℓ`. The former is continuous functions with the
  restricted topology; the latter is the actual finite-subextension-valued sheaf, not
  the full continuous-function sheaf of the algebraic closure. Both use their canonical
  ring-object structures; no arbitrary ring structure is assumed on an equal carrier.
  The conjunction spells out the node's two choices without an additional coefficient
  hypothesis or restricting to only one of them.
- Schemes X,Z,U: `{Z U X : Scheme.{u}}` and, separately for every scheme, an `Over`
  instance over `Spec (.of k)` and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`
  instances on its structure morphism. These are exactly separated finite type over k.
- Morphisms over k: `(i : Z ⟶ X) (j : U ⟶ X)` with
  `[i.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))]`.
- Closed and open immersions: `[IsClosedImmersion i] [IsOpenImmersion j]`.
- Complementarity: `hij : Set.range i.base = (Set.range j.base)ᶜ`.
  No quasi-compactness hypothesis on j is added: it follows in the stated setting.
- Λ_T: every module category and constructibility predicate uses
  `condensedRingObj Λ T`, the recorded pullback p_T^* of the coefficient ring object.
- Unbounded derived category: the ambient category is the existing
  `DerivedCategory (FormalSupportModules Λ T)`. `FormalSupportModules` abbreviates
  internal modules `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)`.
- K in Dbc(X,Λ): `∀ K : BoundedConstructible (condensedRingObj Λ X)`. The full
  subcategory is the recorded `sk-def-sfb-bounded-constructible` declaration; `K.obj`
  is its object in the ordinary unbounded derived category. In particular the middle
  term's bounded constructibility is already carried by its type.
- Sections with support: `(formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj`.
  The imported real construction is exactly `formalSupportKernel Λ j` followed by
  `formalSupportPullback Λ i`; the kernel is that of the canonical open unit.
- Exact closed direct image i_*: `(lowerStar Λ i).mapDerivedCategory`. The existing
  closed-immersion exactness instance permits this termwise derived functor.
- Exact inverse image j^*: `(formalSupportPullback Λ j).mapDerivedCategory`.
  This is the imported coefficient-compatible inverse image, transporting the action
  along the inverse of α_j. Extension of scalars along the isomorphism α_j is canonically
  this scalar transport, so it is the exact derived inverse image in the node, with
  its actual module action. No separate functor is defined in this delivery.
- Rj_*: `(lowerStar Λ j).rightDerivedFunctor`, the right derived functor of the full
  module pushforward composite, not of its individual abelian-sheaf factors.
- First arrow: `a.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj`.
  Here `a : lowerStar Λ i ⊣ formalClosedSupport Λ i j` is existential in the
  conclusion, normalized by
  `(formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
  (formalSupportKernelInclusion Λ j).app M` for every M. This is the same normalization
  as the recorded `FormalClosedSupportAssertions`. It identifies the canonical
  support adjunction, rather than allowing a rescaled counit. The kernel comparison
  is an isomorphism in the complementary case, so this equation determines the
  ordinary counit and hence the adjunction. No adjunction is assumed as input or
  chosen from an unspecified existence theorem.
- Second arrow: the unit of
  `(formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction`.
  It is exactly the canonical unit from K to Rj_*j^*K.
- Connecting arrow: `∃ δ : Rj_*j^*K ⟶ (i_*RΓ_ZK) ⟦(1 : ℤ)⟧`.
  The source does not specify a cone model or require a chosen connecting morphism.
- Distinguished triangle: `Triangle.mk` of those exact first two arrows and δ lies
  in `distTriang _`, in the ambient derived category on X.
- All terms are bounded constructible: explicit conjuncts assert
  `boundedConstructible (condensedRingObj Λ X)` for i_*RΓ_ZK, Rj_*j^*K, and
  `(i_*RΓ_ZK) ⟦(1 : ℤ)⟧`. Together with K's full-subcategory type these cover all
  four displayed terms, including the shifted term.
- Closed support is bounded constructible on Z: the last conjunct is
  `boundedConstructible (condensedRingObj Λ Z)` of the same RΓ_ZK object.

The helper is only the full expanded assertion at a coefficient ring. It is not asserted
for arbitrary rings: the theorem specializes it precisely to the two field coefficients.
Its existential ordinary adjunction is shared for all K, as the source's canonical
adjunction is. There is no stronger naturality requirement on the unspecified δ.

### Dependency declarations read and used

The statements and records of all eleven statement dependencies were read, including the
closed slopmaster2 audit of `sk-def-sfb-qlbar-condensed`. The relevant source docstrings
and signatures were opened. Module names below are imports or public reexports of the
stated module.

- `sk-def-sfb-dc-setting`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the standing
  explicit finite-type/over-field binders. No compactification is needed in this result.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing`, with its exported continuous and adic constructions.
- `sk-def-sfb-qlbar-condensed`: the audit's exact upstream module
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`, imported
  through `Condensed.FiniteSubextension`. Its node needs no replacement record.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and its
  commutativity instance, through the module-object derived imports.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, used by `FormalSupportModules`.
- `sk-def-sfb-bounded-constructible`:
  `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`, reexporting
  `AlgebraicGeometry.ProEtale.boundedConstructible`, `BoundedConstructible`, and
  `mem_boundedConstructible_iff` from
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`. This is exactly
  the recorded general ring-object constructibility predicate; it is not silently
  replaced by the separate finite-constant-model predicate.
- `sk-def-sfb-module-derived-pushpull`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`,
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`,
  `leftDerivedUpperStarIsoMapDerivedCategory`, and the generic total derived functors.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `sk-lem-formal-closed-support`: `Sheaf.Paper.FormalClosedSupport`,
  `AlgebraicGeometry.ProEtale.CondensedRing.FormalClosedSupportAssertions` and
  `formalClosedSupportAssertions`. This module reexports the exact existing
  `formalClosedSupport`, `formalSupportPullback`, `formalSupportPullbackAdjunction`,
  `formalSupportKernelComparison`, and `formalSupportKernelInclusion` used here.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated` and
  `CategoryTheory.IsTriangulated` in the Mathlib triangulated-category modules;
  `CategoryTheory.Pretriangulated.Triangle.mk` and `distTriang` express the triangle.

The recorded proof dependencies with declarations are imported as proof imports unless
already public statement imports. The not-yet-recorded proof-only node
`det-lem-formal-closed-support-derived` contributes no separate import. The seven-step
proof docstring follows the node, including quasi-compactness of j, termwise exactness,
the triangle, counit normalization by full faithfulness and two vanishings, open direct
image, triangulated closure and final closed pullback. Proofs remain entirely deferred.
The proof-only `CoefficientHeartTriangulated` currently speaks about constant-model
constructibility; relating its predicate to the statement dependency's general
constructibility remains a proof-stage interface obligation, not a reason to change
this node's statement.

### Edge cases

Checked the formula before writing and again against the elaborated statement:

- Empty X (and hence empty Z,U): full subcategories and zero derived objects are allowed;
  there is no nonempty hypothesis.
- Empty Z, j the identity: closed support is zero, the open unit is invertible, and
  the triangle has vertices 0,K,K.
- Empty U, i the identity: closed support is K and the triangle has vertices K,K,0.
- Zero K: all four terms, including the shift, are zero and bounded constructible.
- Nonreduced closed subschemes and disconnected schemes are not excluded.
- Arbitrary integer cohomological bounds and the +1 shift are retained. There is no
  derived-completeness condition and no finite-ring or torsion hypothesis.
- ℓ=2 is included when p differs from it; p=ℓ is excluded exactly as in the source.
- The finite subextension includes the base field itself; the algebraic-closure branch
  retains finite-subextension-valued sections.
- Universe u is explicit, with `Scheme.{u}`, profinite objects in u+1 and coefficient
  groups in u+1. No object/morphism universe equality is added. All variables are bound;
  both auto-implicit options are disabled.

### Searches

All services used `/home/ubuntu/weil-launcher-nt/msearch.py Q40
 det-prop-closed-adjoint-constructible-support`:

1. LeanFinder: `Closed support localization triangle for bounded constructible proetale
   module complexes`. Eight hits, headed by
   `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, concerned generic derived
   boundedness; no matching support/constructibility theorem.
2. LeanSearch: `Derived sections with closed support preserve bounded constructible
   proetale sheaves`. Eight hits: generic sheaf pullback finite-limit preservation,
   ordinary compact support and global sections; no matching theorem.
3. Loogle: `Triangle, distTriang` returned a query parse failure, not evidence of absence.
   Retried `"Triangle.mk"`: eight hits giving the exact generic triangle constructor
   and its projections; used that constructor.
4. Mathlib grep service: `formalClosedSupport|closedSupport|sectionsWithSupport`.
   Two hits on unrelated locally finite-function closed support; no matching theorem.
5. Direct rg of the upstream source, the side framework and `lean/Sheaf` for support,
   formalClosedSupport and constructibility found the existing support constructions,
   the recorded dependency modules, and finite-coefficient support results. In particular,
   `AlgebraicGeometry.ProEtale.boundedConstructible_closedSupportTriangle_obj` in
   `WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible` was opened:
   it works in `Sheaf (ProEt.topology X) (ModuleCat Λ)` for a finite discrete ring Λ
   killed by an invertible integer. It does not state this theorem for internal modules
   over the non-discrete condensed E or finite-subextension-valued Qbar coefficients.
6. Direct rg of `ClosedSupportConstructibleAssertions|closedSupport_constructible` in
   Mathlib, upstream sources, side framework, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` found no existing name. The exact blueprint-id search
   in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` also found no declaration.
7. The current blueprint detail statement and its proof were opened in
   `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`.
   `coord/pefw-upstream-framework.md` was read to use the actual module-object overlay.

No statement correction, dependency replacement or new DAG notion is needed. No
STATEMENT-DISPUTED flag is raised.

### Validation

`scompile.py Q40 det-prop-closed-adjoint-constructible-support
 lean/Sheaf/Paper/ClosedSupportConstructible.lean` (absolute sandbox filename passed)
compiled the sandbox file in 12.4 seconds and the library-path file in 9.7 seconds.
No error or warning remained. The first attempt exposed the lexer token `)⟦` imported
by the module-operation notation; adding whitespace before shift notation repaired it.
Every line is at most 100 characters. There is one theorem and its only proof is `sorry`.

## Second reading by Q40

This is a repeated source-to-signature reading by this worker; the dispatcher explicitly
forbids starting other agents. The independent reading is the maintainer's delivery review.
I reopened the node and the module and checked all hypotheses and all conclusion clauses
against the correspondence above. The prime and characteristic binders, all three schemes'
finite-type and separated structure maps, both k-morphism instances, closed/open immersions
and actual complement equality are present. The E and Qbar conjunction retains both cases
with the correct topology and canonical ring structures. The helper quantifies over the
recorded bounded-constructible full subcategory. Its support object uses the recorded kernel
functor, not an arbitrary right adjoint. The ordinary adjunction's normalization fixes the
counit; its actual derived counit and the canonical open unit are used literally in
`Triangle.mk`. The three additional displayed terms, including the shift, and the support
object on Z have individual predicate conjuncts. No assumption of quasi-compact j,
nonempty schemes, torsion coefficients, or derived completeness has slipped in.

The source's four displayed terms require four checks; K's check is provided by its type,
so no redundant conclusion is added. The connecting arrow is existential exactly because
the node asserts a distinguished triangle without choosing a cone model. The only repair
found in the file was the shift-token spacing described above. The related finite-discrete
coefficient theorem was read and rejected as a match because its category and coefficients
differ. The helper is a real definition of this assertion, with no proof holes; the main
statement has precisely the expected postponed proof.
