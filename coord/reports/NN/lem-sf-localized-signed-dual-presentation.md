## Worker report

The module `Sheaf.Algebra.Homology.LocalizedSignedDualPresentation` states this
node in four named theorems, all with `sorry`, and supplies explicit maps and
transparent specializations of existing categories. It constructs no new Hom,
module-sheaf category, scalar localization, or derived category. All fourteen
public declarations are listed in `lean.declarations`. This repair adds the definition
node `def-sf-rational-term-hom-data`, bound with `existing: true` to twelve existing
definitions. There are no dependency-module repairs or new Lean declarations.

This repairs the independent stage-2 return of immutable head `4350f9693de0`,
H2/B3: a theorem node did not own the definitions used in the statement. The
comparison theorem is removed from `stmt_deps`, retained in `proof_deps`, and
replaced by the new definition owner. The mathematical Lean statement and the
reviewed interval correction are retained. The stage-1 review by Q127 is retained
verbatim; it is not stage-2 completion.
The provided `CompactObject.lean` example is now a withdrawn module with no
remaining declarations; its node and the current live statement modules supplied
the record/header conventions instead.

The source readings were Stacks `sites-cohomology.tex`, Section 0A8X (Hom product,
its exact differential and bifunctoriality), Lemma 08JI (finite-free summands and
comparison with an injective model), and Lemma 08JJ (degree-reversed finite
projective dual); the current blueprint `prop-sf-dualizable.proof.md`; and every
step of the item's reviewed fraction/zero-defect proof. The strictification
argument is explicitly agent-written, not a claim that Stacks states it.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small site | `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`. This is the common large-universe skeleton convention, with arbitrary explicit `u`. |
| Commutative coefficient ring and scalar | `(A : Type v) [CommRing A] (t : A)`; `v` is independent of `u`. No assumption that `t` is nonzero or regular. |
| Sheaf of commutative A-algebras | `(R : Sheaf J CommRingCat.{u})` and `(a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))`. The compatible global section homomorphism is exactly the unital algebra action on every section, compatible with restrictions. |
| Canonical A-linearity | Each scalar-dependent theorem is explicitly instantiated at `scalarLocalizationCoefficientLinear A R a`. The instance lambda is applied to this prescribed datum; it is not an arbitrary linearity assumption. Derived linearity is induced by the existing derived-category instance used by `RationalTermHom.localizedMap`. |
| Module sheaves, complexes and D(R) | `Modules R` is the recorded `ringedSiteModules`, `Complex R` is `CochainComplex (Modules R) ℤ`, and `[HasDerivedCategory.{w} (Modules R)]` selects the size convention for the already-existing `DerivedCategory`. |
| Raw scalar localization and its Q^0 | `ScalarLocalization A (Modules R) t` and `ScalarLocalization.localization A (Modules R) t`, with the recorded tensor-Hom category and localization functor. |
| Any bounded localized complex | `bounded_localized_complex_lift` quantifies over every `Pbar : CochainComplex (ScalarLocalization A (Modules R) t) ℤ` and every `a₀ b₀ : ℤ`, with `∀ q, q < a₀ ∨ b₀ < q → IsZero (Pbar.X q)`. |
| Actual integral bounded lift | The existential `P : Complex R` has the same integral zero-support predicate. `∀ q, a₀ ≤ q → q ≤ b₀ → P.X q = (Pbar.X q).obj` retains precisely the objects on the interval. This is the correction explained below. |
| Localized chain isomorphism | `s : ((ScalarLocalization.localization A (Modules R) t).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ Pbar`. This is an isomorphism of actual complexes, not only an assertion about their cohomology. |
| Derived image isomorphism | `bounded_localized_complex_lift_derived` gives `Nonempty (rawDerivedObject ... (Q^0_* P) ≅ rawDerivedObject ... Pbar)`. It uses the actual `DerivedCategory.Q`, with explicit abelian/derived-category structure parameters for that raw localized category. These are implementation structures for the derived category mentioned in the node, not a torsion, finiteness, or projectivity restriction on Pbar; the chain lift theorem has no such parameters. |
| Canonical raw derived image | `rawDerivedObject` casts along uniqueness of zero morphisms (`Subsingleton.elim` on `HasZeroMorphisms`) before applying `DerivedCategory.Q.obj`. The raw localization's preadditive zero and an explicitly supplied abelian structure's zero need not be definitionally the same. The cast is canonical, changes neither terms nor differentials, and uses no postponed data theorem. |
| Localized finite-free presentations survive | For every degree and rank the final clause of the lift theorem takes the original raw localized maps `i,p` with `i ≫ p = 𝟙 _`, and asserts `(s.hom.f q ≫ i) ≫ (p ≫ s.inv.f q) = 𝟙 _`. The retractions themselves remain localized. |
| Chosen numerators may have torsion defects | There is no hypothesis on numerator differentials or on their composites. The proof docstring records multiplying the numerators by a common annihilating power and the explicit scaling components. |
| Any actual bounded P, with ranks m_r | The main theorem quantifies over every `P : Complex R`, `a₀ b₀ : ℤ`, and `m : ℤ → ℕ`, requiring integral zero support, and `m r = 0` outside the interval. The latter implements “taking m_r=0 outside”, without restricting the in-interval ranks. |
| Degreewise retractions in D(R)[1/t] | For each `r` in the interval there exist maps between `RationalTermHom.localizedObject ... (single R (P.X r))` and `localizedObject ... (single R (free R (m r)))` with `i ≫ p = 𝟙 _`. `free R m` is precisely the existing `SheafOfModules.free (ULift (Fin m))`, also for m=0. These are not assumed integral or chain splittings. |
| Fixed K-injective j | `(I : Complex R) [I.IsKInjective] (j : RationalTermHom.single R (RationalTermHom.coefficients R) ⟶ I) [QuasiIso j]`. Thus j really is a quasi-isomorphic resolution of R[0], not any arrow to an injective object. |
| D and T | `dual R P = homComplex P (single R (coefficients R))` and `resolvedDual R P I = homComplex P I`, the recorded product Hom construction. The coefficient object is the existing regular module sheaf. |
| Surviving projections identify the dual terms | `dualProjection R P q` is exactly `RationalTermHom.projection` at `(q,-q,0)`, followed by postcomposition with `singleObjXSelf.hom`. The first pointwise assertion is `∀ q, IsIso (dualProjection R P q)`. The module also states `Nonempty (DerivedCategory.Q.obj (dual R P) ≅ DerivedCategory.Q.obj (signedSheafDualComplex P (coefficients R)))`, so the identification is explicitly present in derived form as required by the October 21 convention. |
| Correct signed differential | `(dual R P).d q (q+1) ≫ dualProjection R P (q+1) = dualProjection R P q ≫ ((q+1).negOnePow • homObjMap (P.d (-(q+1)) (-q)) (𝟙 _))`. This is exactly (-1)^(q+1) times precomposition with d_P^(-q-1), using the specified projections. |
| Dual degree bounds | `∀ q, q < -b₀ ∨ -a₀ < q → IsZero ((dual R P).X q)`. |
| Dual terms are localized retracts of the specified same free rank | For every q there exist maps from the localized single of `(dual R P).X q` to the localized single of `free R (m (-q))` and back, with composite the identity. This includes all degrees outside the interval. |
| Every single-term comparison is invertible | `∀ r, IsIso (RationalTermHom.localizedMap R A t (RationalTermHom.comparison R e j (P.X r)))`, with `e` existentially supplied and required to satisfy the existing `RationalTermHom.IsNormalized`. Its formula is normalized ordinary Hom identification followed by postcomposition with the very same j. |
| Actual c_P is postcomposition | The definition `postcompose R P j` is `((homComplexFunctor (R := R)).obj (op P)).map j`; its type is an actual chain map from D to T. |
| Contravariant chain-map naturality | `postcompose_natural` states `dualMap R f ≫ postcompose R P' j = postcompose R P j ≫ resolvedDualMap R I f` for every `f : P' ⟶ P`, even without boundedness. Both precomposition maps are defined by the existing Hom bifunctor. |
| Module-map naturality of the single-term comparison | The second conjunct after normalized e is the existing ordinaryMap/comparison/resolvedMap square for every module map f. |
| A[1/t]-linear extensions and all-fraction naturality | The final existential maps `b F G` and `z F G` are `→ₗ[Localization.Away t]` maps on the actual localized Hom modules of degree-zero derived objects. The first clause fixes their values on every image of a module map; the second is their naturality square for every localized morphism, not just those images. |
| Bounded ordinary dual before invertibility of Q_t(c_P) | All conclusions concern D's support and terms or the single-term comparisons. No theorem asserts invertibility of the localized total postcompose chain map. |

Dependency declarations used, with their signatures and docstrings read in the
listed sources:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the recorded
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the present statements use its
  already-exported Grothendieck-topology/sheaf convention, without assuming all
  pullbacks or choosing a separate precoverage.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the exact existing `SheafOfModules` category.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, specializing
  the complete integer cochain shape and its chain maps.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`. The size-convention node is a
  convention, not a missing definiendum; u, v, w and z are explicit universes.
- `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplex` and `homComplexFunctor`, including the specified
  product differential and bifunctoriality.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, read for the K-injective
  interpretation of Hom(P,I); its module is retained as a dependency import.
- `Sheaf.CategoryTheory.ScalarLocalization`:
  `CategoryTheory.ScalarLocalization`, `.localization`, `.category`,
  `.preadditive`, `.localizationAdditive`, `.linear` and `.linearOriginal`.
- `Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions`:
  `CategoryTheory.scalarLocalizationCoefficientLinear` and
  `scalarLocalizationDerivedLinear`. The exact A-action is the global-section
  action restricted along a, not a free choice of linear structure.
- `WeilConjectures.Algebra.Homology.HomComplexToSingle`:
  `CategoryTheory.signedSheafDualComplex` and `homComplex_to_single_iso`.
- `Sheaf.Algebra.Homology.RationalTermHomComparison`:
  `CategoryTheory.RationalTermHom.single`, `coefficients`, `ordinary`, `resolved`,
  `projection`, `ordinaryMap`, `resolvedMap`, `IsNormalized`, `comparison`,
  `localizedObject`, `localizedMap`, `rational_term_hom_comparison`. Their exact
  normalized interface is used; no replacement comparison or retraction is
  introduced. The new `def-sf-rational-term-hom-data` owns these definitions;
  `rational_term_hom_comparison` is the main proof input only.
- `Mathlib.RingTheory.Localization.BaseChange`:
  `LocalizedModule.equivTensorProduct`, `IsLocalization.Away.tensorEquiv` and
  `tensorRightEquiv` (the recorded Mathlib match for
  `lem-weil-pbc-localization-tensor`).
- `Mathlib.Algebra.Module.LocalizedModule.Basic`:
  `LocalizedModule.Away`, `mkLinearMap`, `IsLocalizedModule.eq_iff_exists` for the
  existing fraction interpretation and its torsion zero criterion.

The gained statement dependencies are existing landed nodes for the signed dual,
the prescribed coefficient actions, and the new definition owner for the existing
normalized rational-term interface. No existing dependency has been modified. The earlier stmt_deps are retained. There is no cycle:
the rational-term comparison does not use this bounded-presentation theorem.

Edge cases checked mathematically before writing:

- a>b: all input localized terms are zero objects; the integral zero complex
  works and equality on [a,b] is vacuous. The dual support is empty too.
- a=b: no differential denominators or successive defects occur; both maxima
  are zero. Single-degree signs and retractions still apply.
- m_r=0: the localized term is a retract of the zero free sheaf; it is zero
  after localization, without implying its integral underlying sheaf is zero.
- t=1: ordinary localized arrows have denominator one; the construction reduces
  to the original complex on the interval.
- t=0 or nilpotent: the raw localized category is zero; outside support an
  underlying integral sheaf can be nonzero, which forces the recorded correction.
- Genuine nonzero torsion defects are permitted. For Z-modules
  P^0=Z, P^1=Z, P^2=Z/2 with successive numerator maps identity and reduction,
  the composite is nonzero integrally but zero after inverting 2. Multiplying
  both numerators by 2 kills this defect; no integral square-zero numerator
  hypothesis has been smuggled into the statement.
- Negative degrees: r=-q and -(q+1)=-q-1 give the stated sign. q=0 gives minus
  precomposition, q=1 gives plus, matching the Hom differential convention.
- Zero coefficient ring, empty site, zero P and arbitrary unbounded I require
  no nonemptiness, nontriviality, or boundedness hypothesis beyond the node's.

Searches actually run in this worker, through msearch.py with this group/item:

- LeanFinder query: “A bounded complex in a scalar localized linear category
  admits an integral complex lift after clearing denominators and killing torsion
  defects”. Eight results, chiefly bounded derived replacement/roof results such
  as `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` and
  `DerivedCategory.left_fac_of_isStrictlyLE_of_isStrictlyGE`. None lifts a raw
  scalar-localized complex with torsion defects.
- Loogle query: `"CochainComplex", "Localization"`. Two results:
  `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp` and
  `HomotopyCategory.Plus.instIsLocalizationPlusInjectiveObjectQuotientInverseImageQuasiIsoMapCochainComplexPlusι`.
  These construct localization functors; neither states the lift or signed dual.
- Mathlib grep query: `strictif|clear.*denom|localized.*complex`, restricted to
  `Algebra/Homology`. Six hits, all on localized shifted Hom or the derived
  category definition. No exact match.
- LeanSearch query: “A bounded cochain complex in a scalar localized category
  lifts to an integral complex by clearing differential denominators and killing
  torsion defects”. Eight results: bounded derived representatives, ConnectData,
  injective resolutions, CM5b and mapping-cone lift formulas. No exact match.
- `rg` on both `lean/Sheaf` and `lean/WeilConjectures` for
  `localizedSigned|localized_signed|strictif|clear.*denom`, and for the exact node
  id in `WeilConjectures`, found no existing declaration of this node. The signed
  dual and Hom-to-single modules, and the existing RationalTermHom comparison,
  were found by semantic names and read/reused. Other denominator-clearing and
  site strictification results address different notions.
- DAG grep found both citers and the item. A search for an abelian interface for
  ScalarLocalization found no such declaration; the derived-image corollary
  consequently treats the raw category's abelian/derived structures explicitly
  and transports its unique zero morphisms, with no fabricated instance.

Validation: `scompile.py NN lem-sf-localized-signed-dual-presentation` compiled
both its sandbox projection and its actual module name cleanly (10.5 s and
12.0 s). Auto implicits are disabled; every universe is declared; no diagnostics
or local instance/notation/private declarations remain. All four theorem proofs
are `sorry`, as required for this stage. All definitions have real data.

## Statement corrected

The old statement, verbatim:

Let $\mathcal C$ be a small site, $A$ a commutative ring, $t\in A$, and $R$ a sheaf of commutative $A$-algebras. Use sheaves of $R$-modules, their derived category $D(R)$, and the scalar localization $Q_t:D(R)\to D(R)[1/t]$ [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category, def-weil-linear-scalar-localization], in the universe of [def-weil-size-convention]. Write $\mathcal M=\operatorname{Mod}_R(\mathcal C)$ and $Q_t^0:\mathcal M\to\mathcal M[1/t]$ for raw scalar localization of this $A$-linear module-sheaf category. Every cochain complex $\overline P$ in $\mathcal M[1/t]$ that is zero outside $[a,b]$ admits a cochain complex $P$ in $\mathcal M$, zero outside the same interval and with the same underlying module objects, and a chain isomorphism $(Q_t^0)_*P\cong\overline P$. In particular their images in the derived category of $\mathcal M[1/t]$ are isomorphic. Localized finite-free-retract presentations of the terms are preserved by this identification; no lift of the retraction maps themselves is required. This assertion allows nonzero $t$-power-torsion defects in chosen numerators of successive localized differentials.  For an actual $P$ as above, or any cochain complex $P$ of $R$-module sheaves, zero outside an integer interval $[a,b]$. Suppose that for each $r\in[a,b]$ there are $m_r\geq0$ and morphisms $i_r:Q_t(P^r[0])\to Q_t(R^{\oplus m_r}[0])$ and $p_r:Q_t(R^{\oplus m_r}[0])\to Q_t(P^r[0])$ with $p_ri_r=1$. These are degreewise localized retractions; no integral or chain-level splitting is assumed. Fix a K-injective resolution $j:R[0]\to I$ [def-pur-derived-internal-hom], and set $D=\mathcal Hom_R^\bullet(P,R[0])$, $T=\mathcal Hom_R^\bullet(P,I)$ [def-pur-hom-complex]. Then the surviving Hom projections identify
$$D^q=\mathcal Hom_R(P^{-q},R),\qquad d_D^q(\phi)=(-1)^{q+1}\phi\circ d_P^{-q-1},\qquad D^q=0\quad(q\notin[-b,-a]).$$
For every $q$, $Q_t(D^q[0])$ admits a retraction from $Q_t(R^{\oplus m_{-q}}[0])$, taking $m_r=0$ outside $[a,b]$. For each $r$, postcomposition with $j$ gives an isomorphism
$$Q_t\bigl(\mathcal Hom_R(P^r,R)[0]\bigr)\xrightarrow{\sim}Q_t\bigl(\mathcal Hom_R^\bullet(P^r[0],I)\bigr).$$
The actual chain map $c_P:D\to T$ is postcomposition with $j$, natural contravariantly under chain maps in $P$; the single-term comparisons are natural under module maps and their $A[1/t]$-linear extensions. In particular, $D$ is a bounded complex with the allowed localized finite-free-retract terms, before any assertion that $Q_t(c_P)$ is invertible.

The phrase “with the same underlying module objects” cannot hold outside [a,b].
Take the one-point ringed site with A=R=Z and t=2, a complex with Z/2 in degree 2
and zero differentials, and [a,b]=[0,0]. Its degree-2 term is a zero object after
scalar localization but nonzero integrally. A lift zero outside [0,0] cannot keep
that integral term. The reviewed Q127 proof already chooses zero integral terms
outside the interval and keeps the original objects only inside it. The corrected
phrase states exactly that construction. The current blueprint's opening local
bounded-model sentence is unchanged, as is the unit's proof route. This is the
item's agent-written extension, not a correction of a blueprint unit statement.

The statement_change record has the complete base-citer audit:

- `lem-sf-coefficient-dual-model-transport`: holds true. Its cited step transports
  the localized chain isomorphism by an exact coefficient functor and retains
  support. It uses no equality of original integral objects outside the interval.
- `prop-sf-dualizable`: holds true. It uses an actual bounded lift with the same
  rational retract terms and its signed dual; these are unchanged. Its step
  never requires nonzero integral torsion terms to be retained outside support.

No citer was edited. `statement`, `stmt_deps`, `statement_change` and `lean` are
the only changed fields of the item's node; proof and proof_deps are unchanged.
The added dependencies expose already-landed notions in the statement, including
the new definition owner; old_stmt_deps preserves the original dependency list. There is no unresolved STATEMENT-DISPUTED flag.

## New nodes

`def-sf-rational-term-hom-data` defines the degree-zero single, regular coefficient
module, ordinary and resolved Hom complexes, their precomposition maps, chosen
product projections, normalized-identification predicate, postcomposition
comparison, and scalar-localized objects/maps. Its `existing: true` record names
the twelve definitions in `Sheaf.Algebra.Homology.RationalTermHomComparison`;
nothing is copied or redefined. The source is Stacks 0A8X/08JI and the
agent-written scalar-localized local-dual extension of the current blueprint.
The primary signature `comparison` is copied verbatim from the existing source.
The live source was also read using `scompile.py --source`.

Searches for this new node: LeanSearch on normalized internal Hom comparison
returned external injective resolutions, Ext and sheaf-map constructors (8 hits);
LeanFinder on degree-zero sheaf Hom, projection normalization and postcomposition
returned unit/free sheaf Hom equivalences and sheafification (8 hits). Neither
provides this internal-Hom data package. Mathlib grep
`homComplex|homObjMap|singleObjXSelf` in `Algebra/Homology` returned 25 hits on
external Hom complexes and single-degree identifications. Project rg found the
exact definitions in `RationalTermHomComparison`, no corresponding upstream
`WeilConjectures` name or `dag/lean_names_upstream.json` entry. DAG rg on the
fully qualified definitions found only the theorem node, not a definition owner.
Blueprint searches `rational term Hom` (0 results) and `Hom complex` (3 unrelated
results: K-injective bridge, categorical trace, closed-support-stratum Hom) found
no blueprint definition of this package. The new node therefore records existing
project definitions, with `mathlib_match: null`; all three actual msearch records
are retained in its `mathlib_searches` and the sandbox search log.

Clause correspondence for the definition node:

- Small site, coefficient ring sheaf and modules: explicit source variables
  `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}` and
  `(R : Sheaf J CommRingCat.{u})`; `ringedSiteModules` gives the module category.
- `S(F)` and the regular module: `single` and `coefficients` use the existing
  `HomologicalComplex.single` and `SheafOfModules.unit`.
- `B(F)` and `T_I(F)`: `ordinary` and `resolved`; the former is the single
  internal Hom sheaf, the latter the existing Hom-complex bifunctor.
- Precomposition maps: `ordinaryMap` is the single of `homObjMap f (𝟙 _)`;
  `resolvedMap` is the first-variable bifunctor map at the very same `I`.
- Product projections and their degree-zero specialization: `projection` and
  `zeroProjection`. `ProjectionData.eq_chosen` fixes the already-selected
  projection family; `projectionData_exists` is proved in the existing source.
- Normalization: `IsNormalized` is precisely the displayed degree-zero equation
  with `singleObjXSelf.hom` on the source and its inverse on the target.
  It asserts no existence of a normalized family.
- Postcomposition: `comparison R e j F` composes `(e F).hom` with the second
  variable map of the Hom bifunctor at the specified `j`. It does not require
  K-injectivity, a quasi-isomorphism, or invertibility of that comparison.
- Scalar action and localized images: `localizedObject` wraps `Q.obj K`;
  `localizedMap` is exactly `TensorProduct.tmul A 1 (DerivedCategory.Q.map f)`.
  The item supplies the canonical action `scalarLocalizationCoefficientLinear`;
  derived linearity and scalar localization use the recorded existing interfaces.

Edges of the new definition node go only to pre-existing definition nodes, never
to the comparison theorem or to this item. Its blueprint ancestor is
`prop-sf-dualizable`, with via `[lem-sf-localized-signed-dual-presentation]`.
Edge cases: zero coefficient ring, empty site, zero module, arbitrary/unbounded
`I`, arbitrary `j`, and `t=0,1` are permitted by all definitions. No normalized
family is chosen and no denominator is inverted inside the integral comparison.

## Second reading by NN

Author self-check of the repair; the maintainer supplies the independent review.
I reopened the new node, the exact existing definitions and docstrings, the item
node, and the saved Lean statement. The twelve existing definition names cover
every `RationalTermHom` name used by the item, including `projection` (not listed
in the old theorem node's declaration inventory) and the normalization helper
`zeroProjection`. The item still quantifies over the normalized family itself,
so it needs only those definitions to state its conclusion. The theorem's
existence/isomorphism result is used by the planned proof and remains in
`proof_deps`. This is the exact H2/B3 repair requested for head `4350f9693de0`.
The integral lift, sign, support, rank retractions, resolution, naturality and
all-fraction comparison clauses remain verbatim in the saved Lean file.
The previous correction and its two-citer audit are unchanged. The initial saved
packet dry run passed at `bef83c32390`; that pre-repair result is not claimed as
validation of the newly added definition record.

Repair validation (2026-10-22): the explicit `scompile.py NN
lem-sf-localized-signed-dual-presentation` invocation compiled the retained
module both in the private sandbox (10.5 s) and under its actual library name
(12.0 s), without errors or unexpected warnings. The repaired packet dry run
passed preflight and compilation at `576341a6549`, staging exactly the report,
item node, new definition node and retained Lean module. A scripted self-check
confirmed coverage of every used `RationalTermHom` definition, verbatim primary
theorem signature, 100-character Lean line limit, unchanged proof/proof_deps, and
`old_stmt_deps` identical to the current base. No source or launcher file was
modified, and no direct git command or global build was run.
