## Worker report

Statement module: `Sheaf.Paper.IntegralGeneralLfpSequentialContinuity`, main declaration `AlgebraicGeometry.ProEtale.IntegralSequentialContinuity.integralGeneralLfpSequentialContinuity`. There is one postponed theorem, with the six-step natural-language proof in its docstring. The five supporting declarations are transparent aliases of the existing module category and derived Hom, the explicit canonical colimit comparison, and the actual repeated-scalar diagrams. They introduce no independent notion, no replacement coefficient ring, and no postponed data.

The live node has a stage-1 acceptance from Q112 and no Lean binding. The previous reported rejection conflated that split with this stage-2 task; this packet supplies the missing Lean statement. No repair note exists for the item. The natural-language statement and all six proof steps are preserved. The returned H2 dependency fault is repaired: `lem-sfb-integral-lfp-constant-model-comparison` is removed from `stmt_deps` and remains a proof dependency. The new definition node `def-sfb-integral-condensed-ring` owns the transparent specialization used in the signature, with its canonical multiplication and commutativity structures. No dependency node is changed.

Hypotheses and clauses, matched to the Lean:

| Node text | Lean rendering |
| --- | --- |
| A prime ell | `l : ℕ` and `[Fact l.Prime]` |
| A finite field extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]` |
| R = O_E with its valuation topology | Existing `integralCondensedCoefficientRing l E`; it is the continuous-function condensed ring on `latticeCoefficientIntegers l E`, the valuation-topology type synonym of the recorded ring of integers |
| X locally Noetherian and quasi-compact | `X : Scheme.{u}`, `[IsLocallyNoetherian X]`, `[CompactSpace X]` |
| Small pro-etale site; B = p_X^* underline(R) | `Scheme.ProEt.topology X` and `condensedRingObj (integralCondensedCoefficientRing l E) X` in `Modules` |
| Ordinary unbounded D(B) | `DerivedCategory (Modules l E X)`, using the existing native derived-category instance, without completion |
| H_B = derived internal Hom | `hom l E X K` is exactly `(CondensedRing.derivedHom (integralCondensedCoefficientRing l E) X).obj (op K)` |
| K has bounded general-ring-object constructible cohomology, arbitrary section-valued presentation entries | `_hK : boundedConstructible (condensedRingObj (integralCondensedCoefficientRing l E) X) K`; its general predicate is `IsConstructibleModuleObject`, rather than constant-model constructibility or perfectness |
| Descending chains of closed subsets stabilize | Conclusion `TopologicalSpace.NoetherianSpace X`; Mathlib identifies this with well-founded strict inclusion of closed subsets |
| Each cohomology module has a finite constructible stratification with finite scalar local models | Conclusion `∀ q : ℤ, IsConstantModelConstructible (integralCondensedCoefficientRing l E) X ((DerivedCategory.homologyFunctor _ q).obj K)`; on this qcqs X the recorded predicate is precisely `IsFiniteConstantStratified` |
| Torsion scalar modules, and degree-dependent stratifications, allowed | The existing finite-presentation predicate imposes no flatness, freeness, or torsion-free condition; the existential stratification is inside the quantifier over q |
| Exact small filtered colimits of module sheaves | Conclusions `HasColimitsOfSize.{u+1,u+1} (Modules l E X)` and `AB5OfSize.{u+1,u+1} (Modules l E X)` |
| Any sequential diagram with one common termwise lower bound | `M : ℕ ⥤ CochainComplex (Modules l E X) ℤ`, `c : ℤ`, and `∀ n q, q < c → IsZero ((M.obj n).X q)` |
| Functorial internal-Hom representatives | The conclusion supplies `∃ F, Nonempty (F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K)` and then quantifies over every such F and identification e. Thus a representative model is supplied, not assumed to exist |
| Canonical evaluation-induced comparison is an isomorphism in D(B) | `IsIso (comparison l E X K F e M)`, where the actual map is `DerivedCategory.Q.map (colimit.post M F) ≫ e.hom.app (colimit M)` |
| Termwise exact sheaf-module colimits on both sides | Left object is `Q.obj (colimit (M ⋙ F))`; right object is `hom(K, Q.obj (colimit M))`. Colimits are in complexes, computed termwise in module sheaves, never ordinary categorical colimits of the derived category |
| Independence of representatives | For any two model functors F and G and a componentwise quasi-isomorphism `τ : M ⟶ N`, a unique isomorphism between their localized termwise Hom colimits makes the displayed square commute with `hom.map (Q.map (colimMap τ))`. Taking τ to be the identity compares any two Hom models. Arbitrary N is allowed, even without a termwise lower bound; zigzags follow by composition/inversion |
| No constructibility or completeness on targets | No such binders occur for M, N, L or C |
| Any representative C of any L with H^q(L)=0 below c | Arbitrary `L`, `C`, `eC : Q.obj C ≅ L`, `c : ℤ`, and only `L.IsGE c` |
| Good quotient truncation P, with specified terms and induced differentials | Exactly Mathlib `C.truncGE c`; its definition is zero below c, opcycles/cokernel of the incoming differential at c, C above c, and the induced differential |
| Scalar-equivariant quasi-isomorphism C to P | `QuasiIso (C.πTruncGE c)` and the explicit commuting equation with `l • 𝟙`; the map itself is a morphism of B-module complexes, hence B-linear |
| The repeated-ell sequence of P represents the scalar sequence of L | Existential natural isomorphism `tower l E X (C.truncGE c) ⋙ Q ≅ derivedTower l E X L`, normalized by `Q.map (C.πTruncGE c) ≫ a.hom.app n = eC.hom` for every n |
| The displayed continuity applies to that sequence | `(C.truncGE c).IsStrictlyGE c` and the final `IsIso (comparison ... (tower ... (C.truncGE c)))` clause |
| No further condition on L | No constructibility, completeness, upper bound, termwise bound on C, or Tor condition is assumed |

The representative parameter e does not replace the canonical map by an arbitrary arrow. It identifies an actual complex-valued representative with the already fixed derived internal Hom. Naturality and the formula for `colimit.post` give, for each n,
`Q.map (colimit.ι (M ⋙ F) n) ≫ comparison = e.hom.app (M.obj n) ≫ hom.map (Q.map (colimit.ι M n))`.
Under the existing tensor-Hom adjunction the right-hand legs are the evaluation transposes. All representative choices are conclusions/universal choices of the same object, and the comparison itself is explicitly constructed. The independence square concerns these actual maps.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: publicly retains the recorded `Padic.coefficientExtensionAbsoluteValue`, `Padic.coefficientExtensionIntegers` and coefficient extension constructions.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`, `IsNoetherian`, and the underlying Noetherian-space instance. The proof dependency `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` has no Lean record yet; no invented import is attached to it.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, available through the direct Noetherian import.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`; publicly available through the existing framework imports.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` and its continuous coefficient exports.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`, `condensedRingObj`, and the actual monoidal inverse image from the point.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`; the native existing Grothendieck instance fixes the morphism universe.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: `CondensedRing.derivedHom` and `derivedTensorHomAdjunction`.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`: publicly retains the exact general `boundedConstructible` and `mem_boundedConstructible_iff`. Its discrete-coefficient specialization is not used.
- `Sheaf.Paper.CondensedConstantConstructibility`: `IsConstantModelConstructible`, `IsFiniteConstantStratified`, `HasFiniteConstantLocalModel`.
- `Sheaf.Paper.IntegralCondensedCoefficientRing`: `integralCondensedCoefficientRing` and its canonical `MonObj`/`IsCommMonObj`, owned by `def-sfb-integral-condensed-ring`; public statement import.
- `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingObjOfUniverse` and its two canonical structures, owned by `def-sfb-continuous-map-condensed-ring`.
- `Sheaf.Paper.LatticeSheafBasic`: `latticeCoefficientIntegers`, owned by `def-sfb-continuous-lattice-coefficients`, with the canonical valuation topology.
- `Sheaf.Paper.IntegralLfpConstantModelComparison`: `integralLfpConstantModelComparison`; ordinary proof import only, for proof step 2.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.cocone`, `colimit.post`, `colimMap`.
- `Sheaf.Paper.ConstructibleInternalHomContinuity`: `constructible_internalHom_continuity`; proof import only. Its cohomology-cocone formulation is used in the proof plan to establish the derived isomorphism, rather than substituted for that isomorphism in this statement.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`: `SheafOfModules.grothendieckAbelian_with_localized_generator`; proof import only, used through the existing exact internal/section-module equivalence.
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`: `truncGE`, `πTruncGE`, `quasiIso_πTruncGE_iff`, and the actual cokernel/extension construction. These implement exactly good truncation, not stupid truncation.

Edge cases checked before writing: the empty scheme; K zero; a single cohomology degree; integral torsion models R/(varpi), zero presentations, and free models; constant and zero sequential diagrams; arbitrary negative cutoff c; C already termwise bounded below; C with a nonzero acyclic tail below c; and the two boundary degrees c and c+1 of good truncation. The construction at c is a cokernel, not a kernel. The target scalar is ell, not a unit or an invertibility hypothesis. Both the identity representative change and arbitrary componentwise quasi-isomorphisms are retained. Schemes and coefficient fields range over `Type u`, module morphisms over `u+1`, and small filtered diagrams over `u+1`; the sequence itself has the usual small natural-number index. There is no equality of site object and morphism universes.

Searches for an existing statement:

- `msearch.py ... leanfinder "Derived internal Hom from bounded integral constructible complexes preserves sequential colimits and canonical quotient truncation gives bounded below representatives"`: eight hits, including `DerivedCategory.exists_iso_Q_obj_of_isGE`, its bounded variant, and `isGE_Q_obj_iff`. These are generic representative facts, not the integral continuity statement or its full clauses.
- `msearch.py ... loogle "CochainComplex.truncGE, CochainComplex.πTruncGE, colimitComparison"`: no hits because the last identifier does not exist; not used as negative evidence about truncation.
- Corrected `msearch.py ... loogle "CochainComplex.truncGE, CochainComplex.πTruncGE"`: eleven exact truncation/projection hits, including `quasiIso_πTruncGE_iff`, used via the existing construction.
- `msearch.py ... grep "truncGE|πTruncGE" Algebra/Homology/Embedding`: 25 hits, identifying the precise canonical construction and functoriality.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and general-lfp/sequential-continuity names: no existing declaration of this item. The existing `IntegralGeneralLfpHomInversion` is its downstream consumer, not the continuity statement; `IntegralLfpHomContinuity` and `IntegralConstructibleSequentialHom` concern different global-Hom statements. The more general `ConstructibleInternalHomContinuity` is reused as a proof dependency and has different source hypotheses and no full truncation/scalar-tower assertion.
- Direct source reads followed each dependency record and every relevant matching declaration and docstring. Read Bhatt--Scholze pp. 60--61 and HRS Theorems 4.13, 6.2 and the local-model discussion; read Mathlib's full good-truncation construction. The source distinction already in the node is retained: BS 6.8.12 states global direct-sum continuity; internal-sheaf sequential continuity and the general-lfp bridge are the separate explicit extracted obligations, not claimed verbatim from that lemma.

No mathematical statement correction, dependency replacement, or statement dispute is required. The one new definition node repairs the returned H2 ownership fault. The only `sorry` is the main theorem; all definitions have complete data. Compilation through the prescribed `scompile.py` succeeded in both sandbox and library modes, with no errors or warnings. The first compiler pass found the nonexistent name `colimit.map`; this was repaired to Mathlib's existing `colimMap` before the successful pass.


## New nodes

`def-sfb-integral-condensed-ring` specializes the existing continuous-map condensed ring
of `def-sfb-continuous-map-condensed-ring` to the canonical valuation-topology integers
of `def-sfb-continuous-lattice-coefficients`. Source: HRS Example 3.1, read directly in
the local PDF, including the explicit continuous-function formula and rings-of-integers
examples. Its prime, finite-extension, valuation-topology, sections, restrictions,
pointwise multiplication and commutativity clauses are rendered by the explicit binders,
`latticeCoefficientIntegers`, `continuousMapRingObjOfUniverse` and its exact two
canonical structures. No theorem proof or arbitrary choice supplies data. The new name
does not clash with the earlier theorem-module helper; both unfold to the same existing
construction with the same structures, so this changes no coefficient object.

Fresh searches: LeanSearch for "condensed ring of continuous functions into the valuation
ring of a finite extension of the p-adic numbers" returned eight generic continuous-map,
valuation-topology and p-adic hits; none owns this specialization. Loogle for
`Profinite.continuousMapRingObj, PadicInt` returned an unknown-identifier diagnostic
(no negative inference is drawn from that diagnostic). Mathlib grep for
`condensed|Condensed` under `NumberTheory/Padics` returned zero hits. Project/DAG `rg`
and `blueprint_refs.py search 'integral condensed ring'` found the generic constituent
definition nodes and the existing theorem-owned helper, but no definition node owning
this specialized ring; the bundled-scalar and integral-quotient nodes include different
notions. The searches are recorded as returned in `mathlib_searches`. This specialization
is exactly the non-clashing definition-node repair requested by the maintainer.

## Second reading by Q27

Repair self-check (the maintainer supplies the independent reading): reopened both node
records and both Lean files. The original theorem's prime, finite extension, qc/locally
Noetherian scheme, bounded general constructibility, DCC, finite scalar local models,
AB5, all representative-existence/independence clauses, canonical comparison and good
truncation/scalar-tower conclusions remain as matched in the table above. The only
signature change is the definitionally identical coefficient-ring name. Checked the new
node's two cited definition dependencies against their actual constructions and the HRS
source; its ring and instances have real data and introduce no additional hypothesis.
The original theorem node's natural-language statement and proof are unchanged. Removed
the rejected theorem from statement dependencies and made its import proof-only.
