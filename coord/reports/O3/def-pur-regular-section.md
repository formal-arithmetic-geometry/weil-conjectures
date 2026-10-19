## Worker report

Repair of the returned immutable packet `3e45b5d1b9b8`, H3 and H11. The saved report and module
were inspected first and the prescribed initial dry run was run. Its concrete failure was a
`lean.statement`/file-signature mismatch after the replacement interface was written; the
record now reproduces the new signature verbatim. The sandbox node's non-`lean` fields have
been compared with current main and are identical. No statement correction, new node, or
dependency repair is needed.

`Sheaf.Paper.PurityRegularSection` now starts with an actual locally free module `F` and a global
section `s : F.sections`. It defines evaluation using the existing ordinary sheaf-Hom bidual
map. It applies the existing vector-bundle construction to **the dual of F**. The geometric
section is chosen from a **unique** affine characterization by the evaluation ring map, which
determines the actual morphism over T. This is the unique-object construction allowed by the
contract, not a choice from bare existence or `Nonempty`.

The old module took an arbitrary chosen bundle and map to it, and replaced actual component
germs by unrelated regular sequences. Those defects are removed. `IsRegularSection` now uses
a local affine frame of the given `F` and its actual component germs. `IsTransverseDirectSum`
uses two actual frames and the concatenation of their component lists, as well as the stated
regularity of both summands. The evaluation ideal, closed immersion, polynomial and quotient
charts, section correspondence, rank-zero case, sectionwise direct sum, and canonical over-T
comparison with the scheme-theoretic intersection are all present.

Every definition has real data. The symmetric-algebra extension is chosen using the existing
unique universal property. The geometric section and direct-sum comparison are chosen using
named unique-characterization theorems, each with its complete mathematical proof in its
docstring. All new theorem proofs are `sorry`, as required in stage 2. They state the explicit
clauses of this node; no independent unstated theorem or new mathematical notion is assumed.

## Complete clause audit (H11 repair)

This audit replaces the earlier incomplete claim that no mismatch was found. The node and
replacement module were read together. Names below are in namespace `AlgebraicGeometry`.

| Node hypothesis or clause | Lean rendering and audit result |
| --- | --- |
| Fixed finite-field purity setting | Section binder `P : WeilConjectures.PurityFiniteSetting.{u}`; the base field is `P.field.k`. |
| T is a separated finite-type k-scheme | `T : Scheme.{u}`, `hT : T ⟶ Spec (CommRingCat.of P.field.k)`, and `[IsSeparated hT] [LocallyOfFiniteType hT] [QuasiCompact hT]`. The recorded bundle dependency takes the explicit structure map, so this encoding follows that interface. |
| F is locally free of constant rank r, allowing r=0 | `F : T.Modules`, `r : ℕ`, `[F.IsFiniteLocallyFreeOfRank r]`. No positivity assumption. |
| Ordinary Zariski sheaf dual, with sections the linear maps on the localized site | `Scheme.Modules.dual F`, the existing abbreviation for `SheafOfModules.homObj F (SheafOfModules.unit _)`. The existing `homObj` definition uses morphisms of restricted module presheaves; its sheaf theorem is already supplied upstream. |
| A frame gives the dual frame by coordinate projections on any open U | The real construction `regularSectionDualFrame F r U e` composes `overHomObjIso`, contravariant transport through `e`, and `homObjFreeUnitIso`. `regularSectionDual_rank` records the resulting constant rank. `regularSectionPolynomial_coordinates` additionally states the Kronecker-delta equations on affine frames. |
| E(F) is Spec_T Sym(F dual), not Sym(F) | `regularSectionBundle P T hT F r` has `𝓔 := Scheme.Modules.dual F`, canonical `VectorBundleZeroSection.scheme` and projection, `phi := Iso.refl _`, and the derived dual-rank witness. The Noetherian instance comes from `isNoetherian_of_locallyOfFiniteType hT`, not an extra assumption. |
| Canonical projection p and zero section z | The fields and `zeroSection` of the constructed `PurityVectorBundle`; the existing zero-section specification gives the augmentation, section identity, affine formula, and closed immersion. |
| A section is an element of Gamma(T,F) | `s : F.sections` is a compatible family on all Zariski opens. Since the opens category has terminal object top, this is exactly F(T), not an additional section datum. |
| ev_s(lambda)=lambda(s restricted to U) | Definition `regularSectionEvaluation F s` uses `sectionsMap (SheafOfModules.bidual F)` and `homObjSectionsEquiv`. `regularSectionEvaluation_apply` states the formula at `Over.mk (𝟙 U)` for every open and every dual section. |
| Unique algebra map extending ev_s | `regularSectionAlgebraMap T F s` is chosen from `exists_quasiCoherentSymmetricAlgebra_core`. `regularSectionAlgebraMap_spec` states both the generator formula and uniqueness among all algebra maps with that formula. |
| Relative Spec gives the corresponding T-morphism | `regularSectionGeometric_existsUnique` characterizes a subtype of maps satisfying `f ≫ p = 𝟙 T`, on every relative-Spec affine chart, by `Spec.map` of `SymmetricAlgebra.lift` of evaluation. `regularSectionGeometric` is its unique choice. Thus the chart formula fixes the canonical algebra/Scheme variance. |
| Conversely a geometric section gives a section, with coefficients its values on the dual basis; overlap gluing | `regularSectionGeometric_bijective` states bijectivity of this specific canonical map. Its docstring gives the inverse construction in a frame, the evaluation characterization on overlaps, and gluing. `regularSectionPolynomial_coordinates` fixes the dual-basis coefficients explicitly; reconstruction is the existing basis `sum_repr` identity. |
| Z(s)=T times over E(F) with maps s,z | `regularSectionZeroScheme` is `pullback (regularSectionGeometric ... s).val (regularSectionBundle ...).zeroSection`. |
| The morphism Z(s) to T | `regularSectionZeroProjection` is the first pullback projection, fixing which T is used. |
| Its ideal sheaf is the image of evaluation | `regularSectionZeroIdeal` uses Mathlib `Scheme.Hom.ker`. `regularSectionZeroIdeal_spec` identifies membership in its ideal on every affine open with existence of a dual section evaluating to that element. These affine image ideals specify the quasi-coherent image sheaf, including on nonaffine T. |
| On an affine frame open, Sym(F dual) has polynomial coordinates | `regularSectionPolynomial_coordinates` gives the dual section basis `d` and the existing `SymmetricAlgebra.equivMvPolynomial d`, with its value on every degree-one generator. The sheafification-unit/affine comparison is inherited from the bundle construction and its `affineChart`. |
| The section sends x_i to a_i and zero sends x_i to 0 | The last two clauses of `regularSectionPolynomial_coordinates` state these two equations on the degree-one dual-basis sections, using `regularSectionAlgebraMap` and the existing augmentation. The geometric affine characterization and the existing zero-section chart formula transport them to the scheme maps. |
| A tensor over A[x_i] with A is A/(a_i) | `regularSectionAffineRing` states the isomorphism of the commutative-ring pushout of the evaluation and zero polynomial maps with `A ⧸ Ideal.span (Set.range a)`. The pushout is the tensor product with those two distinct algebra actions. Both inclusions become the quotient map, and the inverse sends a residue class to its first-factor inclusion, i.e. a tensor 1. |
| The tensor-to-quotient map sends a tensor b to ab, with inverse a-bar to a tensor 1 | The two projection equations in `regularSectionAffineRing` determine that multiplication map on products of the factor inclusions; its last equation specifies the inverse. The docstring verifies balancedness and both inverse identities, including the generator relations. |
| The zero scheme on U has quotient ring A/(a_i) over U | `regularSectionZero_affine` gives a scheme isomorphism of the inverse-image open with `Spec` of that quotient and its equation with the quotient closed immersion to U. The basis coefficients are exactly `b.repr (s.val (op U.1))`. |
| Its ideal is (a_i), also the image of evaluation | The affine quotient chart together with `regularSectionZeroIdeal_spec` and the coordinate equations. No arbitrary regular sequence is substituted for the actual coefficients. |
| Z(s) to T is a closed immersion | First conjunct of `regularSectionZeroIdeal_spec`; its proof docstring cites the affine-cover criterion and the quotient charts. |
| Regularity at each point of Z(s) in a local frame | `IsRegularSection` quantifies over `x : regularSectionZeroScheme ...`, then an affine open `U` containing its image, an actual `Module.Basis (Fin r) O(U) F(U)`, and `List.ofFn` of the germs of its actual coefficients. For a quasi-coherent locally free sheaf an affine section basis gives a sheaf frame, and every local sheaf frame can be refined to such an affine open, so the affine formulation is equivalent to the node's local-frame formulation. |
| Each component is a nonzerodivisor modulo predecessors; final quotient nonzero | The recorded Mathlib predicate `RingTheory.Sequence.IsRegular` on that very germ list. Its inherited `IsWeaklyRegular` gives successive injectivity and `top_ne_smul` gives the nonzero final quotient. |
| No smoothness of base or zero locus | No smoothness or regular-base instance is present. |
| Empty zero locus makes regularity vacuous | The definition has an empty point quantifier in this case; `regularSection_emptyZero` states it explicitly. |
| Rank zero: E(F)=T, unique section zero, Z(s)=T, empty sequence regular | `regularSection_rankZero` states that every section is `F.unitHomEquiv 0`, both the bundle projection and zero-scheme projection are isomorphisms, and `IsRegularSection` holds. Its docstring invokes the nonzero scheme stalk for the empty-list regularity condition. Scheme equalities in the node mean these canonical isomorphisms over T. |
| Second locally free module G of rank e allowing e=0 | `G : T.Modules`, `e : ℕ`, `[G.IsFiniteLocallyFreeOfRank e]` in the intersection and sum declarations. |
| s and t are regular | First two conjuncts of `IsTransverseDirectSum`. |
| Transverse means actual concatenated components in simultaneous frames | The third conjunct quantifies over an intersection point and one containing affine open, separate bases of F(U) and G(U), and regularity of the concatenation of their actual germ lists using `++`. There is no arbitrary length-(r+e) sequence. |
| Direct sum has sections F(U) direct sum G(U) | The finite product `F ⨯ G` is the finite direct sum in this abelian category. `regularSectionSum_sections` states bijectivity of the two projections on every open and identifies the projections of the paired section. `regularSectionSum` constructs the pair using `prod.lift` and `unitHomEquiv`; `regularSectionSum_rank` gives rank r+e. |
| Its zero scheme is the scheme-theoretic intersection | `regularSectionSumZeroScheme` uses the actual section of F direct sum G. `regularSectionIntersectionScheme` is separately the pullback of the two zero-scheme projections. `regularSectionSumZeroComparison_existsUnique` gives the unique isomorphism between them over T. |
| Comparison induced by projections and glues on overlaps | `regularSectionSumZeroComparison` chooses the uniquely determined over-T isomorphism, and `_spec` states its projection equation. Its existence/uniqueness proof docstring uses the affine quotient comparisons and agreement of their projections on overlaps. This rules out an arbitrary `Nonempty` isomorphism. |
| Simultaneous affine frames give A/(a_i,b_j) for both schemes | `regularSectionIntersection_affine` gives the quotient by the supremum of the two component ideals and its projection to U. The direct-sum comparison over T identifies the other zero scheme with this same chart. The general `regularSectionZero_affine` also applies to the concatenated direct-sum frame. |
| Intersection ring A/(a_i) tensor_A A/(b_j), multiplication and inverse | `regularSectionIntersectionRing I J` states the A-algebra isomorphism with `A ⧸ (I ⊔ J)`, its pure-tensor multiplication formula, and the inverse on every residue class. Specialize I,J to the two component ideals in the preceding chart. |

## Dependencies and searches

Read all thirteen recorded statement-dependency nodes, including their full statements and
Lean or Mathlib bindings. The definitions use these declarations, without private copies:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`; the scheme restriction/frame API is used by the
  existing bundle construction.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjSectionsEquiv`; `WeilConjectures.AlgebraicGeometry.Modules.Dual`:
  `Scheme.Modules.dual`; the existing `SheafOfModules.bidual`, `overHomObjIso`,
  and `homObjFreeUnitIso` supply evaluation and the actual dual frame.
- `Sheaf.Paper.PurityVectorBundleZeroSection`: `PurityVectorBundle` and its `zeroSection`.
  `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: `scheme`, `π`, `affineChart`,
  `augmentation`, `zero_spec`, and `affineChart_spec` supply the relative-Spec construction.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`:
  `exists_quasiCoherentSymmetricAlgebra_core` supplies the unique extension.
- The relative-Spec dependency is the published
  `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec` module, declaration
  `AlgebraicGeometry.affine_morphism_relative_spec`, reused through the bundle construction.
  Its complete current signature and docstring were read using `scompile.py --source`,
  as was `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`, absent from the older checkout.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`:
  `quasiCoherentSymmetricAlgebra_affine_comparison` and the existing symmetric-algebra sheaf
  inclusion and section map, used in the bundle charts and evaluation generator equations.
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`: `SymmetricAlgebra.equivMvPolynomial` and
  `equivMvPolynomial_ι_apply` are the recorded polynomial identification.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Pullbacks`: `pullbackSpecIso` and its projection equations;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`, `snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  `Scheme.Hom.app_surjective`, `IsClosedImmersion.hasAffineProperty`; these are the recorded
  affine closed-immersion criterion, with `HasAffineProperty.iff_of_iSup_eq_top`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- Mathlib module-sheaf limits, `unitHomEquiv`, and `sectionsMap` give the sectionwise finite
  direct sum. Mathlib `Scheme.Hom.ker` and `IdealSheafData` give the zero ideal.

The recorded dependencies' modules are reached by the public bundle/dual imports, except for
newly explicit Mathlib imports for polynomial bases, regular sequences, ideal sheaves, and
module-sheaf limits. There is no proof dependency to add: the node's `proof_deps` is empty.

Searches retained from the saved packet: LeanFinder “Regular section of a finite locally free
sheaf and transverse pair of sections defined by a regular sequence” and “Regular sections of
algebraic vector bundles defined by regular sequences in local rings and transverse direct
sums”; LeanSearch “A regular vector bundle section has components forming a regular sequence
in each local ring at its zero locus”; Loogle `"RegularSequence"` and `"IsRegular", "Scheme"`;
Mathlib grep `regularSection|regular_section|transvers.*section` and
`IsRegular|zeroLocus|IdealSheafData`. No exact regular-section construction was found.

Repair searches:

- `msearch.py N3 def-pur-regular-section leanfinder` with “Global sections of a finite locally
  free sheaf correspond to sections of the relative spectrum of its symmetric dual algebra”:
  eight hits, generic Gamma-Spec adjunction and affine-space descriptions, no exact match.
- `msearch.py ... loogle '"homObjSectionsEquiv"'`: no indexed hit. Direct source reading finds
  the exact ordinary sheaf-Hom equivalence, and the module reuses it.
- `msearch.py ... grep 'regularSection|regular_section|transvers.*section' AlgebraicGeometry/`:
  zero hits.
- `rg` for `regularSection|regular_section|def-pur-regular-section` in the prescribed upstream
  and project source directories, and names in `dag/lean_names_upstream.json`: no existing
  public implementation of this node.
- `rg` for same-rank dual declarations found only a **private** `dual_rank` in
  `PicardPullbackLocalRanks`; it cannot be imported as a public interface. Its public building
  blocks `overHomObjIso` and `homObjFreeUnitIso` are reused in `regularSectionDualFrame`.
- `rg` for quotient/tensor comparisons found `Algebra.TensorProduct.tensorQuotientEquiv` and
  `quotientTensorEquiv`, not the two-factor component-ideal comparison with the formulas
  required here. No second quotient or tensor-product definition is introduced.

## Edge cases and validation

Checked before and during the repair: empty base; empty zero locus; rank r=0 and/or e=0;
empty intersection; unit components (empty zero locus); nonreduced and singular bases;
repeated nontransverse equations. For example, two copies of x at the origin of A1 are
individually regular but their concatenation (x,x) is not regular modulo its predecessor.
The revised transversality predicate detects this, unlike the old arbitrary-sequence clause.
On k[epsilon]/epsilon^2, the epsilon component is not regular. Rank-zero regularity uses the
empty list and the nonzero local ring at a scheme point, rather than assuming a nonempty base.
No additional characteristic, smoothness, positivity, or geometric-section hypothesis appears.

Compilation and delivery validation are performed only by the prescribed `scompile.py` and
`deliver2.py` wrappers. The report's clause audit is the worker's self-check; the maintainer's
independent immutable-head review remains the independent review. No second worker was
started and no independent second reading is claimed.

No `STATEMENT-DISPUTED` or source/node fault is asserted.

The final repaired file passed `scompile.py N3 def-pur-regular-section` cleanly in both modes:
sandbox compilation (48.8 seconds) and the named library module (36.1 seconds), with no errors
or warnings. The dual-frame API uses explicit universe `u`, with no restriction on the
scheme or rank universes. The metadata signature, full list of 34 declarations, 100-character
line limit, source tags, and the proof docstrings of all 17 postponed theorem clauses were
also checked against the final file.

## Second reading by N3

Independent maintainer second reading, 2026-10-18, of immutable delivery
`b96311b4ca7cdd4e174a9a4a1d37bd2760c350e9`. The reader did not author this delivery
or its earlier reading. The required group heading is retained; this text records the
maintainer's independent reading, not a claim that another N3 worker reviewed it.

I read the item JSON and all thirteen statement-dependency JSON files in the immutable
snapshot, the entire delivered Lean file, and the worker report. I checked the actual
upstream/project declarations and docstrings, rather than relying on the worker's table.
The previous contents of this section expressly disclaimed a second reading and supplied
no audit. This report-only replacement repairs H11 (and the substantive report requirement
of H1); no mathematical statement, dependency record, or Lean file is changed.

### Source and clause comparison

Read Stacks `divisors.tex`, Tag 067M, `section-regular-ideal-sheaves` at line 4514,
including the successive injectivity and nonzero final quotient convention, together with
Tag 01WY, `definition-regular-section` at line 2778, and Tag 02OQ,
`definition-zero-scheme-s` at line 2818. The latter two concern invertible sheaves;
they support the rank-one case, not a substitute definition for all ranks. The full-rank
section convention comes from this node and its cited blueprint: main-20261015,
`sec-smooth-purity/sk-prop-an/thm-pur-localized-top-chern.md`, statement and (L3),
and its proof Step 3 (actual component equations in a frame). Also read Algebra 00LF,
`definition-regular-sequence` at line 16594, and Constructions 01LW/01LX,
`definition-relative-spec`/`lemma-spec-properties` at lines 642/663 and their preceding
functor description. The definition is ordinary Zariski geometry throughout.

| Node objects, hypotheses, and conclusion clauses | Independent match and judgement |
| --- | --- |
| Finite purity datum; separated finite-type k-scheme T | `P : PurityFiniteSetting.{u}`, `T : Scheme.{u}`, explicit `hT`, and separated, locally-finite-type, quasi-compact instances. The last two encode finite type. The bundle dependency requires the explicit structure morphism. No smoothness, regular-base, or extra Noetherian assumption is present; the needed Noetherian fact is derived by `isNoetherian_of_locallyOfFiniteType hT`. |
| Locally free F of constant rank r, including zero | `F : T.Modules`, `r : ℕ`, and the recorded `IsFiniteLocallyFreeOfRank r`. Its source definition is local free generators indexed by a type equivalent to `Fin r`; the scheme open-cover interface gives precisely the node's frames. |
| Ordinary sheaf dual and coordinate-projection dual frames | `Scheme.Modules.dual` abbreviates the existing `SheafOfModules.homObj F (unit _)`. `regularSectionDualFrame` composes restriction of Hom, contravariant transport of the given frame, and the existing finite-free dual isomorphism. `regularSectionDual_rank` records constant rank. This reuses the ordinary sheaf Hom, not derived Hom. |
| Bundle E(F)=relative Spec Sym(F dual), p, z | `regularSectionBundle` sets its module to `dual F` and its scheme/projection to `VectorBundleZeroSection.scheme`/`π`; `phi` is identity. The reused `PurityVectorBundle.zeroSection` is the augmentation section. This has the required dual variance. |
| s is an actual global section; evaluation on every open | `s : F.sections` is a compatible family, equivalent to F(T) since the top open is terminal. `regularSectionEvaluation` uses the existing bidual map and global-sections/Hom equivalence. `_apply` specifies lambda applied to the actual restriction of s. |
| Unique algebra extension, corresponding geometric section, inverse correspondence and gluing | `regularSectionAlgebraMap` uses the recorded unique universal property; `_spec` fixes its values and uniqueness. `regularSectionGeometric_existsUnique` fixes a map over T by Spec of the evaluation lift on every affine chart. `regularSectionGeometric` chooses only from that unique characterization. `_bijective` supplies the section correspondence, with the inverse and overlap argument in its docstring. No arbitrary map or bare Nonempty choice replaces it. |
| Zero fibre product, morphism to T, evaluation ideal, closed immersion | `regularSectionZeroScheme` is the pullback of the actual geometric section and augmentation zero section; `_Projection` is fst. `_ZeroIdeal` reuses Mathlib `Hom.ker`. `_ZeroIdeal_spec` asserts closedness and equality with the evaluation image on every affine open. Since this morphism is closed, it is quasi-compact, so the kernel ideal-sheaf construction computes the actual kernel on affine opens. Exactness on affine quasi-coherent modules gives the displayed image of sections. |
| Polynomial coordinates, generator values, tensor quotient and its maps | `_Polynomial_coordinates` uses a dual basis with the Kronecker equations, `equivMvPolynomial`, evaluation to the actual basis coefficients, and augmentation to zero. `_Zero_affine` supplies the quotient chart over U. `_AffineRing` is the commutative-ring pushout of the two explicitly distinct polynomial maps, with both factor inclusions equal to the quotient map and the inverse on residue classes. This specifies multiplication on pure tensors, as in the node. |
| Regularity at every point of Z(s), actual component germs, injectivity and final quotient nonzero | `IsRegularSection` quantifies over points of that pullback, an affine neighbourhood of its image, an actual basis of F(U), and `List.ofFn` of the germs of `b.repr (s.val ...)`. The predicate is the recorded `RingTheory.Sequence.IsRegular` on the base stalk itself. Its `regular_mod_prev` and `top_ne_smul` are exactly the two regular-sequence conditions. Quasi-coherence converts an affine section basis to a sheaf frame; any local frame refines to an affine one. Thus the neighbourhood formulation adds no hypothesis. |
| Rank zero, empty base and empty zero locus | `_rankZero` says every section is zero, p and the zero projection are isomorphisms over T, and regularity holds. `_emptyZero` states vacuity. Empty-list regularity at scheme points uses nonzero local rings, not a global nonempty-scheme assumption. |
| G of rank e, regularity of both sections, transverse concatenation | `IsTransverseDirectSum` includes both regularity predicates and then quantifies over points of the actual scheme intersection with simultaneous affine bases and the concatenation of the two actual germ lists. No auxiliary unrelated regular sequence is used. Neither r nor e is required positive. |
| Sectionwise direct sum and paired section | `_Sum` is the actual product pairing via `unitHomEquiv` and `prod.lift`. `_Sum_sections` gives the sectionwise bijection to pairs and both global-section projections. Finite products are direct sums in this module category; `_Sum_rank` gives r+e. |
| Zero scheme of sum equals scheme intersection; quotient by both component ideals; canonical gluing | `_SumZeroScheme` uses the actual paired section and the derived rank witness. `_IntersectionScheme` is the pullback of the two closed zero-scheme projections. `_SumZeroComparison_existsUnique` fixes the unique isomorphism over T, `_Comparison` chooses it, and `_spec` records its projection equation. Uniqueness follows from monomorphy of closed immersions. `_Intersection_affine` gives A/(I+J) over U and `_IntersectionRing` specifies the multiplication tensor map and inverse. These formulas force agreement on overlaps and match the node. No transversality assumption is needed for this scheme identity. |

### Exact dependency declarations, uniqueness searches, and gates

The thirteen dependency bindings were checked as follows: `PurityFiniteSetting` in
`Sheaf.Paper.PurityFiniteSetting`; `SheafOfModules.IsFiniteLocallyFreeOfRank` in the
recorded LocallyFree module and its scheme open-cover API; `homObj` and
`homObjSectionsEquiv` in InternalHom; `PurityVectorBundle`, its zero section and
`zeroSection_spec`; `exists_quasiCoherentSymmetricAlgebra_core`;
`affine_morphism_relative_spec`; Mathlib `pullback`, `fst`, `snd`; Mathlib `Spec`
and `Spec.map`; `quasiCoherentSymmetricAlgebra_affine_comparison`;
`SymmetricAlgebra.equivMvPolynomial` and `_ι_apply`; `pullbackSpecIso` and its two
projection equations; `IsClosedImmersion.hasAffineProperty`,
`HasAffineProperty.iff_of_iSup_eq_top`, affine preimage and `Hom.app_surjective`;
and `RingTheory.Sequence.IsRegular`. The symmetric-algebra, affine-chart and
zero-section interfaces were read in the read-only N3 clone. The published relative-Spec
module, absent at its recorded path locally, was read successfully with
`scompile.py --source WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`.
Its functor, counit chart, morphism variance and open-restriction clauses agree with the
record and the use here. I also read the actual bidual, internal-Hom restriction,
finite-free duality and ideal-sheaf kernel definitions used by the constructions.

Fresh independent searches used LeanSearch with “Section of a finite locally free
algebraic sheaf is regular when its zero scheme is cut out by the component regular
sequence” and LeanFinder with “Algebraic vector bundle section with regular zero scheme
and transverse concatenation of local equations”. Both returned eight hits: ordinary
regular sequences, set-valued scheme zero loci, or topological/manifold bundles; none
states this notion. Independent `rg` for regular sections and transverse-section wording
in upstream WeilConjectures, Mathlib algebraic geometry, project Sheaf and
`dag/lean_names_upstream.json` found no exact declaration. Existing dual, regular-sequence,
fibre-product and ideal-sheaf definitions are reused, so no H4 duplicate was found.

All 34 def/theorem names in the file are listed in `lean.declarations`. All 17 theorems
have only `sorry` bodies and explanatory source/blueprint proof docstrings. Every definition
has real data; the two new choices are uniquely characterized, and the algebra choice uses
the existing unique extension theorem. The module docstring has source and blueprint data.
The exact text from `def IsRegularSection` through `: Prop` equals `lean.statement`, including
the newline. There are no lines over 100 characters, unbound universes or auto-implicit
variables (`autoImplicit false`), file-local instances, or added characteristic restrictions.
The shared size u is the existing scheme/module encoding; the finite indices use `Fin` and
`ULift`, with no silent equality of different site universes.

No new definition node, dependency repair, or statement correction is needed; thus no
statement-change citer audit is triggered. The shared route-pivot dropped-node list has no
intersection with the item's thirteen citations. There is no item route-pivot repair note
at the supplied shared ref. The module introduces no infinity/dg/model-category machinery
and makes no pro-etale replacement of its Zariski sheaf geometry.

### Edge cases and compiler evidence

Checked mathematically: rank zero in either or both factors; empty T; empty zero locus;
empty intersection; a unit component; zero section of positive rank on a nonempty base;
regular coordinate tuples; repeated equations; nonreduced and singular bases. On A1,
(x) and (x) are individually regular but (x,x) fails after the first quotient. On
k[epsilon]/(epsilon^2), epsilon fails injectivity. On k[x,y]/(xy), x+y is a nonzerodivisor
and its zero scheme can be nonreduced; the definition accepts this without smoothness.
The zero section in positive rank fails injectivity at every scheme point, while the
empty base is vacuous. At rank zero the relevant local ring itself is the nonzero final
quotient. These checks reveal no excluded node case or unintended stronger condition.

Reproduced the immutable file using only the prescribed wrapper:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py N3 def-pur-regular-section \
  snapshot/lean/Sheaf/Paper/PurityRegularSection.lean
Checking 1 Lean file(s) on the server, one at a time.
sandbox Sheaf/Stage2/Sandbox0.lean
(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-ixxqk3ff/.lbuild) [32.5 s]
library Sheaf/Paper/PurityRegularSection.lean
[37.8 s]
exit code 0
```

There were no error or warning messages. The installed `scompile.py` is the 2026-10-17
server-overlay implementation, rather than the older local-first implementation described
in the brief. This evidence is from that authorized wrapper and its private overlay in
both sandbox and named-library modes, not a direct SSH command or a global build. No
repository, branch head, live Lean file or snapshot was edited. Only the independent review
and this complete replacement report were written. Final judgement: mathematically correct;
FIX only to replace the empty second-reading disclaimer with this real independent audit.
