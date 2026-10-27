## Worker report

Item: lem-sfb-cyclic-total-triangulated. Group N6, stage 2, 2026-10-22 UTC.
Module: `Sheaf.CategoryTheory.CyclicTotalTriangulated`.
Primary declaration: `CategoryTheory.RelativeCyclic.exists_signed_cyclicTotal`.

The delivery states the node's clauses using the already landed
`CategoryTheory.RelativeCyclic.TotalModel`. It adds the landed definition node
`def-sfb-relative-cyclic-total` to stmt_deps, as authorized by brief-stage2 §5
(STMT_DEPS MAY GAIN LANDED NODES). No existing field besides lean and this addition
changes. There are no new nodes, dependency replacements or statement corrections.
`HasSignedTotalShift` and `IsTotalDescent` are transparent predicates describing this
node's signed shift formula and its descent comparison; they contain no postponed data.
The five theorems have exactly `by sorry` proofs and matching clause-specific source
and natural-language proof docstrings. No choice of total or descent is defined from
an uncharacterized existence statement.

Sources read: the complete node and its nine proof steps; every stmt_deps node and
its recorded declaration; the complete landed RelativeCyclicTotal module and the
relevant RelativeDerivedInvariants definitions; the main-20261015 direct-images
proof, paragraph (3); Stacks `homology.tex`, lemma-long-exact-sequence-cochain
(Tag 0117), definition-shift-cochain; `derived.tex`, definition-cone,
lemma-acyclic (05RT), definition-unbounded-derived-category (05RU), and
lemma-universal-property-localization (05R7). The blueprint paragraph supplies the
open-direct-image context, while the node explicitly identifies this as an extracted
agent-formulated auxiliary calculation with exact combined reference wanted. The
Lean docstrings retain that attribution and the explicit coordinate argument.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Arbitrary commutative condensed ring on the coherent profinite site | `A : CondensedBar.Ring.{u}`, the existing abbreviation for `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1})`. Its `toMon` is exactly `Profinite.CondensedRing`, with the bundled commutativity instance; no topological presentation of A is imposed. |
| Size convention containing the parameters | Explicit `universe u`; `G : Type u`; `Z.{u}` is the lifted multiplicative discrete integers. Internal sheaves have values in `AddCommGrpCat.{u+1}`; the existing small-Hom derived category has morphism universe u+1. No site object/morphism universes are equated and no independent small test universe is introduced. |
| Internal modules and all sectionwise condensed actions | `Equivariant A G` is the existing abbreviation for `Profinite.CondensedAction.ActionModule A.toMon G`; its underlying modules are `Profinite.CondensedAction.Modules A.toMon`, built with `CategoryTheory.Mod`. |
| G profinite | Explicit `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]`; the integer factor has no compactness hypothesis. |
| `K(N)^n=N^n⊕N^(n-1)` retaining G | Existential `K : TotalModel A G`, whose `coordinates N n` is that precise isomorphism, using the exact restriction `retainResidual A G Z`. |
| Differential `(dx,(T-1)x-dy)` | `K.differential`, part of the existing TotalModel specification, with `generatorEnd` fixed by the constant section `(1,generator)` in RelativeDerivedInvariants. |
| Differential squares to zero and is G-equivariant | `K.functor.obj N` is an actual `CochainComplex (Equivariant A G) ℤ`; its complex square-zero law and its equivariant differentials are part of these types. Existence of K asserts these obligations, without assuming a model as a hypothesis. |
| Invariant augmentation `(inclusion,0)` | `K.augmentation` and `K.augmentation_coordinates`; its source is the existing normalized `invariants A G Z`, and `invariantInclusion` retains the residual G-action. |
| Diagonal maps, identities, composition, additive functor on complexes | `K.maps` fixes both diagonal components; functoriality is in `K.functor`; `exists_signed_cyclicTotal` additionally asserts `K.functor.Additive`. |
| Homotopy `(h,-h)` | The same theorem quantifies over all equivariant maps f,g and `h : Homotopy f g`, returning `H : Homotopy (K.functor.map f) (K.functor.map g)` with its two diagonal coordinates fixed for every i,j. |
| Bounded-below quasi-isomorphisms | The explicit `CochainComplex.plus _ N` and `... P` hypotheses, followed by `QuasiIso f → QuasiIso (K.functor.map f)`. `K.bounded` is the termwise bounded-below preservation clause of the existing model. |
| Triangulated descent `QK : D+ → D+` | The final existential F and its actual `F.CommShift ℤ` structure, together with `IsTotalDescent`; this asserts `F.Additive`, `F.IsTriangulated`, and a natural shift-compatible isomorphism from `plusQ ⋙ F ⋙ DerivedCategory.Plus.ι` to `CochainComplex.Plus.ι ⋙ K.functor ⋙ DerivedCategory.Q`. The target is cohomologically bounded below, not a replacement category. |
| Shift `(x,(-1)^s y)` | `HasSignedTotalShift`; `s.negOnePow` handles all integer shifts, and explicit shift-degree isomorphisms keep both reindexed coordinates. `TotalModel.shift` supplies coherent shifts. |
| Cone permutation and sign in source-cone cyclic degree | `cyclicTotal_cone`: its first projection equation keeps the two B coordinates; its second keeps the A^(n+1) coordinate and negates A^n. With source coordinates `(b,a,c,e)` these are exactly `(b,c,a,-e)`. The isomorphism is an isomorphism of complexes, not just degreewise objects. |
| All cone arrows, including negative projection | The last two equations of `cyclicTotal_cone` identify `mappingCone.inr` and `mappingCone.triangle.mor₃` after the prescribed shift. Mathlib's `triangle` uses `-mappingCone.fst`; hence this is the node's negative third arrow. The first arrow is `K.functor.map f`. |
| This cyclic total is the double-complex total | `cyclicTotal_twoColumn` supplies exactly columns zero and one, each chain-isomorphic to UN, with horizontal differential T-1 and all other columns zero. The total isomorphism is fixed on both diagonal inclusions by `K.coordinates`. This connects the following generic signed comparisons to K itself. |
| Lower vertical bound b, moved to zero, with sign `(-1)^(ab)` | `cyclicTotal_lowerBound` assumes precisely `a<0 ∨ q<b → IsZero ((D.X a).X q)`, asserts existence of its finite diagonal sums, and asserts first-quadrant vanishing of `shiftFunctor₂ ... b`. The existing chain isomorphism `D.totalShift₂Iso b : Tot(D_b) ≅ Tot(D)[b]`, equivalently `Tot(D) ≅ Tot(D_b)[-b]`, has the explicit `(a*b).negOnePow` summand formula. |
| Lower-bound comparison maps and quasi-isomorphisms | Its last conjunction gives the naturality square for every bicomplex map f and equivalence of the corresponding quasi-isomorphism assertions. The target's HasTotal binder just supplies the data needed to write its total; the square does not require a bound on the target. |
| Transposition sign `(-1)^(aq)` | `cyclicTotal_transpose` uses the existing chain isomorphism `(D.totalFlipIso ...).inv`, and pins its summand formula to `(a*q).negOnePow`. |
| Row augmentations, column comparisons, sign one on axes | Explicit column-zero lower-shift formula, and explicit a=0 and q=0 transposition formulas without a sign. Both theorems quantify over every bicomplex comparison map and assert the total-map naturality square and quasi-isomorphism equivalence; this includes augmentation bicomplex maps and thus their row/column comparison diagrams. A shifted lower-bound axis is interpreted in the reindexed first-quadrant coordinates, as in proof step 9. |

Dependency declarations used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (through the
  public dependency chain).
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` (the existing internal
  module category, also through the public dependency chain).
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `Modules`,
  `ProductInvariants`, `inflate`, `inclusion`, `residual` in
  `Profinite.CondensedAction`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the recorded additive and essentially
  surjective Q instances. `def-weil-size-convention` has no Lean definiendum: its
  explicit universes are respected as described above.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure` and `.Plus`:
  `DerivedCategory.Plus`, `.Plus.ι`, bounded-below complex/homotopy localization.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`: existing public total-complex
  API for `def-sp-double-complex-total`. In particular the imported Mathlib
  `HomologicalComplex₂`, `.total`, `.ιTotal`, `.total.map`, `.flip`, `.flipFunctor`
  use the node's commuting-differentials and signed-total convention.
- Added landed node `def-sfb-relative-cyclic-total`, module
  `Sheaf.CategoryTheory.RelativeCyclicTotal`: `TotalModel`, `plusQ`; its public
  `RelativeDerivedInvariants` dependency supplies `Z`, `generator`,
  `retainResidual`, `generatorEnd`, `invariantInclusion`, `invariants`, and the
  small-Hom derived-category instances. `HasComparison` and its downstream
  comparison with derived invariants are not hypotheses of this theorem.
- `Mathlib.Algebra.Homology.TotalComplexShift`: `shiftFunctor₂`,
  `shiftFunctor₂XXIso`, `totalShift₂Iso`, `ι_totalShift₂Iso_hom_f`, and
  `totalShift₂Iso_hom_naturality` (full signatures and constructions read).
- `Mathlib.Algebra.Homology.TotalComplexSymmetry`: `totalFlipIso` and its
  `ιTotal_totalFlipIso_f_inv` formula (full signatures and constructions read).
- Proof imports: `Mathlib.Algebra.Homology.HomologySequence` for
  `ShortComplex.ShortExact.homology_exact₁/₂/₃` and δ;
  `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic` for
  `CochainComplex.mappingCone.quasiIso_iff_acyclic`;
  `Mathlib.CategoryTheory.Localization.Predicate` for `Localization.lift`, `fac`,
  `liftNatTrans`, `liftNatIso`, `natTrans_ext`; and
  `Sheaf.CategoryTheory.AdditiveLocalizationDescent` for
  `CategoryTheory.Functor.additive_of_additive_localization`.
  The proof node `lem-sfb-condensed-action-injective-infrastructure` has no recorded
  Lean module or Mathlib match in the read clone, so no fictional import is added.
  Its required categories and exactness interfaces are already exposed by the
  existing public RelativeDerivedInvariants dependency chain. This delivery does
  not attempt that separate infrastructure theorem.

Edge cases checked before and during statement writing: zero coefficient ring and
zero complexes; trivial residual group; T=1 (including the nonzero shifted summand);
f=0; the cone's negative third arrow; negative, odd and zero integer shifts and
lower bounds; characteristic two; complexes with cohomological lower bounds not
shared by their chosen terms; rows/columns on either augmentation axis; zero or
empty diagonal sums. No natural-number truncation drops negative b or s, and no
compactness is imposed on the discrete factor. The two-column total needs only
finite biproducts even for an unbounded N. No statement dispute was found.

Searches actually run (msearch.py, group N6/item lem-sfb-cyclic-total-triangulated):

1. LeanFinder: `Signed two term cyclic totalization preserves homotopies and quasi
   isomorphisms and induces a triangulated derived functor`. Eight hits including
   DerivedCategory.Qh, the homotopy-category triangulated instance and exact-functor
   derived-category constructions. None states this condensed cyclic calculation.
2. Loogle: `CochainComplex.mappingCone, Functor.IsTriangulated`. Zero hits, with the
   diagnostic `unknown identifier 'Functor.IsTriangulated'` for the unqualified name.
   The fully qualified Mathlib declaration was subsequently read and checked by
   the compiler; this search was not treated as evidence that it did not exist.
3. Mathlib grep: `cyclicTotal|CyclicTotal|mappingCone`, subdirectory
   `Algebra/Homology`. Twenty-five cone-related hits, including mapping cones,
   their standard triangles and bounded-below cone bounds; none is a condensed
   cyclic total. Further direct source searches found TotalComplexShift and
   TotalComplexSymmetry, whose canonical maps are reused instead of copied.
4. LeanSearch: `The two term cyclic complex with differential T minus 1 preserves
   quasi isomorphisms and defines a triangulated functor on bounded below derived
   categories`. Eight hits for Functor.IsTriangulated, exact-functor derived
   constructions, and preservation of short-complex homology. No exact match.
5. Direct rg on both `lean/WeilConjectures` and `lean/Sheaf`:
   `cyclicTotal|CyclicTotal|namespace.*RelativeCyclic|TotalModel`. Found the landed
   RelativeCyclicTotal specification and downstream comparisons/restriction theorem;
   no declaration for this node. The downstream RelativeCyclicRestrictionModel
   depends on this item and is not used as an upstream proof. Direct rg for the
   item id in WeilConjectures and rg of the relevant names in
   `dag/lean_names_upstream.json` found no match. No existing notion is redefined.

Validation: the completed module passed scompile.py in both sandbox module mode
(25.0 s) and final library module mode (21.4 s), with no errors or unexpected
warnings. All variables/universes are explicit (`autoImplicit false`), lines are at
most 100 characters, and the diagnostic #check commands were removed.

## Second reading by N6

This is a second in-worker source reading, in accordance with the dispatcher's
single-worker/no-subagents instruction. It does not claim an independent reviewer.
The maintainer independently reviews the delivered packet.

I reopened the node and the complete final module and matched each clause in the
table above. The initial draft needed the bicomplex clauses as well as derived
triangulated descent. The final file now includes `cyclicTotal_twoColumn`, with
both column identifications and the T-1 differential pinned, followed by the actual
Mathlib lower-shift and flip isomorphisms, their signed coordinate formulas, their
naturality squares, quasi-isomorphism equivalences, and sign-free axis equations.
Thus row augmentation compatibility is not replaced by an unnormalized existence
of an isomorphism.

I checked that the cone's source pair and target pair have the opposite storage
order in Mathlib: using its named fstX/sndX projections gives exactly the node's
`(b,a,c,e) ↦ (b,c,a,-e)`, and the last arrow uses `triangle.mor₃` with the negative
projection, followed by K's signed shift. The constant `(1,generator)` in
`generatorEndExist` is the positive integer generator, not multiplicative identity.
I also checked that `TotalModel` supplies the invariant augmentation and both
square-zero and equivariance through its actual bundled complex type. The main
existential asserts existence of this model rather than taking it as an added
hypothesis. F lands in the actual cohomological D+; no termwise bounded model is
assumed for arbitrary derived objects.

One elaboration error in the new total-shift formulas was repaired by qualifying
`CochainComplex.shiftFunctorObjXIso`, since field notation on the total complex
looks in HomologicalComplex. The complete file then compiled cleanly in both module
names. The DAG statement remains unchanged, with only the explicit reuse of the
landed TotalModel node added to stmt_deps. No further mathematical mismatch was found.
