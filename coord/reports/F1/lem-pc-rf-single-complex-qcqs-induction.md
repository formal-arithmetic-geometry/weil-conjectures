## Worker report

The module states `AlgebraicGeometry.singleComplexBaseChangeQcqsInduction`. It introduces a cartesian square of schemes with morphisms `f`, `f'`, `g`, and `g'`, records quasi-compactness and quasi-separatedness of `f`, and uses the derived-category objects `K` and `K'`, a derived pullback map `φ`, a proposition `stalkCondition` with proof `h_stalk`, and the comparison morphism from `Lg^* Rf_* K` to `Rf'_* K'`; the conclusion is that this comparison is an isomorphism. The direct-image and pullback functors are the recorded declarations `schemeDerivedDirectImage` (Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage) and `derivedPullback` (Sheaf.AlgebraicGeometry.DerivedPullback), while the derived category is `schemeDerivedCategory` (Sheaf.AlgebraicGeometry.DerivedCategory). The `IsPullback` hypothesis renders the cartesian square, `[QuasiCompact f]` and `[QuasiSeparated f]` render the qcqs assumptions, and `h_stalk` renders the stalkwise condition. Edge cases checked: identity base change and empty schemes are admitted by the unrestricted `IsPullback` square and proposition hypothesis.

Searches: `msearch.py leanfinder "quasi-compact quasi-separated derived base change Mayer Vietoris induction"` found no derived theorem; `msearch.py loogle "DerivedCategory, Iso"` found no hits; grep for `base.change.*complex` in Mathlib found no matches; `rg` over the project found no existing single-complex qcqs induction declaration.

## Earlier second reading (a previous round; superseded)
The theorem signature was independently checked against the node. The cartesian square is represented by `IsPullback g' f' f g`; the qcqs assumptions are typeclass binders; the derived objects, pullback map, stalk proposition and proof, and comparison morphism occur in the same order as the node; and the conclusion is `IsIso comparison`. The dependency declarations are imported from their landed modules.

## Second reading by F1

I opened the node and all five recorded dependency signatures, then read perfect.tex
at equation-bc and labels lemma-single-complex-base-change-condition and
lemma-single-complex-base-change (Tags 0DJ8 and 0DJ9). The local literature checkout
is absent; I used the obtained Stacks TeX at /home/ubuntu/c1-stacks-review/perfect.tex
and checked https://stacks.math.columbia.edu/tag/0DJ9. The corrected node only adds
explicit citations identifying its canonical maps; its mathematical assertion is
unchanged and agrees with the source. This reading supersedes the earlier second
reading and the worker report's claim that arbitrary Prop/morphism binders suffice.

The node's objects, hypotheses and conclusion, matched individually:

1. Four schemes X', X, S', S: `{X X' S S' : Scheme.{u}}`. This is Mathlib's Scheme
   from def-pc-scheme, with no affine, nonempty, reduced or Noetherian assumption.
   Verdict: exact.
2. Four scheme morphisms f, f', g, g': the four explicit arrow binders, in the node's
   orientations. Verdict: exact.
3. The cartesian square and f' the base change of f: `sq : IsPullback g' f' f g`.
   I checked the IsPullback signature and its commutative-square equality sq.w;
   this is the same fibre-product notion as def-pc-base-change, not merely a
   commutative square. Verdict: exact; the worker already got this part right.
4. f quasi-compact and quasi-separated: `[QuasiCompact f] [QuasiSeparated f]`.
   These are the properties of f itself; there is no extra global qcqs hypothesis
   on X or either base. Verdict: exact; retained.
5. K in D_QCoh(O_X): `K : schemeDerivedCategory X` and
   `hK : schemeDerivedQCohProperty X K`. I opened DerivedCategory.lean: the latter
   requires all integer cohomology sheaves to be quasi-coherent. Verdict: repaired;
   the worker only introduced K in the ambient derived category.
6. K' in D_QCoh(O_X'): the corresponding K' and hK' binders. Verdict: repaired;
   the worker omitted its quasi-coherent cohomology condition too.
7. The map L(g')^*K -> K': `φ : (derivedPullback g').obj K ⟶ K'`. I opened the full
   derivedPullback existence theorem and chosen definition, including the K-flat
   counit and the shared SheafOfModules carrier. This is derived tensor pullback,
   not Mathlib's underived module pullback or an etale-sheaf inverse image.
   Verdict: exact; retained.
8. For every x', every i in Z, the specific localized stalk tensor-cohomology map
   induced by φ is an isomorphism: `h_stalk : ∀ (x' : X') (i : ℤ), IsIso
   (SingleComplexBaseChange.stalkComparison f f' g g' sq K K' φ x' i)`.
   The new definition's R, A, B, C are the node's four actual stalk rings.
   leftAlgebra is f's stalk map; rightAlgebra transports g's stalk map along sq.w.
   tensorMap is fixed by BOTH projection restrictions, so is not an arbitrary
   ring map. Its cohomologyModel uses the existing
   ModuleCat.baseDerivedTensorCohomologyModel, which I opened, including its
   universal counit, tensor-algebra action and localized_eq equation.
   The map is localizedComparison followed by the canonical tensorStalkIso and
   the homology map of the stalk of t. Coordinates.P is K-flat; Coordinates.e
   and e' identify Q(P), Q(N) with K, K'; represents fixes t to the GIVEN φ
   through the same derived counit. The output target H^i(N_x') identifies with
   H^i(K'_x') via e' and exactness of the recorded stalk functor. Omitting that
   final isomorphism from an IsIso assertion is equivalent, not a weakening.
   Verdict: repaired; arbitrary stalkCondition : Prop and h_stalk were completely
   unrelated to this hypothesis. All integer degrees and all points are covered.
9. The conclusion concerns the canonical composite, not every arrow between its
   endpoints: `IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
   (schemeDerivedDirectImage f').map φ)`. The new dependency module constructs
   the counit mate: transpose Lf'^*Lg^*Rf_*K ≅ Lg'^*Lf^*Rf_*K -> Lg'^*K under
   Lf'^* ⊣ Rf'_*. Its adjunction Hom equivalence is specified by the underived
   tensor-pullback adjunction, the exact left-derived counit used by the
   composition isomorphisms, and the existing right-derived unit. This is the
   equivalent counit form of the node's unit construction, not an arbitrary
   adjunction or an unconstrained chosen morphism. The second arrow is exactly
   Rf'_* φ, tying the comparison to the given map. Verdict: repaired.
10. The conclusion lies in D(O_S'): the shared derived direct image and pullback
    functors give exactly this category. HasDerivedCategory uses the same
    Mathlib abelian SheafOfModules instances throughout. The family binder
    supplies the infrastructure needed by the existing composition constructor;
    standard derived-category constructions exist for every scheme, so it adds
    no geometric/finiteness assumption or universe-vacuous test condition.
    Verdict: exact.

Edge cases: the empty scheme is permitted in every position where a cartesian
square exists; the stalk condition is correctly vacuous on empty X'. Zero K and
zero K' are permitted. No nonempty, finite-rank, perfect, boundedness, flatness or
Tor-independence binder has been added. i = 0 and all negative integer degrees
are included. There is no index-set binder and hence no empty-index exclusion.
Arbitrary commutative stalk rings include the zero ring, all characteristics and
nonreduced bases. The scheme universe u and derived-category universe w are
explicit and shared with the existing definitions; there is no smaller auxiliary
universe over which an algebra/scheme test could become vacuous. Identity base
change and an arbitrary morphism φ are covered.

Independent searches: msearch leanfinder "derived base change of a single quasi
coherent complex from localized stalk tensor cohomology" returned eight generic
localization/cohomology declarations, none this theorem or comparison. Loogle
"DerivedCategory.homologyFunctor" found the standard cohomology functor and
isIso_iff, which I reused through the shared definitions; no scheme comparison.
The msearch grep query "single.*complex.*base.*change|base.*change.*stalk" in
Mathlib/AlgebraicGeometry found only SurjectiveOnStalks stability. LeanSearch
"canonical localized stalk cohomology comparison of a single complex under scheme
base change" was unavailable (Internal Server Error), recorded as unavailable,
not as negative evidence. rg over WeilConjectures found only etale/pro-etale
base-change maps, which have different coefficient categories. rg over lean/Sheaf
and DAG definitions found the already recorded base-derived tensor cohomology
model and PullbackStalkTensor.IsComparisonIso. I opened both: the latter is a
chosen-fibre-product criterion with target Lp^*K and no map to a given K', so it
cannot encode the present general-square, arbitrary-φ condition. The algebraic
model and the existing module pullback-stalk natural isomorphism ARE reused.
The existing DAG canonical base-change definition had no Lean record, so it is
formalized as a dependency rather than duplicated by a new node. No existing
Mathlib or source statement says this O-module single-complex qcqs theorem.

New-definition reading (H12): def-pc-single-complex-base-change-stalk-condition
states exactly the equation-bc comparison, with canonical K-flat coordinates.
The three existence theorems have complete natural-language proofs: tensorMap
by its universal property; tensorStalkIso by the EXISTING degreewise natural
stalk-pullback map and its differential naturality; Coordinates by a K-flat
resolution, a K-injective target and the localization Hom bijection. Thus all
chosen data satisfy concrete equations, not True or unconstrained existence.
Every data definition has a complete body. No theorem is proved in this stage.
The new node has the exact required fields, source, three search kinds (including
LeanSearch's unavailable status), matching citations, ancestry and lean record.

Dependency reading (H13): def-pc-derived-base-change-map's unit formula is typed
as Rf_*K -> Rf_*Rg'_*Lg'^*K ≅ Rg_*Rf'_*Lg'^*K. Its counit mate in
SchemeDerivedBaseChangeMap.lean is equivalent by adjunction triangle identities
and naturality; composition comparisons are universal and the adjunctions are
pinned to those SAME counits. All four arbitrary scheme morphisms and their
square equality are present, so it covers the chosen pullback and the restricted
square on any open W. Its domain includes every D_QCoh object in the node.

Additional repairs: supplied the absent module docstring and header; corrected
"Cohomology of Schemes" to perfect.tex / Derived Categories of Schemes; supplied
all four natural-language proof steps and their cited DAG lemmas in the theorem
docstring. Preserved every already correct square/morphism/qcqs binder. No
file-local notation, local instance or private definition was introduced. Named
helper instances are global; letI bindings occur only in data definitions or
algebra-structure-dependent helper types, never as hidden have binders in the
main theorem. Signatures were extracted verbatim with the project's declaration
reader and copied to lean.statement. Each module is owned by exactly one node.

Validation: the final three modules compile together with scompile.py F1
lem-pc-rf-single-complex-qcqs-induction, in dependency order, without errors or
warnings (45.7 seconds). No unbound variable/universe remains; all theorems have
only sorry bodies. Delivery preflight is run separately below.

## New nodes

def-pc-single-complex-base-change-stalk-condition supplies the canonical
equation-bc stalk comparison for a GENERAL cartesian square and the GIVEN map
L(g')^*K -> K'. It reuses the tensor-cohomology model and module stalk/pullback
notions, and specifies every additional coordinate map by projection or
localization equations. Source: perfect.tex, equation-bc before Tag 0DJ8.
Searches listed in the second reading show why neither the algebraic model nor
the special identity-target PullbackStalkTensor criterion already supplies it.

## Dependency modules

def-pc-derived-base-change-map had no recorded declaration. Its module
SchemeDerivedBaseChangeMap.lean gives the exact canonical map by the equivalent
counit construction, with adjunction compatibility equations excluding arbitrary
twists. Its internal named existence theorem has the complete derived-adjunction
proof in its docstring; no data definition contains sorry.

## Statement corrected

The original mathematical statement is preserved. It used canonical stalk and
derived comparison maps without statement dependencies defining those maps, which
made a faithful signature unavailable from its original dependency list. Added
[def-pc-single-complex-base-change-stalk-condition] to identify the stalk equation
and [def-pc-derived-base-change-map] to identify the conclusion's composite. The
old statement is stored verbatim in statement_change.old_statement. No hypothesis,
object, conclusion, proof step or proof dependency changed. Source: perfect.tex,
Tag 0DJ9 and the preceding equation-bc / Tag 0DJ8.

lem-pc-tor-independent-perfect-tensor-base-change: holds:true. I opened its
statement and all four proof steps; step 3 still applies the identical qcqs
single-complex theorem to the inherited tensor-condition map.

lem-pc-rf-base-change-single-complex-criterion: holds:true. I opened its statement
and all three proof steps; step 2 still applies the identical theorem to
E tensor-derived G and its stated target. These are the two actual citers found
by testing stmt_deps and proof_deps, not textual ancestry mentions. Neither was
edited and neither requires a unit-statement change.

Original statement, verbatim:

```tex
In a cartesian square of schemes X' \xrightarrow{g'} X and S' \xrightarrow{g} S, with f:X\to S quasi-compact and quasi-separated [def-pc-scheme, def-pc-base-change], write f':X'\to S' for the base change of f. Let K \in D_{\mathrm{QCoh}}(\mathcal O_X) and let L(g')^*K \to K' be a map in D_{\mathrm{QCoh}}(\mathcal O_{X'}) [def-pc-derived-category]. For x'\in X', put x=g'(x'), s'=f'(x') and s=f(x)=g(s'). Assume that for every x' and i\in\mathbf Z the canonical map H^i(K_x\otimes^L_{\mathcal O_{S,s}}\mathcal O_{S',s'})\otimes_{\mathcal O_{X,x}\otimes_{\mathcal O_{S,s}}\mathcal O_{S',s'}}\mathcal O_{X',x'}\to H^i(K'_{x'}) is an isomorphism. Then the composite Lg^*Rf_*K \to Rf'_*L(g')^*K \to Rf'_*K' is an isomorphism in D(\mathcal O_{S'}).
```

Additional source checks: I opened cohomology.tex at remark-base-change (08HY),
lemma-base-change-map-flat-case (02N7), sheaves.tex at lemma-stalk-pullback-modules
(0098), and more-algebra.tex at equation-comparison-map. The dependency node's
old source field still points to etale-cohomology.tex / 07A7 / 0736; its existing
review/lead note already identifies this as incorrect. The actual O-module,
unbounded construction is cohomology.tex / 08HY, exactly the counit mate used by
the module. I report this pre-existing citation mismatch and preserve that field
because a dependency delivery owns only its lean record. No flat or bounded-below
hypothesis from the historical 02N7 construction is carried into our theorem.

Final dry run: deliver2.py F1 lem-pc-rf-single-complex-qcqs-induction --no-push
printed OK at b04ae243c: preflight passed and the complete packet compiled.
The node's ancestry metadata now follows the computed created.item chain rather
than the stale empty via array in the original item copy.
