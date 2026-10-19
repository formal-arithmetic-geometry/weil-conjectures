## Worker report

This delivery states `AlgebraicGeometry.Scheme.QbarFiniteLevel.comparison` in
`Sheaf.Paper.QbarCohomologyFiniteLevelComparison`. The theorem and its named
auxiliary property theorems have only `sorry` proofs. All definitions have real
data. Auxiliary unit isomorphisms are selected only from unique-existence
statements that specify their actual augmentation or integral representative.

### Clause-by-clause reading

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime l | `(l : ℕ) [Fact l.Prime]`. |
| Algebraically closed base field K | `(K : Type u) [Field K]`, with `[IsAlgClosed K]` on `comparison`. |
| l invertible in K | `[Fact (IsUnit (l : K))]`. |
| Separated finite-type K-scheme X | `T : Space K`, the full subcategory of `Over (Spec (.of K))` cut out by `LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom ∧ IsSeparated T.hom`. Its arrows are exactly K-morphisms. |
| Z_l inside Q_l inside Qbar_l | `Integral l = ULift ℤ_[l]`, `ℚ_[l]`, and `(Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`; `integralAlgebra` is the actual composite ring map. Ω has an independent universe, with the existing coefficient-stage size transports retained. |
| Constant Z/l^n sheaves, n≥1 | `coefficient l n` is the regular `ULift (ZMod (l^(n+1)))` module restricted along `PadicInt.toZModPow`; `finiteSheaf` applies the recorded `constantSheaf` to it on the small etale site. Natural n starts at zero, so exponent n+1 covers exactly the requested positive levels. |
| Usual quotient transitions | `coefficientStep` is `ZMod.castHom` along divisibility of consecutive l-powers. Its integral-linearity uses `PadicInt.cast_toZModPow`. `tower` applies constant sheafification, degree-zero inclusion, and the recorded `Etale.cohomology` functor to these exact arrows. No surjectivity on cohomology is assumed. |
| Ordinary finite-level etale cohomology | `finiteCohomology` is the recorded `AlgebraicGeometry.Etale.cohomology (ModuleCat (Integral l)) X q` on `finiteSheaf[0]`. This retains the natural integral scalar action rather than forgetting to abelian groups; it is ordinary finite-coefficient cohomology. |
| A_X is the completed coefficient limit and Fhat is its regular module in degree zero | `regular` is explicitly `DerivedCategory.singleFunctor _ 0` applied to `SheafOfModules.unit` of the recorded `pbcAdicCompletion`. At the recorded base coefficient field this is A_X, through the canonical Q_l/base-field and Z_l/integer-ring identifications. Its finite levels are the recorded sheafified continuous coefficient functions; the proof explains their local constant-sheaf identification. No object is chosen from unspecified reductions. |
| Integral full category and raw rationalization | `integralUnit` has underlying object exactly `regular`, with membership proof `regular_mem`; its image is taken by the recorded `pbcStageLocalization`, on the recorded `pbcIntegralStage`. |
| Literal pair unit (Q_l, 1_Ql) | `unit` is the literal constructor with `Padic.finiteCoefficientBase l Ω` and the localized `integralUnit`. It lies in the recorded `pbcQbarCategory`, with its existing common-stage scalar structure. |
| H_adic^q = shifted Hom from this unit | `cohomology l X Ω q := unit l X Ω ⟶ (unit l X Ω)⟦(q : ℤ)⟧`. No discrete constant non-torsion etale sheaf is used. |
| Finiteness for every j≥0 and every n≥1 | The argument to the family `e` is exactly `∀ j n : ℕ, Finite (finiteCohomology l T.obj.left j n)`. |
| Every q≥0, Qbar-linear isomorphism | `e T hfin q` is a `LinearEquiv` over Ω, for every `q : ℕ`. Its right side is `Ω ⊗[Integral l] integralLimit l X q`; tensor symmetry exchanges the factors of the displayed formula in the node, without changing the module or adding a hypothesis. The common universe lift is removed by `ULift.ringEquiv`. |
| The specified inverse limit | `integralLimit` is `Limits.limit (tower l X q)` in integral modules, using the actual induced quotient maps. Forgetting the scalar action preserves this limit. |
| Finite constant sections and inverse limit | `constantSection` is the unit of `constantSheafΓAdj`, followed by the inverse resolution-augmentation H⁰ comparison `h0Sections`. `scalarQuotient` is the actual integral quotient, and `integralConstantSection` is `limit.lift` of their composites. Its only needed compatibility proof is the named `constantSection_compatible`. |
| Extend constant sections to Ω, with 1 corresponding to identity | First conjunct of `comparison`, for every integral a and algebraic b. The input is `(algebraMap _ Ω a * b) • identitySection`; output is `b ⊗ₜ integralConstantSection(a)`. The case a=b=1 gives the stated normalization. `identitySection` is the identity transported through the pair category's specified zero-shift isomorphism. These elementary tensors generate the scalar-extended constant-section map, so this is its full compatibility, not just its value at 1. |
| Natural isomorphisms | Second conjunct quantifies every K-morphism `g : T ⟶ S`, both finiteness witnesses, every q and every source cohomology class. `cohomologyPull` uses the recorded actual completed pair pullback and its uniquely integral-normalized unit and shift arrows. `finitePull` uses the actual coefficient sheafification unit into direct image, its derived augmentation and the recorded Leray comparison. `limitPull` is induced by these finite maps through `lim.map`; `TensorProduct.map` gives its scalar extension. |

The categorical API's noetherianity, finite dimension, and stalkwise invertibility
are established by the named `space_noetherian`, `space_finiteDimension`, and
`space_invertible` statements, with their proof plans from Step 1. Their instances
introduce no further assumptions on T. The helpers constructing naturality maps
are all part of the maps explicitly asserted by this item; none is an arbitrary
map or an isomorphism chosen from bare nonemptiness.

### Dependencies

The original statement dependencies are imported through their recorded modules.
Their declarations are:

- `def-weil-l-adic-numbers`: existing Mathlib match `Padic`, `Mathlib/NumberTheory/Padics/PadicNumbers.lean`.
- `def-weil-algebraic-closure`: existing Mathlib match `AlgebraicClosure`, `Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`.
- `def-weil-pbc-etale-cohomology`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.cohomology`.
- `def-weil-pbc-bounded-constructible-complete`: `Sheaf.Paper.IntegralUniformCoefficient`, `AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete`.
- `def-weil-pbc-rational-category`: `Sheaf.Paper.PbcRationalCategory`, `AlgebraicGeometry.Scheme.PbcRationalDerivedCategory`.
- `def-weil-pbc-qbar-category`: `Sheaf.Paper.PbcQbarCategory`, `AlgebraicGeometry.Scheme.pbcQbarCategory`.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparison`.
- `def-weil-pbc-adic-coefficient-datum`: `Sheaf.Paper.AdicCoefficientDatum`, `AlgebraicGeometry.Scheme.completedReductionTower`.
- `def-weil-pbc-finite-stage-pair-category`: `Sheaf.Paper.FiniteStagePairCategory`, `AlgebraicGeometry.Scheme.PbcFiniteStagePairCategory`.
- `def-pur-ringed-site-zeroth-hypercohomology`: `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`, `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`.
- `lem-weil-pbc-ringed-site-locally-free-derived-hom`: `Sheaf.Algebra.Homology.LocallyFreeDerivedHom`, `CategoryTheory.locallyFree_derivedHom`.
- `def-weil-pbc-completed-pullback`: `Sheaf.Paper.PbcQbarCompletedPullback`, `AlgebraicGeometry.Scheme.pbcQbarCompletedPull`.

The already-landed `def-weil-pbc-completed-pullback` is added to `stmt_deps`:
its actual `pbcQbarCompletedPull` is needed to type the scheme-naturality square.
No other DAG field changes apart from `lean`. The recorded proof-dependency
modules are imported without `public` when used only in the proof plan, including the finite-ring comparison,
Milnor, Mittag--Leffler, integral-basis, locally-free Hom, module/abelian
comparison, and scalar-extension interfaces. The main docstring contains all
eight proof steps and traces the actual maps and constant normalization.

### Edge cases

- Empty X: no nonemptiness or connectedness assumption occurs; regular unit is
  the zero object on the empty site and its identity is zero, as is the constant
  section. The dimension theorem includes the empty case.
- A point: the comparison becomes the usual integral coefficient limit and
  extension to Ω. The normalization sends the identity to compatible quotient 1s.
- Two points or disconnected X: no connectedness is used. Constant sections map
  diagonally, rather than being assumed all of H⁰.
- q=0: the proof uses vanishing of negative cohomology, not a finiteness or
  surjectivity hypothesis in degree -1. Zero shift is explicitly transported.
- First level: n=0 in Lean is exponent 1, never the zero coefficient Z/l⁰.
- Characteristic l: excluded precisely by `IsUnit (l : K)`, as in the source;
  all other characteristics are covered. No extra invertibility is imposed.
- Ramified finite E: the existing stage datum and its uniformizer are retained.
  Only the Q_l base stage forms the pair unit; all other stages are reached by
  the recorded scalar extension and common-stage Hom construction.
- Quotient maps on cohomology may fail to be surjective. Only finiteness is
  assumed, and the proof uses stabilization of finite images.

### Searches

The required searches found no existing declaration of the comparison.

| Tool | Query | Result |
| --- | --- | --- |
| `msearch.py leanfinder` | `constant Qbar l adic cohomology is the inverse limit of finite etale cohomology tensored with algebraic closure of Q_l` | Eight unrelated hits (Padic algebraic closures and general cohomology), no comparison. |
| `msearch.py loogle` | `AlgebraicGeometry.Scheme.EllAdicCohomology, CategoryTheory.Sheaf.H` | Zero hits. |
| `msearch.py grep`, AlgebraicGeometry/Sites | `EllAdicCohomology\|qbar.*cohomology\|finite.level.*comparison` (without spaces at alternatives) | Four lines defining existing integral l-adic cohomology, no theorem comparing the pair-category unit to the finite-level tower. |
| `msearch.py leansearch` | `ordinary l adic cohomology is inverse limit of finite etale cohomology groups when finite followed by scalar extension to Qbar l` | Eight unrelated general inverse-limit/adic-completion hits, no match. |
| `rg`, upstream WeilConjectures and side Lean | Own node id; `QbarCohomologyFiniteLevel\|qbar_finite_level\|QbarFiniteLevel` | No existing module or declaration for this item. |
| `rg`, DAG and Lean sources | Unit/coefficient, completed pullback, finite-coefficient inverse image, constant sheaf, derived global sections, and shift interfaces | Reused the recorded coefficient stages, pair category, completed pullback, `Functor.ofOpSequence`, `NatTrans.ofOpSequence`, sheafification and resolution-augmentation APIs; supplied only the owning item's actual unit/tower/maps. |

No independent new nodes or dependency replacement modules are required. There
is no statement correction or disputed mathematical clause. The prior Q73
PASS is the Stage-1 split review (the current node had no `lean` record), not
an existing Stage-2 statement delivery.

### Validation

Compilation uses only the prescribed `scompile.py` wrapper and its private
side-project overlay. The repaired source uses named compatibility lemmas and opaque finite-level
objects to avoid unfolding the derived-category and chosen-limit constructions.
The final file compiled cleanly, with no warnings, in both the sandbox check
(24.9 seconds) and its actual library-module check (27.4 seconds). No development
options remain in the final source. The final dry run and delivery are performed with
`deliver2.py`, including server preflight and per-file compilation. All source
and shared-project files remain read-only to the worker.

## Second reading by N6

Independent maintainer reading of immutable delivery
`6f951755ad3c155989a8c32024edda8fafc9d4a7`, performed after the worker delivery.
I read the packet, the snapshot item, all thirteen statement-dependency records,
the delivered module and its declaration docstrings, and the recorded dependency
implementations in the read-only N6 clone. I did not write the delivery.

The statement is correct. The following checks are independent of the worker's
clause table above.

- `comparison` binds prime l, a field K with `IsAlgClosed K`, and exactly
  `Fact (IsUnit (l : K))`. `Space K` consists of objects over Spec K with locally
  finite type, quasi-compactness and separatedness; these are exactly the
  separated finite-type K-schemes and their K-morphisms. The helper theorems
  `space_noetherian`, `space_finiteDimension` and `space_invertible` derive the
  category prerequisites rather than assume them in the comparison.
- `Integral` is a canonical universe lift of the actual PadicInt ring;
  `quotient` is `PadicInt.toZModPow (n+1)`, and `coefficientStep` is the quotient
  `ZMod.castHom`. `finiteSheaf` uses the recorded constant-sheaf functor on
  the small etale site. `finiteCohomology` uses the recorded right-derived
  global sections and homology, retaining the integral module structure.
  Forgetting that action gives the ordinary finite-coefficient abelian
  cohomology: the free-module left adjoint is exact, so forgetful sends
  injectives to injectives. There is no replacement by pro-etale cohomology
  on the right side.
- `tower` applies that same cohomology functor to the actual sheaf quotient
  maps, and `integralLimit` is its limit in integral modules. The hypothesis
  is finiteness for every natural j and n, covering exactly j>=0, exponent>=1;
  it does not assume cohomology transition maps are surjective.
- `regular` is the degree-zero regular module over `pbcAdicCompletion`, not
  an object selected by reductions. The finite function-coefficient sheaves
  identify canonically with finite constant sheaves: the constants map is
  locally injective and locally surjective on the finite open fibres of
  a continuous function. This also tracks quotient maps. At the base finite
  field, the canonical Shrink/ULift and integer-ring identifications give
  the stated completed Z_l coefficient sheaf. `regular_mem` is precisely
  membership in the three-clause complete/constructible/origin predicate.
- `integralUnit` is that regular object in the existing full subcategory;
  `unit` is the literal base-field pair after the existing raw localization.
  `cohomology` is shifted Hom in `pbcQbarCategory`. I checked
  `pbcIntegralStage`, `pbcAmbientStage`, `pbcStageLocalization`,
  `PbcRationalCategory`, and the actual common-stage scalar action. No
  Karoubi envelope or arbitrary coefficient category is used.
- The conclusion gives an Ω-linear equivalence for every q>=0. Its tensor
  factors are reversed by canonical tensor symmetry, with the integral
  action on Ω fixed by `ULift.ringEquiv`, Z_l->Q_l and Q_l->Ω. This is the
  node's tensor product. The arbitrary closure Ω lives in independent
  universe w; finite fields are transported by the existing canonical
  `pbcFiniteField`/Shrink construction, with no equality w=u imposed.
- `constantSection` uses the constant-sheaf/global-sections adjunction and
  the inverse degree-zero resolution augmentation. `integralConstantSection`
  is their compatible limit. The first conjunct of `comparison` asserts
  equality for every integral a and every b in Ω, hence the entire
  scalar-extended constant-section map. `identitySection` transports the
  identity by the inverse zero-shift comparison. Taking a=b=1 gives exactly
  the required normalization, including the empty scheme.
- The second conjunct is naturality for every K-morphism between schemes
  satisfying the stated finiteness assumption, in every q. `finitePull`
  uses the actual coefficient-to-direct-image map, derived augmentation
  and Leray comparison; `limitPull` is the induced limit map. On the left,
  `cohomologyPull` uses the recorded `pbcQbarCompletedPull`. Its unit and
  shift isomorphisms are fixed by unique-existence statements specifying
  the ordinary tensor unit/completion augmentation and the localized
  integral representatives. The HEq clauses transport endpoints and fix
  the forward arrows; they do not permit a freely chosen isomorphism.

Sources checked: the blueprint affine-line proof's finite-level sentence;
Milne, Lectures on Etale Cohomology, Section 19, printed pp. 123-125;
Stacks `more-algebra.tex`, `lemma-break-long-exact-sequence` (07KY),
lines 23303-23324; Bhatt-Scholze Proposition 3.1.10, Lemma 6.5.9,
Lemma 6.8.2 and the rational-coefficient discussion in Section 6.8.
The eight-step main docstring follows the node: finite constant/completed
unit, continuous derived limit and finite-site comparison, finite-group
Mittag-Leffler (negative cohomology zero when q=0), regular-unit derived
Hom, finite integral basis, raw rational Hom localization, finite-stage
colimit, and constants/naturality. These are ordinary derived constructions.
No dropped infinity/dg/model-category machinery is introduced. There is no
item-specific route-pivot repair note at the checked origin/newtargets-dag
reference, and neither dependency list intersects route-pivot-dropped.txt.

Edge cases checked: empty X; a geometric point; disconnected X (constants
map diagonally and need not exhaust H^0); q=0; first exponent one;
zero cohomology groups; arbitrary non-surjective cohomology transitions;
ramified finite coefficient fields; all allowed characteristics. No
connectedness, smoothness, properness, nonemptiness or extra finiteness
hypothesis occurs. The characteristic-l base is excluded by exactly the
node's invertibility hypothesis. Site objects and arrows retain their
original sizes; no universe-restricting helper repair is needed here.

One-definition searches: I searched the upstream WeilConjectures tree,
Mathlib AlgebraicGeometry and the side Paper modules for this node id,
QbarFiniteLevel, qbar cohomology, finite-level comparison and
EllAdicCohomology. I opened Mathlib's ElladicCohomology.lean:75 and
OrdinaryCompactCohomology's nearby interfaces. They concern respectively
integral pro-etale cohomology and functorial ordinary/compact cohomology,
not this pair-unit finite-level comparison. The worker records LeanSearch,
Loogle/LeanFinder and grep searches. No duplicate theorem was found.
The new definitions specialize recorded constructions and provide the
actual unit/tower/maps needed by this statement; no missing independent
DAG prerequisite is concealed.

Static checks: the node's `lean.statement` equals the complete source
signature verbatim, including line breaks. All 48 listed declarations are
present. Every declaration has a source/blueprint docstring; all ten
postponed theorem bodies are exactly `by sorry`. Definitions contain real
data; chosen isomorphisms are uniquely specified, and small structural
map laws do not replace any mathematical theorem. There are no lines over
100 characters, no unbound auto-implicit variables, and no project-prefix
namespace or prohibited import. The only added statement dependency is
the already-landed completed-pullback definition, needed for naturality;
this is permitted by the landing tool's STMT_DEPS MAY GAIN LANDED NODES
rule. The item statement and proof are unchanged; no statement correction
or citer audit is needed, and there are no new/dependency modules.

Finding H11 (also the substantive reading requirement in H1): the delivered
`## Second reading by N6` contained only a notice that no worker second
reading had occurred. It was a placeholder rather than a reading. This
complete independent section replaces it; the Worker report is preserved.
No mathematical repair or Lean replacement is required.

### Independent compiler evidence and review boundary

The worker records clean sandbox/library checks of 24.9 s and 27.4 s. I
independently reproduced the exact immutable module with:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py N6 \
  lem-fd-qbar-cohomology-finite-level-comparison \
  snapshot/lean/Sheaf/Paper/QbarCohomologyFiniteLevelComparison.lean
```

Exit status: **0**. Complete final wrapper output:

```text
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-0iyeox0u/.lbuild) [95.4 s]
library Sheaf/Paper/QbarCohomologyFiniteLevelComparison.lean

[106.5 s]
```

No errors or warnings were emitted. Progress messages identified each invocation
as having a 60 s limit after slot acquisition; the displayed wrapper wall times
are recorded verbatim, without asserting they are Lean CPU times. The installed
`scompile.py` (2026-10-17 implementation) sends the side overlay to the server's
persistent `nt_srv_compile.py --wire-confirm`, rather than performing a compile
on this machine. Thus this is prescribed-wrapper server confirmation, not an
unperformed local compile. No compiler limit was changed. Both sandbox and real
module-name checks were run; there is one delivered Lean file.

I compared all three changed snapshot files byte-for-byte with `git show` at the
immutable commit: all match. The commit diff consists only of the item record,
module and report. The record changes are `lean` and the allowed already-landed
completed-pullback dependency. The source `lean.statement` is verbatim equal to
the stored signature. I did not run a global build, direct compiler, preflight,
merge, delivery, fetch, claim, direct ssh, or any mutating git command. Only this
review and the complete replacement report under fixes were written. The
snapshot and all project clones were left unchanged.

All findings: H11 report placeholder, repaired in the supplied complete report.
No H3 mathematical mismatch, H4 duplicate, H5 hollow definition, H6 local theorem
proof, H7 silent correction, H8 docstring fault, H9 convention fault, H10 compiler
fault, H12 new-node fault or H13 dependency replacement fault was found.
