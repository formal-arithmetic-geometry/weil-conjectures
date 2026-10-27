## Worker report

Item: lem-coef-finite-bidual-transpose. Group N5, stage 2, 2026-10-22.

The delivery states `CategoryTheory.FiniteBidualTranspose.finite_bidual_transpose`
in `Sheaf.SixFunctors.FiniteBidualTranspose`. Its only theorem has proof `sorry`.
The two auxiliary definitions have complete data: `scalarCounit` composes the
recorded scalar counit with localization of an equality transport;
`TensorComparisonModel` spells out the K-flat representative square that
characterizes the canonical tensor comparison. Neither constructs a new tensor,
internal Hom, scalar extension, evaluation, or bidual map.

The earlier worker's refusal confused stage 1 with stage 2. The ND merge recorded
in the live node is a reviewed stage-1 split: it has `reviewed`, but no `lean`
or `reviewed_lean`. It supplies the proof plan used here. This delivery does not resplit it. The returned stage-2 delivery is repaired
as described below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The site is `C : Type c`, `[Category.{v} C]`, `J : GrothendieckTopology C`.
  Its coefficients and modules use `max c v r`. This contains the site objects
  and arrows while retaining their independent universes. The sheafification
  and locally-bijective-equivalence instances are the standard small-site
  hypotheses of the recorded module and internal-Hom declarations. No equality
  between object and arrow universes is imposed.
- A -> B is `φ : A ⟶ B` for `A B : Sheaf J CommRingCat.{max c v r}`.
  Both module categories are the recorded `RingedTensorModules` spelling of
  `ringedSiteModules` / Mathlib `SheafOfModules`.
- D(A), D(B) are Mathlib `DerivedCategory` of those categories. The two
  `HasDerivedCategory` instances have independent morphism universes `wA`, `wB`.
  There is no constructible, bounded, perfect, or dualizable subcategory.
- S is `M.T`, where `M` is precisely the dependency's
  `SheafOfModules.DerivedChangeOfRingsCochainModel φ`. Thus its ordinary functor
  is fixed on objects and maps, its counit is universal, it computes on K-flats,
  and it is triangulated. This is a presentation of the specified derived
  extension, not an unconstrained functor. `hE` identifies the termwise ordinary
  extension with `CochainPullback.extend φ`; the object's `obj_eq` and `map_eq`
  already prescribe this same functor, so the equality only aligns presentations.
- H_A, H_B are `derivedInternalHomOfUniverses J A` and
  `derivedInternalHomOfUniverses J B` with their respective localization sizes.
- The tensors and closed adjunctions are `SA`, `SB`, with their existing
  `CoefficientTensorModels` `TA`, `TB`. The data `coherenceA`, `coherenceB`
  are exactly `RingedDerivedTensorCoherence`, including the representative
  associators, unitors, and Koszul braidings. These are presentations of the
  canonical structures supplied by the recorded closed-monoidal theorem,
  not extra geometric assumptions or arbitrary monoidal structures.
- The canonical tensor identifications are `t`, normalized by `ht`.
  `TensorComparisonModel` says, for every pair of K-flat complexes P,Q,
  that the square comparing localization, the existing scalar counit,
  the existing total-tensor identifications, and the actual scalar tensor
  isomorphism `CochainPullback.epsilon φ P Q` commutes. It retains K-flatness
  of both extended complexes. Its equality is exactly the defining K-flat
  square of canonical derived tensor pullback, specialized to the identity
  geometric inverse image. In particular a freely chosen natural tensor
  isomorphism is not accepted. The cochain epsilon itself is fixed by the
  ordinary pure-tensor normalization in `extensionComparison`.
- The chosen dualizing objects and map are arbitrary `ΩA`, `ΩB`, and
  `u : M.T.obj ΩA ⟶ ΩB`. No invertibility is assumed for u.
- The arbitrary object is `K : DerivedCategory (RingedTensorModules J A)`.
  Its two comparison maps are `hK` and `hDK`, with exactly the sources
  S(D_A K), S(D_A^2 K), and targets D_B(SK), D_B(S D_A K).
- Evaluation is `SA.evaluation T ΩA` and `SB.evaluation T ΩB`, the actual
  adjunction counit, in the order dual tensor object.
- The two hypotheses are `hevK`, `hevDK`. Each is
  `SB.tensor.map (h_T, 1) ≫ evB = t.inv ≫ M.T.map evA ≫ u`.
  Lean composes left to right; restoring `t.inv` makes both sides maps from
  S(D_A T) tensor ST to ΩB. They assert the node's hypothesis once for
  T=K and once for T=D_A K. No naturality of a family h is assumed.
- The bidual maps are written directly as `SA.transpose K (H_A(K,ΩA)) ΩA`
  applied to signed braiding followed by `SA.evaluation K ΩA`, and the
  corresponding `SB.transpose` expression at SK. These use the existing closed
  transpose and evaluation, with no separate definition or selected bidual map.
  This avoids importing the dropped-route `RingedSiteDualityMaps` module.
- The first conjunct is
  `M.T.map deltaA ≫ hDK = deltaB ≫ H_B.map (hK.op, 1)`.
  This has source SK and target D_B(S D_A K), as in the node.
- The second conjunct treats invertibility by quantifying over isomorphisms
  `eK`, `eDK` with homs equal to `hK`, `hDK`. This is equivalent to requiring
  both given maps to be isomorphisms. It states
  `M.T.map deltaA ≫ eDK.hom ≫ H_B.map (eK.inv.op, 1) = deltaB`.
  The last Hom map is the inverse of D_B(hK); it has the contravariant
  direction required in the statement. There is no invertibility condition
  on either bidual map.
- The last conjunct says the same t preserves the two specified braidings,
  `M.T.map symmetryA ≫ t = t ≫ symmetryB`. The supplied
  `coherence.symmetry_model` explicitly identifies those braidings with
  multiplication by `(i*j).negOnePow` on every homogeneous summand.
  Consequently this is preservation of exactly the same Koszul sign,
  including odd degrees and characteristic two, rather than an unsigned swap.
- No flatness, finite generation, constructibility, nonzero-object, or
  biduality-isomorphism hypothesis occurs.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its E, obj_eq,
  map_eq, T, ε, universal, triangulated and computes fields; the recorded
  `nonempty_derivedChangeOfRingsCochainModel` supplies these presentations.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its explicit localization
  construction using the canonical functorial K-injective replacement.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its unique K-flat representative square specifies the t normalization.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CategoryTheory.RingedTensorModules`, `RingedDerivedTensorCoherence`,
  `RingedDerivedTensorSymmetryModel`, `ringedDerived_closed_symmetric_monoidal`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `WeilConjectures.CoefficientClosedStructure`, its tensor, transpose and
  evaluation, `CoefficientTensorModels`, its iso, and `coefficientTotalTensor`.
- `Sheaf.SecSmoothPurity.CochainCoefficientArrows`:
  `CategoryTheory.CochainPullback.extensionFunctor`, `extend`, `epsilon`,
  `extensionPullback`, and `extensionComparison`. The identity geometric
  inverse image and the actual ring map are retained in these constructions.
- Proof import `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`,
  the symmetric monoidality result used in the node's proof step 1.

The three already recorded definition nodes
`def-zl-ringed-derived-closed-symmetric-monoidal-data`,
`def-pur-cochain-coefficient-arrows`, and `def-coef-ringed-tensor-hom-model`
are added to `stmt_deps`, since this signature uses their existing declarations.
The closed symmetric monoidal existence theorem
`lem-sf-ringed-derived-closed-symmetric-monoidal` stays in `proof_deps` only. Their combined statement/proof dependency
closures were checked for a path back to this item; none exists. No new node
or dependency module is needed. The item's statement and proof are unchanged.

Edge cases checked before writing: K=0 and either Ω=0 make the equality a
zero-map identity; the zero ring and the empty site are not excluded. For
A=B and u the identity, the canonical comparison gives the ordinary signed
bidual transpose. Non-flat Z -> Z/2 is allowed since only K-flat source
resolutions, not flatness of the ring map, enter the comparison. Arbitrary
unbounded K, odd shifts, and characteristic two retain the same signed swap.
The conditional isomorphism clause is not used for the unconditional equality.
In particular hK need not be invertible there. No statement fault or
STATEMENT-DISPUTED issue was found.

Searches for existing statements (2026-10-22):

- `msearch.py leanfinder`, query "evaluation preserving scalar comparison
  respects double transpose in a derived closed symmetric monoidal category":
  eight hits, including `CategoryTheory.expComparison_ev`, `coev_expComparison`,
  `MonoidalClosed.compTranspose`, `ihom.ev_coev_assoc`, and adjunction formulas.
  None states this double-transpose identity. The exponential comparison uses
  Cartesian monoidal categories, which is not the derived tensor here.
- `msearch.py loogle`, query `"bidual"`: zero hits.
- `msearch.py grep`, query `bidual|doubleDual|expComparison`, subdirectory
  `CategoryTheory/Monoidal`: five hits in `Closed/Functor.lean`, all exponential
  comparison formulas, no double-transpose result.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, for this item id,
  `finite_bidual_transpose` and `FiniteBidualTranspose`: no hit.
- Concept searches over both source roots found the generic signed map
  `CategoryTheory.ringedSiteBidual` (its expression is expanded using the existing
  transpose and evaluation; its module is excluded by the route-pivot gate), the stronger
  `evaluationBidualComparisonTransport` (requires invertible coefficient map,
  invertible Hom comparisons and an equivalence of full subcategories), and
  the private `bidual_restriction_untransported` in
  `CoefficientBidualTriangleCompatibility` (invertible Hom comparison at every
  object, identity target coefficient). None covers arbitrary u and the two
  possibly noninvertible h maps in this item. Upstream `Verdier.bidualityMap`
  and `MonoidalClosed.toIhomIhom` define the bidual map but do not state its
  scalar double-transpose compatibility.

Validation: all compiles use scompile.py against the live published library,
separately in module-mode sandbox and library mode. Initial universe-inference
and equality-transport elaboration failures were repaired with explicit
universe arguments and equality of the actual cochain functors. No site
universes were equated, no source file or launcher tool was changed, and no
library/global build was run. Final clean compile and dry-run results are
recorded by the delivery wrapper.

Dry-run repair: the first preflight rejected a direct import of
`Sheaf.CategoryTheory.RingedSiteDualityMaps`, because the module also belongs
to dropped-route node def-per-ringed-site-bidual-transpose. Removed that import
and the newly added corresponding dependency, and expanded the bidual expressions
using existing transpose, evaluation, and braiding. No new map or altered formula
is introduced. Added an explicit public import of CoefficientRingedTensorHomModel.


## Returned delivery repair

Return L, immutable head `9fdb7119165b`, H2: replaced the added statement
dependency `lem-sf-ringed-derived-closed-symmetric-monoidal` with
`def-zl-ringed-derived-closed-symmetric-monoidal-data`. The latter's reviewed
`existing: true` record owns `CategoryTheory.RingedTensorModules` and
`CategoryTheory.RingedDerivedTensorCoherence` in
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`. Reading their
source confirms that the signature uses the abbreviation and coherence structure
directly; it never chooses data from
`CategoryTheory.ringedDerived_closed_symmetric_monoidal`. That existence theorem
remains in `proof_deps`, where the proof plan uses its tensor-Hom bijections.
The statement, proof plan, proof dependencies, Lean signature, and entire Lean
file are unchanged from the returned packet. No new node or dependency module
is introduced. The advisory import is retained as requested by the return's
instruction that the Lean file is unchanged.

Initial saved-packet dry run: `OK (dry run)` at `a03d2cfae01`, with clean
server compilation and preflight. That mechanical pass does not address the
independent review's ownership defect; the dependency replacement above repairs
it. Self-check: the definition node lists both declarations in `lean.declarations`;
the theorem is absent from `stmt_deps` and present in `proof_deps`. No other
node field except `lean` and the authorized statement-dependency additions differs
from the current base. Final compilation, dry run, and push use the prescribed
wrappers.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
