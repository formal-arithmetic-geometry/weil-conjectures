## Worker report

The module Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair states
`SheafOfModules.LineEvaluation.evaluation_inverse_pair`, with a single `sorry`.
Nothing is proved. All auxiliary definitions have actual data: transparent references to
existing module/Hom/global-section objects, the pure-tensor sheafification map, the
specified cancellation composite, and the existing sectionwise linear-category instance.
The node is unchanged outside `lean`; no new nodes or dependency repairs are needed.

Source read: literature/stacks-project/sites-modules.tex, lemma-invertible (Tag 0B8N),
including its quasi-inverse/exactness and internal-Hom evaluation paragraphs, and the first
proof paragraph of lemma-invertible-is-locally-free-rank-1 (Tag 0B8Q). The node's eight
expanded proof steps are recorded in the theorem docstring in the same order.

Hypothesis and conclusion correspondence:

- The general site is `{C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}`.
  The common coefficient/module universe is `max uC vC r`; this allows an arbitrary
  bound above both site universes without identifying the site object and Hom universes.
  `EssentiallySmall` is the node's small-relative-to-modules assumption, and
  `HasSheafCompose` supplies the existing underlying ring sheaf. These give the standard
  module sheafification and abelian instances; no points, terminal objects, binary
  products, local rings, characteristic, or nonzero coefficient assumption is imposed.
- `R : Sheaf J CommRingCat` is the sheaf of commutative rings. `Modules R` is exactly
  `CategoryTheory.ringedSiteModules`, hence Mathlib `SheafOfModules`, with its abelian
  structure. It is not a new category.
- `P : Modules R` and `hP` express precisely that every object has a covering sieve all
  of whose arrows have a slice isomorphism `P.over V ≅ unit (R.over V)`. Covering sieves
  give the covering-family condition without assuming fibre products. The unit uses
  the underlying RingCat sheaf through the recorded `sheafCompose` conversion.
- `dual R P` is `SheafOfModules.homObj (R := R) P (𝟙_ _)`, literally the recorded
  internal Hom to the coefficient unit. `tensorRight P` and `tensorRight (dual R P)`
  are the node's T and S. Lean composition T ⋙ S means the mathematical ST.
- The first conclusion repeats `hP`'s covering-slice statement for `dual R P`.
- The existential `e : P ⊗ dual R P ≅ 𝟙_ _` includes both inverse equations. The
  following universal equation specifies its hom on every pure tensor as
  `phi.app (op (Over.mk (𝟙 U.unop))) x`, so this is the evaluation map, not an
  unconstrained isomorphism. `pureTensor` is exactly the sheafification-unit image
  followed by `tensorObjIsoSheafification.inv`.
- For every U, p, phi with phi(p)=1, the next clauses state e(ap ⊗ bphi)=ab and
  e.inv(a)=ap ⊗ phi. On a trivializing slice p is the basis and phi is its dual.
  Quantification over all such normalized pairs is equivalent in a locally free line:
  a normalized pair trivializes the line, as can be checked on any rank-one chart.
  Quantification over every object includes every restriction of every chart.
- The `u : (R.obj.obj U)ˣ` clause explicitly equates the inverse tensors computed
  using p'=up and phi'=u⁻¹phi to those using p and phi. Normalization phi'(p')=1
  follows from linearity and the unit inverse identity. Forward formulas apply to
  both pairs, so evaluation is independent of the basis as well.
- The natural isomorphisms `a` and `b` have types T ⋙ S ≅ id and S ⋙ T ≅ id.
  Their equality clauses identify them with `cancellation R P dual e` and
  `cancellation R dual P ((β_ dual P) ≪≫ e)`, respectively. `cancellation` is exactly
  `(tensorRightTensor P Q).symm`, tensoring the last pair with e, and
  `rightUnitorNatIso`. This specifies reassociation, the order of evaluation and the
  symmetry in b. Naturality and both inverse equations are part of the NatIso types.
- The two `∀ M` identities are literally T(a.inv_M) ≫ b_TM = identity and
  a.inv_SM ≫ S(b_M) = identity, with categorical composition in Lean's order.
- The final block states all four local formulas: a((x⊗cp)⊗dphi)=cdx,
  a.inv(x)=(x⊗p)⊗phi, b((x⊗dphi)⊗cp)=cdx, b.inv(x)=(x⊗phi)⊗p.
  The two final unit-change equations assert that both inserted inverse tensors
  are unchanged under simultaneous p↦up and phi↦u⁻¹phi.
- Both functors are Additive, and the natural isomorphisms exhibit them as inverse
  equivalences. The four `PreservesFiniteLimits`/`PreservesFiniteColimits` clauses
  give their exactness. Both `IsFlatOnSite` clauses use the recorded definition,
  i.e. exactness of the existing `siteSheafTensorRight`; no new flatness predicate.
- `scalars R` is the existing ring Γ(R) of compatible global sections. The
  `coefficientLinear` instance is exactly the recorded `homLinear` construction,
  acting sectionwise on morphisms. Both `Functor.Linear (scalars R)` clauses,
  together with Additive, express hom-module linearity. This is equivalent to the
  universal B clause: every sheaf B-algebra structure is a ring homomorphism
  B → Γ(R), restriction of scalars gives its sectionwise B-action, and B=Γ(R)
  itself is allowed. Every component of e, e.inv, a, b and their inverses is already
  a sheaf R-module morphism, hence sectionwise R-linear and therefore B-linear.
  No extra choice of an action or an arbitrary linear-category structure is assumed.

Dependency declarations read and used:

- def-weil-size-convention: its `lean.convention` record is metatheoretic; explicit
  universes and the smallness hypothesis implement it.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  `SheafOfModules.cochainModulesMonoidal`, `cochainModulesSymmetric` and
  `cochainModulesPreadditive`; these retain the existing localization tensor with
  independent site universes.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed:
  `SheafOfModules.tensorClosed` and its publicly imported underlying monoidal API.
  The theorem is not strengthened by assuming a separately chosen closed structure.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom:
  `SheafOfModules.homObj`, through TensorClosed's public import.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite:
  `SheafOfModules.IsFlatOnSite` and `CategoryTheory.exactFunctor`.
- Mathlib.CategoryTheory.Linear.LinearFunctor: `CategoryTheory.Functor.Linear` and
  its imported Functor.Additive. WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule:
  `SheafOfModules.homLinear` gives exactly the sectionwise scalar action.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous:
  `SheafOfModules.over` and its functor/morphism implementation, the recorded
  localized-site interface (public because the statement itself uses restriction).
- Proof-only imports: WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
  (`tensor_bilinear_universal`), Sheaf.Algebra.Category.ModuleCat.Sheaf.HomIsSheaf
  (`homObj_isSheaf_and_sections`),
  Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
  (`exists_localizedSiteTensorRestriction`), and Mathlib.CategoryTheory.Adjunction.Limits
  (the recorded is-equivalence-preserves-limits/colimits results). All recorded
  proof dependencies are thus available; overlaps with statement imports remain public.

Edge cases checked before writing: empty category/site and empty covers on objects
whose ring/module sheaves are zero, the zero ring (1=0), M=0, all ring
characteristics, arbitrary units including 1, arbitrary site morphism universe,
and sections of tensor sheaves which are only locally sums of pure tensors.
There is no assertion that the tensor sheaf is computed sectionwise or that a global
basis exists. In a zero ring the normalized-pair condition still reads 0=1 and the
inverse formulas are the unique zero maps, so that case is not removed.

Searches for existing statements and notions (2026-10-22):

- msearch LeanFinder: "A locally free rank one module sheaf has evaluation
  isomorphism with its internal Hom dual and tensor inverse exact equivalences".
  Eight free/unit-Hom hits, including `SheafOfModules.ιFree_mapFree_inv` and
  `SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply`; no general evaluation pair.
- msearch Loogle: `SheafOfModules.unitHomEquiv`. Six hits; the unit/global-sections
  equivalence supplies no locally free line evaluation and triangle assertion.
- msearch LeanSearch: "Tensoring a locally free rank one sheaf with its dual gives
  inverse exact equivalences". Eight ordinary module/rigid-category hits, including
  `Module.Invertible.rTensorEquiv` and `CategoryTheory.tensorRightHomEquiv`;
  none states the ringed-site result with the required specified maps.
- msearch Mathlib grep `IsInvertible|evaluation|ihom.ev` in
  Algebra/Category/ModuleCat/Sheaf: six evaluation-functor/free-sheaf hits, no match.
- rg in lean/WeilConjectures and lean/Sheaf for locally free/invertible/evaluation
  found the existing LocallyFree, InternalHom, Monoidal, HomModule, finite-projective
  evaluation and LineUnboundedDerivedTensor interfaces. The last is specialized to
  pro-etale schemes and states a derived assertion, not this general-site assertion;
  importing it would reverse the mathematical dependency. No exact existing match.
- rg of the proposed `LineEvaluation` namespace and `evaluation_inverse_pair` in
  Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json: no collisions.
  rg for the item's blueprint id in WeilConjectures: no existing declaration.

Validation: the delivered module compiles cleanly through the prescribed scompile.py
in both sandbox and actual module modes. `set_option autoImplicit false` checks all
variables; all universes are explicit. No diagnostic commands or local instances,
private definitions, local notation, extra axioms, or definition-body sorries remain.
No STATEMENT-DISPUTED issue or source correction was needed.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
