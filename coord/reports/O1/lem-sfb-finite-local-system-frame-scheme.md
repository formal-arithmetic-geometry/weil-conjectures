## Worker report

The module `Sheaf.SixFunctors.FiniteLocalSystemFrameScheme` states
`AlgebraicGeometry.FiniteLocalSystemFrame.exists_frameScheme` with a single `sorry`.
The preceding helpers define the actual free module, constant sheaf, frame type, canonical
inverse-image restriction, evaluation of a universal frame, base-changed universal frame,
forgetting a base-change factor, and the canonical map from a geometric-point frame to a
stalk frame. No helper has postponed data and no additional theorem is postponed.
The node's statement, dependencies and proof are unchanged; only its `lean` record is set.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
|---|---|
| An arbitrary scheme T | `T : Scheme.{u}`; no nonemptiness, connectedness, Noetherian or characteristic hypothesis |
| Prime ell and A=Z/ell | `ell : ℕ`, `hell : Nat.Prime ell`, `Coeff ell = ULift.{u+1} (ZMod ell)` |
| n >= 0, including n=0 | `n : ℕ`, with no positivity binder |
| Small etale site | `T.smallEtaleTopology` on `T.Etale` |
| H a sheaf of constant-A modules | `H : Sheaf T.smallEtaleTopology (ModuleCat.{u+1} (Coeff ell))` |
| Etale-local triviality with the fixed rank n | `hH` quantifies an etale cover and a `Nonempty (Frame ell n H (𝒰.f i))` for each member |
| A^n and its constant module sheaf | `liftedModel` is `ModuleCat.of (Coeff ell) (Fin n → Coeff ell)`; `constant` applies the existing `constantSheaf` |
| Fr_H(U)=Isom(constant A^n, v^-1 H) | `Frame ell n H v` is precisely that isomorphism type, with existing `Etale.upperStar` |
| Restriction by inverse image and canonical comparisons | `restrict` composes the inverse of `constantSheafCompUpperStarIso`, `upperStar.mapIso`, and the inverse of `upperStarComp`, with the over-category triangle supplied by `Over.w` |
| Finite etale surjective representing scheme | Existential `P`, `p`, then `IsFinite p ∧ Etale p ∧ Surjective p` |
| Universal frame lambda_P | Existential `frame : Frame ell n H p` |
| Pullback of lambda gives the bijection on every T-scheme | First conjunct: `Function.Bijective (evaluation ell n H p frame U)` for every `U : Over T`; `evaluation` is exactly `restrict ... a frame` |
| Naturality for all maps of T-schemes | Second conjunct equates evaluation at `w ≫ a` with `restrict w` of evaluation at a |
| Composite restriction comparisons | Third conjunct equates `restrict (w' ≫ w)` and the two restrictions, with arbitrary frames |
| P times_T U with its pulled-back universal frame represents Fr_(v^-1 H) | Fourth conjunct uses precisely `pullback p v`, projection `pullback.snd p v`, and the explicitly constructed `baseFrame`, and requires bijectivity for every `W : Over U` |
| Base-change evaluation is the original universal evaluation | The second half of the fourth conjunct composes with the canonical inverse-image comparison and equates the result with evaluation after `forgetBaseChange` |
| Compatibility with composition of base changes | Fifth conjunct states the same equality for U then V and every W over V. Both iterated evaluations, after the displayed canonical comparisons, equal pullback of the original frame along the composite projection. `forgetBaseChange` twice retains exactly the first projection in the fibre-product associator; this describes its action on every test map, rather than choosing an arbitrary isomorphism |
| Local chart is the disjoint union indexed by GL_n(A) | Sixth conjunct quantifies every etale v with a trivialization and gives an isomorphism over U from `pullback p v` to the coproduct indexed by `model ell n ≅ model ell n`. This is `Aut_A(A^n)`, canonically GL_n(A); no Fintype instance or positive-rank assumption is needed to form the coproduct |
| Geometric fibre is the frames of the stalk | Last conjunct: the actual map from `Over.mk s ⟶ Over.mk p` to `liftedModel ell n ≅ ((pointSmallEtale s).ulift).sheafFiber.obj H` is bijective. `stalkFrame` is the inverse constant-stalk comparison, the stalk of the evaluated frame, and the canonical inverse-image/stalk comparison |
| Empty base and rank zero included | No binder excludes either; the empty cover is allowed, and `Fin 0 → Coeff ell` is the zero module with singleton automorphism set |

The standard universe lift is only a change of presentation of the coefficient ring:
`ULift.ringEquiv` identifies it with `ZMod ell`, coordinatewise on the free module.
Fixed-coefficient module-valued sheaves present modules over the constant ring sheaf:
constant scalar multiplication extends uniquely by sheafification and local gluing to
locally constant scalar sections, while a constant-ring module sheaf restricts its action
to constant scalars. These constructions are inverse, also on linear maps. This is the
project's established etale ModuleCat convention, not a stronger condition on H. Inverse
image is the recorded actual `Etale.upperStar` in this presentation. In particular the
statement has no arbitrary pullback functor, comparison isomorphism or frame-evaluation map
as a hypothesis. `ringedSiteModules` is imported as the recorded general module-sheaf interface.

The fibre's source consists of geometric points with their specified Omega-structure,
namely `Mor_T(Spec Omega,P)`, rather than unstructured topological points of a general
scheme. For a finite etale scheme over the separably closed Omega these coincide with its
geometric fibre. The lifted point fibre has the same stalk as the ordinary point fibre,
via the library's `uliftSheafFiberIso`.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (the actual locally ringed space and morphism structures).
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `Scheme.Etale`,
  `Scheme.smallEtaleTopology`; the covering-family lemma gives joint surjectivity.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`; the established
  fixed-constant-coefficient ModuleCat presentation above is used.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf` (sheafification of the constant presheaf).
- `def-weil-pbc-inverse-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar` and its composition comparison. The additional
  public `ConstantSheaf` module supplies the actual constant comparison and the public
  `Stalk` module supplies the actual stalk comparison.
- `def-weil-pbc-finite-etale-category`: the recorded Mathlib specialization of
  `MorphismProperty.Over` to `IsFinite` and `Etale`; the conclusion writes its object data
  explicitly as P,p and those exact two predicates. This does not introduce a new category.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; the base-frame
  construction uses the actual pullback condition. `Over` supplies actual maps over T.

All proof dependencies with recorded modules are imported with plain `import`, including
the current `GeometricPointCanonicalGerm` binding and the upstream set inverse-image
composition module. Mathlib-only proof dependencies are available through these modules.
The complete eight-step natural-language node proof is copied into the theorem docstring.

Edge cases checked before writing: empty T (all test schemes over it are empty, frame sets
singleton and surjectivity vacuous); n=0 (free module zero, Aut singleton, local coproduct U);
ell=2,n=1 (Aut singleton); disconnected base and nontrivial monodromy (only local, not global,
triviality assumed); char(T)=ell (no invertibility assumption is needed); arbitrary non-etale
v (the upperStar API and the fourth/fifth conjuncts impose no etaleness on base changes).
The only etale binder on a test map occurs in the local chart conjunct, as in the node.

Searches made with `msearch.py` (2026-10-24; exact logs in sandbox searches.jsonl):

- LeanFinder: “The frame functor of a finite locally constant sheaf of finite rank modules
  on a scheme is represented by a finite etale surjective scheme”. Eight hits, all condensed
  locally constant functors or discrete equivalences; none states etale frame representability.
- LeanSearch: “The finite etale scheme of frames of a finite rank locally constant module
  sheaf represents the isomorphisms from a constant free sheaf”. Eight hits, including free
  sheaf pullback, free Hom and constant-sheaf facts; none gives this theorem.
- Loogle: `constantSheaf, Iso`: zero hits, service reports unknown identifier constantSheaf.
- Mathlib grep: `frameScheme|frameSheaf|frame_scheme|finiteLocalSystemFrame`: zero hits.
- Direct project grep over WeilConjectures and Sheaf for the node id and frame names:
  no exact match. `ContinuousFrameSheafComparison` concerns continuous coefficient functions
  and scalar extension, and `PurityFrameClass.frameSheafTensorNext` is a purity tensor map;
  neither represents a finite etale local system's frames. The existing finite-local-system
  Galois equivalence and finite-locally-constant representability are proof inputs, not this
  theorem. Canonical constant pullback and composite/stalk comparisons already exist and
  are reused instead of redefined.

No statement dispute or correction; no new DAG nodes or dependency repair modules.

Validation: `scompile.py O1 lem-sfb-finite-local-system-frame-scheme` compiles the sandbox
and the final module separately against the published live build, with no errors or
non-sorry warnings. The file uses module mode, explicit universes, `autoImplicit false`,
public statement imports, real helper definitions, and only the main theorem has `sorry`.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
