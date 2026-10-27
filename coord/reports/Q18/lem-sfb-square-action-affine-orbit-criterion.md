## Worker report

This delivery states `AlgebraicGeometry.Scheme.Modules.squareAction_affine_orbit_criterion`
in `Sheaf.AlgebraicGeometry.SquareActionAffineOrbitCriterion`. Its only theorem proof
is `sorry`; there are no new definitions. The original statement, dependency lists,
and proof plan are unchanged. Only the item's `lean` field is set.

The source was read online: Ning Guo, *Divisors on coherent schemes and homogeneous
spaces*, March 31, 2026 version, section 5.6, section 6.1, Proposition 6.2(iii),
Lemma 6.3(ii), and Corollary 6.5 (PDF page 17):
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf . The item specializes
its sufficient direction to affine section loci and smooth separated groups.
The source's relative ampleness becomes absolute ampleness over an affine base.
No normality or homogeneity is required. No statement fault was found.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Affine base: `(S : Scheme.{u}) [IsAffine S]`.
- The S-group scheme: `(H : Over S) [GrpObj H]`. Group-object multiplication,
  inverse and unit are morphisms over S, with associativity, identity, and inverse
  identities supplied by `GrpObj` and its parent `MonObj` in the cartesian
  category `Over S`. This does not assume commutativity.
- Smooth separated finite presentation: `[Smooth H.hom] [IsSeparated H.hom]`
  `[LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom]`.
  Quasi-separatedness is an existing consequence of separatedness, completing
  finite presentation without adding a separate redundant hypothesis.
- Connected fibres: `hconnected : ∀ s : S, ConnectedSpace (H.hom.fiber s)`.
  `Scheme.Hom.fiber` is literally the fibre product along `S.fromSpecResidueField s`.
  `ConnectedSpace` includes nonemptiness, exactly as the recorded node requires.
- The separated finitely presented S-scheme is `(X : Over S)` with
  `[IsSeparated X.hom] [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom]`.
  Again separatedness supplies quasi-separatedness.
- Action: `[ModObj H X]`. Its morphism `γ[H, X] : H ⊗ X ⟶ X` is over S;
  its unit and multiplication axioms are the two action morphism identities.
- Invertible module: `(M : X.left.Modules) [M.IsInvertible]`, using the project's
  scheme-module invertibility, not an alternative sheaf-module predicate.
- Every S-test scheme and pair of points: `∀ (B : Over S) (g h : B ⟶ H)`.
  The products `X ⊗ B` are Mathlib's chosen scheme pullbacks. The projections
  are `fst X B` to X and `snd X B` to B. Test schemes have the same general
  universe as S, H, and X; no independent smaller test universe is introduced.
- Base-changed module: `(tensorPullback (fst X B).left).obj M`.
  The map `((snd X B ≫ g) • fst X B).left` sends `(x,b)` to `g(b)x`.
  Thus its tensor pullback of M is canonically `τ_g^*M_B`, by the actual
  tensor-pullback composition comparison. This avoids introducing any arbitrary
  translation morphism. The product of points `g * h` is the group law induced
  by the multiplication of the group object.
- Square identity: `hsquare` quantifies `∃ N : B.left.Modules, N.IsInvertible ∧`
  `Nonempty (...)`. The source of its isomorphism is the pullback for `g*h`
  tensored with M_B; the target is the pullback for g tensored with that for h,
  then tensored with `(tensorPullback (snd X B).left).obj N`. All tensors are
  the established sheaf tensor. Existential `Nonempty` imposes no chosen
  isomorphisms, functorial choices of N, or coherence. It expresses exactly
  equality of translation differences modulo base pullbacks.
- The specified union is `(U : X.left.Opens)` with `hU` giving, for every x,
  membership precisely when there are `n : ℕ`, `0 < n`, a global section s of
  `M.tensorPow n`, and an affine open V whose underlying set is precisely
  `nonvanishingLocus (M.tensorPow n) s`, containing x. This includes every affine
  section locus and excludes nonaffine section loci. The invertible-module
  nonvanishing locus is open, so representing the union by an open is harmless.
  Neither a finite family nor a single exponent is chosen.
- Saturation: `horbit` states that the image under `γ[H, X].left.base` of the
  inverse image of U under `(snd H X).left.base` equals `Set.univ`. This
  inverse image is the underlying open of `H ×_S U`. All scheme points are
  used, not merely rational points over a fixed field.
- Conclusion: `IsAmple X.left M`, exactly the existing absolute definition,
  including quasi-compactness and affine nonvanishing neighborhoods in positive
  powers. No relative-ampleness predicate or weakened local conclusion is used.
- The negative final clauses are respected: there is no normality, noetherianity,
  homogeneous-space, transitivity, or commutativity assumption.

Dependency declarations read and used (modules are public imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (the dependency's
  `mathlib_match`, requiring no extra `lean` record).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; `Over`'s cartesian tensor
  is the chosen pullback, as its `tensorObj_left`, `fst_left`, `snd_left` show.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, and `tensorPow`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: publicly exports
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, the actual tensor-formula
  pullback, and its normalized composition comparison `tensorPullbackSectionComp`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  sheaf tensor interface, reusing the established localization tensor.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus` and `.IsAmple`.

Additional framework: `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, `.Mod`,
and `.Over` supply group objects, action on functorial points, the cartesian
structure on `Over S`, and projections. `IsSeparated` is Mathlib's closed-diagonal
predicate. No duplicate notion was created.

All stated proof-dependency modules are plain imports, including
`SquareActionGenerationLocusStable`, `AmpleProjCanonicalMap`,
`SquareActionProjImmersionLocusStable`, and `SectionRingLocalizationBijective`.
The mathematical Mathlib leaves for separation, quasi-separatedness, Proj, and
reflection of an isomorphism on affine global sections are also imported. Their
signatures/docstrings were read. The theorem docstring contains all five steps
of the node's proof, with the named DAG inputs. There are no omitted proof imports.

Edge cases checked before writing:

- Empty X: U and the action domain are empty; saturation and absolute ampleness
  have their usual vacuous point clauses, with quasi-compactness valid.
- Empty S: the over-schemes are empty; fibre connectedness is vacuous, not an
  unintended requirement that S be nonempty.
- Degree zero: excluded by `0 < n`; the tensor unit is never used as a false
  positive-degree section in defining U. Empty section loci are allowed.
- If there are no nonempty affine section loci, U is empty and saturation
  forces X empty. No ampleness for a nonempty such X is asserted.
- Trivial group action: saturation reduces to U = X, recovering the existing
  absolute section-locus criterion. No connectedness of X is imposed.
- Trivial line bundle: the square identity is harmless, but the orbit condition
  still supplies the geometric content. There is no automatic ampleness claim.
- P¹×P¹ with the line O(1,0) over a field has no nonempty affine section loci;
  its section loci contain a complete P¹ factor. The criterion therefore does
  not falsely assert ampleness there.
- Arbitrary characteristics and nonnormal affine bases remain allowed. Finite
  presentation, separatedness, and all-point saturation agree with the node.

Searches for an existing statement (2026-10-24):

1. `msearch.py ... leanfinder "A line bundle satisfying the theorem of the square
   is ample if group translates of its affine section loci cover"`: eight hits,
   including Proj affine covers, `of_affine_open_cover`, and
   `exists_eq_pow_mul_of_isAffineOpen`. None is an ampleness criterion for a
   square-condition invertible module with a scheme-group action.
2. `msearch.py ... loogle '"IsAmple", "IsAffineOpen"'`: zero hits.
3. `msearch.py ... grep
   "Picard.admiss|theorem.of.the.square|squareAction|square_action|IsAmple"
   AlgebraicGeometry`: zero Mathlib hits.
4. `msearch.py ... leansearch "An invertible sheaf satisfying the theorem of the
   square is ample when translates of affine nonvanishing section opens cover
   the scheme"`: eight hits on affine covers, affineness of structure-sheaf
   basic opens and elementary scheme covers; none states this theorem.
5. Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib for
   `squareAction_affine_orbit_criterion|square.action.*ample|square.*orbit.*criterion`
   found no declaration of the item. Broader square-action searches in the
   project found the two current stability inputs, which are reused as proof
   dependencies; the upstream search for the item's exact DAG id had no hit.
   No existing declaration says the criterion, and no notion is defined twice.

Validation: every compile uses the prescribed `scompile.py` and the 60-second
per-file server limit. The final validation results are recorded below.

## Second reading by Q18

A separate pass reopened the node and the finished module, and checked every
binder against the correspondence above. This is a worker self-check; no other
agent was started, as the dispatcher explicitly forbids it. The maintainer's
independent delivery review is still required. In particular this pass checked
that g*h uses the stated order, N lives on B, the last factor is pulled back
along q_B, both sides are in `(X ×_S B).Modules`, only existence of an
isomorphism is required, the positive-power sections are global on X, U includes
exactly the affine section opens, and the saturation is on all product points.
The separatedness instances supply both quasi-separatedness conditions; neither
finite presentation nor quasi-compactness was accidentally dropped. The
conclusion is the original absolute `IsAmple`. No mismatch or statement change
was found. No helpers, new nodes, or dependency-module repairs are needed.

Final validation: the standalone `scompile.py` invocation passed for the delivered
module in both sandbox and library modes, with no compiler errors or unexpected
warnings. `deliver2.py Q18 lem-sfb-square-action-affine-orbit-criterion --no-push`
printed `OK (dry run): commit 124feaedb27 passes the preflight and compiles; nothing
pushed`. Its staged set contained only this report, the item's node JSON, and the
single statement module. No repository files were edited directly and no direct
Git command or global build was run.
