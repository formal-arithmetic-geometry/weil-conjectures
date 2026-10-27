## Worker report

The module `Sheaf.AlgebraicGeometry.StackQcqsMorphism` defines the predicates of
`def-sfb-stack-qcqs-morphism`. It contains five real Prop-valued definitions,
no theorems and no `sorry`. The node statement is unchanged. There is no repair
note for this item. No new nodes or dependency repairs are needed.

Source read: stacks-morphisms.tex, definition-quasi-compact (050U), and
 definition-separated (04YW), clause (4); stacks-properties.tex,
lemma-quasi-compact-stack (04YC), clause (3); spaces-properties.tex,
definition-quasi-compact (03E3); spaces-morphisms.tex,
definition-quasi-compact (03HE), definition-separated (03HL), clause (3),
and the preceding representable characterization. The latest blueprint unit
sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md was read; the supporting
moduli definition changes none of its six-functor statements or route.

Clause-by-clause correspondence:

- Base scheme and size: every definition binds `S : Scheme.{u}` explicitly.
  Endpoints are `BasedCategory.{v₁,w₁}` and `BasedCategory.{v₂,w₂}` over `Over S`.
  All universes and variables are explicit, with `autoImplicit false`.
- Categories fibred in groupoids, morphisms and 2-fibre products: use the recorded
  `BasedCategory`, `BasedFunctor`, `IsAlgebraicModuliStack`, and
  `moduliTwoFiberProduct`. The predicates are meaningful extensions to based
  categories; applying them to the CFGs/algebraic stacks in the statement adds no
  hypothesis. No truncation to isomorphism classes is made.
- Quasi-compact fibred groupoid: `IsQuasiCompactModuli F` is the existential
  `U`, `a : BasedFunctor (discreteModuli (yoneda.obj U)) F`,
  `CompactSpace U.left ∧ IsSmoothModuliAtlas F U a`. The existing smooth-atlas
  predicate tests every scheme base change with its specified space projection,
  smoothness and surjectivity. This is exactly the node's atlas convention, and
  applies equally to the recorded 2-fibre products.
- Quasi-compact stack morphism: `IsQuasiCompactAlgebraicModuliMap f` quantifies
  over `Z` and `g : BasedFunctor Z G`, assumes `IsAlgebraicModuliStack Z` and
  `IsQuasiCompactModuli Z`, and requires
  `IsQuasiCompactModuli (moduliTwoFiberProduct f g)`. Its test object and morphism
  universes include the base-site and endpoint bounds and can be increased by
  `w₃`, `v₃`; there is no independent smaller test-scheme universe or imposed
  equality of endpoint universes.
- Algebraic spaces as discrete groupoids: use the existing `discreteModuli A.obj.obj`
  and `discreteModuliMap`. The generic morphism predicates also accept these
  discrete endpoints, without adding a DM assumption.
- Quasi-compact fppf sheaf: `AlgebraicSpace.IsQuasiCompact A` binds a scheme
  `U`, a presheaf map `a : yoneda.obj U ⟶ A.obj`, and the conjunction
  `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`. Both map predicates
  include representability and test all schemes, as in the dependency.
- Quasi-compact algebraic-space morphism: reuse
  `AlgebraicSpace.MapIsQuasiCompact`. Its definition tests `CompactSpace
  (Point (pullback f a))` over every affine scheme map. For algebraic spaces this
  is the same property as testing every quasi-compact algebraic space in 03HE:
  03E3 identifies compact point space with existence of a quasi-compact étale
  atlas; finite affine refinement gives every quasi-compact scheme test; a
  quasi-compact étale atlas of the test space then gives the space test. The
  converse specializes to affine test schemes. No representability or separation
  of the morphism is assumed. A second definition of this existing notion would
  violate the one-definition rule, so the existing predicate is used directly.
- Quasi-separated algebraic-space morphism: `MapIsQuasiSeparated g` is exactly
  `MapIsQuasiCompact (pullback.diagonal g)`. It is defined for presheaf maps so
  that the sheaf pullback need not be re-bundled using a closure theorem.
- Relative stack diagonal: import and use `moduliRelativeDiagonal f`. Its
  object function is `(x,x,identity (f x))`, and its arrow function is `(a,a)`.
  Its full signature and implementation were read; no duplicate is introduced.
- Quasi-separated stack morphism: for every `T` and
  `t : BasedFunctor (discreteModuli (yoneda.obj T)) (moduliTwoFiberProduct f f)`,
  `IsQuasiSeparatedAlgebraicModuliMap` requires an algebraic space `Z` and
  `p : Z.obj.obj ⟶ yoneda.obj T`, with
  `HasSpaceBaseChange (moduliRelativeDiagonal f) T t Z p`,
  `MapIsQuasiCompact p`, and `MapIsQuasiSeparated p`.
  `HasSpaceBaseChange` supplies the equivalence from the discrete space to
  `T ×_(F ×_G F) F`, together with the 2-isomorphism comparing its projection
  to `discreteModuliMap p`. Thus representability is part of the predicate,
  and qcqs is tested on the actual projection, not an unrelated map.
- No finite-type, Deligne--Mumford, separated-base, nonempty-base or chosen-atlas
  data appears. Every atlas and presentation is existential in Prop.

Dependencies used (full signatures and relevant docstrings/implementations read):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.Topology.Defs.Filter: `CompactSpace`, with no Hausdorff assumption.
- The size-convention node is metatheoretic and has no declaration; explicit
  universe binders implement it.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, and the underlying fppf sheaves and presheaves.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `IsFibredInGroupoids`,
  `discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct`,
  `HasSpaceBaseChange`; the latter includes projection compatibility over T.
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth` (and its existing surjectivity test).
- Sheaf.AlgebraicGeometry.DmStackMorphismProperties: `moduliRelativeDiagonal`.
- Sheaf.AlgebraicGeometry.ProperCurveModuli: `AlgebraicSpace.MapIsQuasiCompact`.
  The last two owning nodes were added to stmt_deps under the landed-node rule.
  They already have usable records; neither node nor its module is changed.

The existing DM-specific `IsQuasiCompactModuliMap` uses an étale atlas over
an affine scheme and does not supply the smooth-atlas definition on arbitrary
algebraic stacks here. It is deliberately not duplicated or rebound. The
existing `IsQuasiCompactPresheafMap` in SpaceQCSeparatedEtaleLocal.lean is a
relative affine-test condition, not the absolute fppf-sheaf atlas condition.
The absolute space quasi-separatedness predicate also differs from the relative
predicate when the base scheme is not quasi-separated.

Edge cases checked against the expanded definitions: empty scheme and empty
atlas are permitted (compactness has no nonempty assumption); identities have
canonical diagonal and scheme-base-change projection; a stack with positive
stabilizers is not excluded by the smooth-atlas clause, which is not replaced
by an étale atlas; non-quasi-compact stacks need not have the existential atlas;
nonrepresentable relative diagonals fail the existential presentation clause.
A non-quasi-separated base S causes no absolute-diagonal substitution: the
presheaf diagonal is always relative to the actual morphism p. No assertion is
made that arbitrary functors have representable diagonals. Universes allow
arbitrary enlargement and retain the object's larger site universe.

Searches actually run:

- msearch.py leanfinder: "A morphism of algebraic stacks is quasi compact if every
  base change by a quasi compact algebraic stack is quasi compact and quasi
  separated if its diagonal is quasi compact and quasi separated". Eight hits;
  only Scheme quasi-compact/quasi-separated predicates and permanence instances.
- msearch.py loogle: "AlgebraicGeometry.QuasiCompact,
  AlgebraicGeometry.QuasiSeparated". Twelve hits, all scheme-related. Read
  Mathlib Morphisms/QuasiCompact.lean:35–46 and QuasiSeparated.lean:43–55;
  their endpoints are Scheme, not algebraic stacks.
- msearch.py grep: "AlgebraicStack|Moduli.*QuasiCompact|Moduli.*QuasiSeparated"
  in Mathlib/AlgebraicGeometry: zero hits.
- rg over lean/WeilConjectures and lean/Sheaf by item id and the same key names;
  found no exact stack predicates. Additional broad searches for quasi-compactness
  and definitions in Sheaf found MapIsQuasiCompact, the DM-specific map predicate,
  the relative atlas affine-test predicate, and the absolute QS predicate; each
  was opened and checked. The canonical relative diagonal is reused.
- rg of dag/lean_names_upstream.json for the proposed names found no clash.

Validation: scompile.py compiled the sandbox and final library-mode module
cleanly against the live published build (10.8 seconds and 10.2 seconds).
No STATEMENT-DISPUTED flag, no statement correction and no hollow definition.

## Second reading by Q59

Re-read the item and the complete module after the clean compile. Each of the
node's atlas existential, algebraic-stack base-change universal, fppf-sheaf
atlas condition, algebraic-space relative diagonal, explicit stack diagonal
and scheme-base-change qcqs clauses is matched above with its actual Lean
expression. Found existing reusable notions during the reading: the canonical
relative diagonal and MapIsQuasiCompact. Reused both and added their already
landed owning nodes to stmt_deps. The DM étale-atlas condition was checked and
not substituted for general smooth-atlas compactness. The projection comparison
in HasSpaceBaseChange was read, so the QS clause retains the required map to T.
No mathematical statement was changed. All five definitions have real data,
source/blueprint docstrings, explicit variables and no auxiliary theorem.
